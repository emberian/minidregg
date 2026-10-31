//! Standard output and error when the reader has gone, for every client binary.
//!
//! std's `print!` family panics when a write fails, and the Rust runtime ignores SIGPIPE, so a
//! reader that closed its end early (`mini --help | grep -q ...`, `doc show NAME | head`) made a
//! client die with a panic and exit 101. Restoring SIGPIPE instead would kill the process on any
//! closed socket or child pipe it writes, and kill a resident (`mini line-resident`,
//! `mini command-resident`) that runs many commands for callers who may leave.
//!
//! A crate root says `#[macro_use] extern crate mini_streams;`: these `print!`, `println!`,
//! `eprint!` and `eprintln!` then shadow std's (the `macro_use` prelude comes before the standard
//! library's) in every module of that crate. A write to a closed standard output unwinds with
//! [`StdoutClosed`], which no panic hook reports; [`guard`] around `main` ends the process with
//! [`CLOSED`] (128 + SIGPIPE, the status a shell shows for a reader that left), and a resident
//! that catches the unwind ([`is_closed`]) ends only that command. A write to a closed standard
//! error is dropped: there is nobody left to tell. [`out`] is the same standard output for a
//! command's own `Write` calls.
use std::io::{self, Write};
use std::process::ExitCode;

/// What a write to a closed standard output unwinds with.
pub struct StdoutClosed;

/// The exit status of a command whose standard output was closed under it: 128 + SIGPIPE.
pub const CLOSED: u8 = 141;

fn closed(error: io::Error) -> ! {
    if error.kind() == io::ErrorKind::BrokenPipe {
        std::panic::resume_unwind(Box::new(StdoutClosed));
    }
    panic!("failed printing to stdout: {error}");
}

#[doc(hidden)]
pub fn print_out(args: std::fmt::Arguments<'_>) {
    if let Err(error) = io::stdout().lock().write_fmt(args) {
        closed(error);
    }
}

#[doc(hidden)]
pub fn print_err(args: std::fmt::Arguments<'_>) {
    let _ = io::stderr().lock().write_fmt(args);
}

/// Standard output for a command's own writes: a closed reader ends the command as `print!` does.
pub fn out() -> Out {
    Out(io::stdout())
}

pub struct Out(io::Stdout);

impl Write for Out {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        match self.0.write(bytes) {
            Ok(written) => Ok(written),
            Err(error) => closed(error),
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        match self.0.flush() {
            Ok(()) => Ok(()),
            Err(error) => closed(error),
        }
    }
}

/// Whether a caught unwind is a closed standard output rather than a panic.
pub fn is_closed(payload: &(dyn std::any::Any + Send)) -> bool {
    payload.is::<StdoutClosed>()
}

/// Run a binary's `main`: a closed standard output ends the process with [`CLOSED`], quietly;
/// any other panic unwinds as before.
pub fn guard(main: impl FnOnce() -> ExitCode) -> ExitCode {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(main)) {
        Ok(code) => code,
        Err(payload) if is_closed(&*payload) => ExitCode::from(CLOSED),
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => { $crate::print_out(::std::format_args!($($arg)*)) };
}

#[macro_export]
macro_rules! println {
    () => { $crate::print_out(::std::format_args!("\n")) };
    ($($arg:tt)*) => { $crate::print_out(::std::format_args!("{}\n", ::std::format_args!($($arg)*))) };
}

#[macro_export]
macro_rules! eprint {
    ($($arg:tt)*) => { $crate::print_err(::std::format_args!($($arg)*)) };
}

#[macro_export]
macro_rules! eprintln {
    () => { $crate::print_err(::std::format_args!("\n")) };
    ($($arg:tt)*) => { $crate::print_err(::std::format_args!("{}\n", ::std::format_args!($($arg)*))) };
}

#[cfg(test)]
mod tests {
    #[test]
    fn a_closed_stdout_unwinds_with_the_marker_and_guard_ends_with_141() {
        let mut ends = [0i32; 2];
        // SAFETY: pipe(2) into a two-element array; dup/dup2 on this process's descriptors.
        assert_eq!(unsafe { libc_pipe(ends.as_mut_ptr()) }, 0);
        unsafe { libc_close(ends[0]) };
        let saved = unsafe { libc_dup(1) };
        assert_eq!(unsafe { libc_dup2(ends[1], 1) }, 1);
        let code = super::guard(|| {
            crate::println!("to nobody");
            std::process::ExitCode::SUCCESS
        });
        unsafe { libc_dup2(saved, 1) };
        unsafe { libc_close(saved) };
        unsafe { libc_close(ends[1]) };
        assert_eq!(format!("{code:?}"), format!("{:?}", std::process::ExitCode::from(super::CLOSED)));
    }

    extern "C" {
        #[link_name = "pipe"]
        fn libc_pipe(fds: *mut i32) -> i32;
        #[link_name = "close"]
        fn libc_close(fd: i32) -> i32;
        #[link_name = "dup"]
        fn libc_dup(fd: i32) -> i32;
        #[link_name = "dup2"]
        fn libc_dup2(from: i32, to: i32) -> i32;
    }
}
