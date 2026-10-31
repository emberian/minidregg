//! Standard output and error when the reader has gone.
//!
//! The std `print!` family panics when a write fails, and the Rust runtime ignores SIGPIPE, so a
//! reader that closed its end early (`mini --help | grep -q ...`, `doc show NAME | head`) made
//! `mini` die with a panic and exit 101. Restoring SIGPIPE would instead kill the process on any
//! closed socket or child pipe it writes, and kill a resident (`line-resident`,
//! `command-resident`) serving many commands on behalf of one caller who left.
//!
//! So every `print!`/`println!` in this crate is these macros (declared before every module, they
//! shadow std's by textual scope), and the commands' own stdout writers are [`out`]. A write to a
//! closed standard output unwinds with [`StdoutClosed`], which no panic hook reports. `main` ends
//! the process with [`CLOSED`] (128 + SIGPIPE, the status a shell shows for a reader that left);
//! a resident ends only that command, with the same status, and keeps serving. A write to a
//! closed standard error is dropped: there is nobody left to tell.
use std::io::{self, Write};

/// What a write to a closed standard output unwinds with.
pub(crate) struct StdoutClosed;

/// The exit status of a command whose standard output was closed under it: 128 + SIGPIPE.
pub(crate) const CLOSED: u8 = 141;

fn closed(error: io::Error) -> ! {
    if error.kind() == io::ErrorKind::BrokenPipe {
        std::panic::resume_unwind(Box::new(StdoutClosed));
    }
    panic!("failed printing to stdout: {error}");
}

#[doc(hidden)]
pub(crate) fn print_out(args: std::fmt::Arguments<'_>) {
    if let Err(error) = io::stdout().lock().write_fmt(args) {
        closed(error);
    }
}

#[doc(hidden)]
pub(crate) fn print_err(args: std::fmt::Arguments<'_>) {
    let _ = io::stderr().lock().write_fmt(args);
}

/// Standard output for a command's own writes: a closed reader ends the command as `print!` does.
pub(crate) fn out() -> Out {
    Out(io::stdout())
}

pub(crate) struct Out(io::Stdout);

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
pub(crate) fn is_closed(payload: &(dyn std::any::Any + Send)) -> bool {
    payload.is::<StdoutClosed>()
}

macro_rules! print {
    ($($arg:tt)*) => { $crate::streams::print_out(format_args!($($arg)*)) };
}

macro_rules! println {
    () => { $crate::streams::print_out(format_args!("\n")) };
    ($($arg:tt)*) => { $crate::streams::print_out(format_args!("{}\n", format_args!($($arg)*))) };
}

macro_rules! eprint {
    ($($arg:tt)*) => { $crate::streams::print_err(format_args!($($arg)*)) };
}

macro_rules! eprintln {
    () => { $crate::streams::print_err(format_args!("\n")) };
    ($($arg:tt)*) => { $crate::streams::print_err(format_args!("{}\n", format_args!($($arg)*))) };
}
