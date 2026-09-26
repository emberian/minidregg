// Test-only MCP delivery fault: submit one broker request, then refuse its reply.
// The controller and native Mini still execute the queued request. This helper
// has no custody key, journal access, or ability to forge a Mini receipt.
use std::env;
use std::fs;
use std::io::{self, Write};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::Duration;

fn main() -> io::Result<()> {
    let args: Vec<_> = env::args_os().collect();
    if args.len() != 3 {
        eprintln!("usage: broker-drop ABSOLUTE_BROKER_SOCKET REQUEST_JSON_FILE");
        std::process::exit(2);
    }
    let socket = Path::new(&args[1]);
    if !socket.is_absolute() {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "socket must be absolute"));
    }
    let request = fs::read(&args[2])?;
    if request.is_empty() || request.len() > 65_535 || request.contains(&b'\n') {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "request must be one bounded JSON line"));
    }
    // The driver validates the exact JSON/name with jq before invoking this
    // byte-only helper. Keeping it std-only makes the fault binary trivial to
    // build in an isolated test directory.
    let mut stream = UnixStream::connect(socket)?;
    stream.set_write_timeout(Some(Duration::from_secs(5)))?;
    stream.write_all(&request)?;
    stream.write_all(b"\n")?;
    stream.flush()?;
    // The server's later write has no client reader. A confirmed native call
    // must therefore be recovered from its exact retained receipt, not from
    // an ACP/MCP success response.
    stream.shutdown(std::net::Shutdown::Read)?;
    Ok(())
}
