//! Probe one real native host stdio process across an externally published image.
//! The shell driver supplies two already valid images and owns the CAS evidence.
use std::env;
use std::io::{self, Read, Write};
use std::process::{Command, ExitCode, Stdio};

struct HostGuard(std::process::Child);
impl Drop for HostGuard {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn frame(host: &mut std::process::Child) -> io::Result<Option<Vec<u8>>> {
    let input = host.stdin.as_mut().expect("host stdin");
    input.write_all(&1u32.to_le_bytes())?;
    input.write_all(&[0])?; // describe refreshes the verified image.
    input.flush()?;
    let output = host.stdout.as_mut().expect("host stdout");
    let mut length = [0u8; 4];
    match output.read_exact(&mut length) {
        Ok(()) => {}
        Err(error) if matches!(error.kind(), io::ErrorKind::UnexpectedEof | io::ErrorKind::BrokenPipe) => {
            return Ok(None)
        }
        Err(error) => return Err(error),
    }
    let count = u32::from_le_bytes(length) as usize;
    if !(1..=1_048_576).contains(&count) {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "invalid host reply length"));
    }
    let mut bytes = vec![0; count];
    output.read_exact(&mut bytes)?;
    Ok(Some(bytes))
}

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args_os().collect();
    if args.len() != 7 {
        return Err("usage: replay-poison HOST CONFIG STORE ROOT EXPECTED-IMAGE REPLACEMENT-IMAGE".into());
    }
    let child = Command::new(&args[1])
        .arg(&args[2]).arg("stdio")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit())
        .spawn().map_err(|e| format!("launch host: {e}"))?;
    let mut host = HostGuard(child);
    let first = frame(&mut host.0).map_err(|e| format!("initial describe: {e}"))?
        .ok_or("host ended before initial describe")?;
    if first.first() != Some(&0) {
        return Err(format!("initial describe returned operation {:?}", first.first()));
    }
    println!("initial describe accepted: {} reply bytes", first.len());
    let cas = Command::new(&args[3]).arg("cas").arg(&args[4]).arg(&args[5]).arg(&args[6])
        .output().map_err(|e| format!("CAS launch: {e}"))?;
    print!("CAS stdout: {}", String::from_utf8_lossy(&cas.stdout));
    eprint!("CAS stderr: {}", String::from_utf8_lossy(&cas.stderr));
    if !cas.status.success() || !String::from_utf8_lossy(&cas.stdout).contains("Installed") {
        return Err(format!("CAS did not publish replacement: {}", cas.status));
    }
    match frame(&mut host.0) {
        Ok(None) => println!("first frame after replacement: host closed without acceptance"),
        Ok(Some(bytes)) => return Err(format!("host accepted replacement: {} reply bytes, opcode {:?}", bytes.len(), bytes.first())),
        Err(error) if matches!(error.kind(), io::ErrorKind::BrokenPipe | io::ErrorKind::UnexpectedEof) => {
            println!("first frame after replacement: connection closed: {error}")
        }
        Err(error) => return Err(format!("first replacement frame: {error}")),
    }
    match frame(&mut host.0) {
        Ok(None) => println!("next frame remains closed"),
        Ok(Some(bytes)) => return Err(format!("poison failed: later frame accepted, opcode {:?}", bytes.first())),
        Err(error) if matches!(error.kind(), io::ErrorKind::BrokenPipe | io::ErrorKind::UnexpectedEof) => {
            println!("next frame remains closed: {error}")
        }
        Err(error) => return Err(format!("later frame: {error}")),
    }
    let exit = host.0.wait().map_err(|e| format!("host wait: {e}"))?;
    if exit.success() { return Err("host exited successfully after invalidated session".into()); }
    println!("PASS persistent host poisoned; exit {exit}");
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => { eprintln!("FAIL replay-poison: {error}"); ExitCode::FAILURE }
    }
}
