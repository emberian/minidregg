// Read-only policy probe: a pinned but disallowed op must stop at the frontend.
use std::env;
use std::fs;
use std::io::{Read, Write};
use std::os::unix::net::UnixStream;
use std::time::{Duration, Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 4 && args.len() != 5 {
        return Err("usage: host-frontend-probe SOCKET CONFIG HOST_SHA256 [--slow-prefix]".into());
    }
    let config = fs::read(&args[2])?;
    if config.is_empty() || config.len() > 65_536 || args[3].len() != 64 {
        return Err("invalid config or SHA-256 length".into());
    }
    let mut host_hash = [0u8; 32];
    for (index, byte) in host_hash.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&args[3][index * 2..index * 2 + 2], 16)?;
    }
    let mut envelope = vec![2];
    envelope.extend_from_slice(&(config.len() as u32).to_le_bytes());
    envelope.extend_from_slice(&config);
    envelope.extend_from_slice(&host_hash);
    envelope.push(255); // frontend must refuse before contacting private Mini
    let mut stream = UnixStream::connect(&args[1])?;
    stream.set_read_timeout(Some(Duration::from_secs(15)))?;
    if args.get(4).is_some_and(|mode| mode == "--slow-prefix") {
        let started = Instant::now();
        stream.write_all(&[1])?;
        let mut byte = [0u8; 1];
        if stream.read(&mut byte)? != 0 || started.elapsed() > Duration::from_secs(12) {
            return Err("partial frame was not closed by the whole-frame deadline".into());
        }
        println!(
            "partial frame closed after {} ms",
            started.elapsed().as_millis()
        );
        return Ok(());
    }
    if args.len() == 5 {
        return Err("unknown probe mode".into());
    }
    stream.write_all(&(envelope.len() as u32).to_le_bytes())?;
    stream.write_all(&envelope)?;
    let mut prefix = [0u8; 4];
    stream.read_exact(&mut prefix)?;
    let len = u32::from_le_bytes(prefix) as usize;
    if len == 0 || len > 4096 {
        return Err("unexpected refusal frame length".into());
    }
    let mut reply = vec![0u8; len];
    stream.read_exact(&mut reply)?;
    if reply[0] != 254
        || !reply[1..].starts_with(b"frontend requires exact pinned v2 Mini envelope")
    {
        return Err(format!("frontend returned different bounded status: {:?}", reply).into());
    }
    println!("frontend policy refusal for peer UID {}", unsafe {
        geteuid()
    });
    Ok(())
}

unsafe extern "C" {
    fn geteuid() -> u32;
}
