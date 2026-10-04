//! One length-prefixed frame each way per step: a little-endian `u32` length,
//! then that many bytes. Every frame the broker's own protocol uses is one JSON
//! object; the member exchange relays the ssh key-service frames verbatim
//! (the same prefix, bounded by [`MEMBER_FRAME`]).
//!
//! A response is `{"ok":true, ...}` or a named refusal
//! `{"refused":"CODE","detail":"TEXT"}`.
use serde_json::Value;
use std::io::{Read, Write};
use std::os::unix::net::UnixStream;
use std::time::Instant;

/// The largest frame either side sends: a provider response body (at most
/// [`MAX_PROVIDER_RESPONSE`] bytes) travels hex-encoded inside one.
pub const MAX_FRAME: usize = 4 << 20;
/// The ssh key-service exchange's bound, which the remote `mini key` client
/// enforces on every frame it reads; member frames stay inside it.
pub const MEMBER_FRAME: usize = 32_768;
/// The largest provider response body the broker returns.
pub const MAX_PROVIDER_RESPONSE: usize = 1 << 20;
/// The largest provider request body the broker forwards.
pub const MAX_PROVIDER_REQUEST: usize = 1 << 20;

pub fn zero(bytes: &mut [u8]) {
    for b in bytes.iter_mut() {
        // SAFETY: a valid, aligned, exclusive byte reference.
        unsafe { std::ptr::write_volatile(b, 0) };
    }
}

fn deadline(stream: &UnixStream, end: Instant) -> Result<(), String> {
    let left = end.saturating_duration_since(Instant::now());
    if left.is_zero() {
        return Err("mini-keys exchange timed out".into());
    }
    stream
        .set_read_timeout(Some(left))
        .and_then(|_| stream.set_write_timeout(Some(left)))
        .map_err(|_| "mini-keys socket unavailable".into())
}

fn io(what: &str, error: &std::io::Error) -> String {
    match error.kind() {
        std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut => {
            "mini-keys exchange timed out".into()
        }
        _ => format!("mini-keys {what} failed"),
    }
}

/// Write one frame before `end`.
pub fn write_frame(stream: &mut UnixStream, bytes: &[u8], end: Instant) -> Result<(), String> {
    if bytes.is_empty() || bytes.len() > MAX_FRAME {
        return Err("mini-keys frame exceeds bound".into());
    }
    let mut frame = Vec::with_capacity(4 + bytes.len());
    frame.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
    frame.extend_from_slice(bytes);
    let result = (|| {
        let mut rest = frame.as_slice();
        while !rest.is_empty() {
            deadline(stream, end)?;
            match stream.write(rest) {
                Ok(0) => return Err("mini-keys peer closed".into()),
                Ok(n) => rest = &rest[n..],
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => return Err(io("write", &e)),
            }
        }
        Ok(())
    })();
    zero(&mut frame);
    result
}

fn read_exact(stream: &mut UnixStream, mut bytes: &mut [u8], end: Instant) -> Result<(), String> {
    while !bytes.is_empty() {
        deadline(stream, end)?;
        match stream.read(bytes) {
            Ok(0) => return Err("mini-keys peer closed an incomplete frame".into()),
            Ok(n) => bytes = &mut bytes[n..],
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(io("read", &e)),
        }
    }
    Ok(())
}

/// Read one frame of at most `bound` bytes before `end`. The length is
/// refused before any body byte is read.
pub fn read_frame(stream: &mut UnixStream, bound: usize, end: Instant) -> Result<Vec<u8>, String> {
    let mut header = [0u8; 4];
    read_exact(stream, &mut header, end)?;
    let size = u32::from_le_bytes(header) as usize;
    if size == 0 || size > bound.min(MAX_FRAME) {
        return Err("mini-keys frame exceeds bound".into());
    }
    let mut bytes = vec![0; size];
    if let Err(error) = read_exact(stream, &mut bytes, end) {
        zero(&mut bytes);
        return Err(error);
    }
    Ok(bytes)
}

/// Send one JSON object.
pub fn send(stream: &mut UnixStream, value: &Value, end: Instant) -> Result<(), String> {
    let mut bytes = serde_json::to_vec(value).map_err(|_| "mini-keys encode failed")?;
    let result = write_frame(stream, &bytes, end);
    zero(&mut bytes);
    result
}

/// Receive one JSON object (frame bytes are zeroed once parsed: a request may
/// carry a secret on its way in).
pub fn recv(stream: &mut UnixStream, bound: usize, end: Instant) -> Result<Value, String> {
    let mut bytes = read_frame(stream, bound, end)?;
    let value = serde_json::from_slice::<Value>(&bytes);
    zero(&mut bytes);
    match value {
        Ok(value) if value.is_object() => Ok(value),
        _ => Err("mini-keys frame is not one JSON object".into()),
    }
}

/// A named refusal frame.
pub fn refusal(code: &str, detail: &str) -> Value {
    serde_json::json!({"refused": code, "detail": detail})
}

pub fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push(DIGITS[(b >> 4) as usize] as char);
        out.push(DIGITS[(b & 15) as usize] as char);
    }
    out
}

/// Lowercase hex only; anything else (odd length, uppercase, other bytes) refuses.
pub fn unhex(text: &str) -> Result<Vec<u8>, String> {
    if text.len() % 2 != 0
        || !text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("invalid hex encoding".into());
    }
    let digit = |b: u8| if b.is_ascii_digit() { b - b'0' } else { b - b'a' + 10 };
    Ok(text
        .as_bytes()
        .chunks(2)
        .map(|pair| (digit(pair[0]) << 4) | digit(pair[1]))
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn frames_round_trip_and_bounds_refuse_before_the_body() {
        let (mut a, mut b) = UnixStream::pair().unwrap();
        let end = Instant::now() + Duration::from_secs(1);
        send(&mut a, &serde_json::json!({"op":"hello"}), end).unwrap();
        assert_eq!(recv(&mut b, 64, end).unwrap()["op"], "hello");
        a.write_all(&(65u32).to_le_bytes()).unwrap();
        assert!(read_frame(&mut b, 64, end).unwrap_err().contains("exceeds bound"));
        a.write_all(&(2u32).to_le_bytes()).unwrap();
        a.write_all(b"[]").unwrap();
        assert!(recv(&mut b, 64, end).unwrap_err().contains("not one JSON object"));
    }

    #[test]
    fn a_silent_peer_times_out_at_the_deadline() {
        let (_a, mut b) = UnixStream::pair().unwrap();
        let start = Instant::now();
        let error = read_frame(&mut b, 64, start + Duration::from_millis(60)).unwrap_err();
        assert!(error.contains("timed out"), "{error}");
        assert!(start.elapsed() < Duration::from_secs(1));
    }

    #[test]
    fn hex_is_lowercase_canonical() {
        assert_eq!(unhex(&hex(&[0, 1, 0xfe])).unwrap(), vec![0, 1, 0xfe]);
        assert!(unhex("0A").is_err());
        assert!(unhex("abc").is_err());
    }
}
