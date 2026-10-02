//! Bounded HTTP/1.1: one request per connection, `Content-Length` bodies only.
//!
//! The endpoint sits behind Caddy on loopback, so this reads exactly what a reverse proxy
//! forwards and refuses everything else (chunked bodies, oversize heads and bodies).

use std::io::{Read, Write};
use std::net::TcpStream;
use std::time::Duration;

pub const MAX_HEAD: usize = 16 * 1024;
pub const MAX_BODY: usize = 64 * 1024;

#[derive(Debug)]
pub struct Request {
    pub method: String,
    pub path: String,
    /// The query string after `?`, or empty.
    pub query: String,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

impl Request {
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(k, _)| k.eq_ignore_ascii_case(name))
            .map(|(_, v)| v.as_str())
    }
}

/// Why a request could not be read; the status to answer with, if any.
#[derive(Debug)]
pub struct ReadError {
    pub status: Option<(u16, &'static str)>,
    pub detail: String,
}

fn bad(status: u16, reason: &'static str, detail: impl Into<String>) -> ReadError {
    ReadError { status: Some((status, reason)), detail: detail.into() }
}

fn find_head_end(buf: &[u8]) -> Option<usize> {
    buf.windows(4).position(|w| w == b"\r\n\r\n")
}

pub fn read_request(stream: &mut TcpStream) -> Result<Request, ReadError> {
    let _ = stream.set_read_timeout(Some(Duration::from_secs(10)));
    let mut buf = Vec::with_capacity(4096);
    let mut chunk = [0u8; 4096];
    let head_end = loop {
        if let Some(end) = find_head_end(&buf) {
            break end;
        }
        if buf.len() > MAX_HEAD {
            return Err(bad(431, "Request Header Fields Too Large", "head too large"));
        }
        let n = stream
            .read(&mut chunk)
            .map_err(|e| ReadError { status: None, detail: format!("read: {e}") })?;
        if n == 0 {
            return Err(ReadError { status: None, detail: "closed before the head ended".into() });
        }
        buf.extend_from_slice(&chunk[..n]);
    };
    let head = std::str::from_utf8(&buf[..head_end])
        .map_err(|_| bad(400, "Bad Request", "head is not UTF-8"))?;
    let mut lines = head.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split(' ');
    let (method, target, version) = match (parts.next(), parts.next(), parts.next(), parts.next()) {
        (Some(m), Some(t), Some(v), None) => (m, t, v),
        _ => return Err(bad(400, "Bad Request", "malformed request line")),
    };
    if version != "HTTP/1.1" && version != "HTTP/1.0" {
        return Err(bad(505, "HTTP Version Not Supported", "not HTTP/1.x"));
    }
    let path = target.split('?').next().unwrap_or("").to_string();
    let query = target.split_once('?').map(|(_, q)| q.to_string()).unwrap_or_default();
    let mut headers = Vec::new();
    for line in lines {
        let (k, v) = line
            .split_once(':')
            .ok_or_else(|| bad(400, "Bad Request", "malformed header"))?;
        headers.push((k.trim().to_string(), v.trim().to_string()));
    }
    let mut request = Request { method: method.to_string(), path, query, headers, body: Vec::new() };
    if request.header("transfer-encoding").is_some() {
        return Err(bad(411, "Length Required", "only Content-Length bodies are accepted"));
    }
    let length = match request.header("content-length") {
        None => 0,
        Some(v) => v.parse::<usize>().map_err(|_| bad(400, "Bad Request", "bad Content-Length"))?,
    };
    if length > MAX_BODY {
        return Err(bad(413, "Payload Too Large", format!("body of {length} bytes")));
    }
    let mut body = buf[head_end + 4..].to_vec();
    if body.len() > length {
        return Err(bad(400, "Bad Request", "more bytes than Content-Length"));
    }
    while body.len() < length {
        let n = stream
            .read(&mut chunk)
            .map_err(|e| ReadError { status: None, detail: format!("read body: {e}") })?;
        if n == 0 {
            return Err(ReadError { status: None, detail: "closed inside the body".into() });
        }
        body.extend_from_slice(&chunk[..n]);
        if body.len() > length {
            return Err(bad(400, "Bad Request", "more bytes than Content-Length"));
        }
    }
    request.body = body;
    Ok(request)
}

pub fn write_response(
    stream: &mut TcpStream,
    status: u16,
    reason: &str,
    content_type: &str,
    body: &[u8],
) -> std::io::Result<()> {
    let head = format!(
        "HTTP/1.1 {status} {reason}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(head.as_bytes())?;
    stream.write_all(body)?;
    stream.flush()
}

/// One plain-HTTP request to a loopback address; returns (status, body).
/// Used by the fake Discord and the tests, never by the endpoint itself.
pub fn client_request(
    addr: &str,
    method: &str,
    path: &str,
    headers: &[(&str, &str)],
    body: &[u8],
) -> Result<(u16, Vec<u8>), String> {
    let mut stream = TcpStream::connect(addr).map_err(|e| format!("connect {addr}: {e}"))?;
    let _ = stream.set_read_timeout(Some(Duration::from_secs(30)));
    let mut head = format!("{method} {path} HTTP/1.1\r\nHost: {addr}\r\nConnection: close\r\n");
    for (k, v) in headers {
        head.push_str(&format!("{k}: {v}\r\n"));
    }
    head.push_str(&format!("Content-Length: {}\r\n\r\n", body.len()));
    stream.write_all(head.as_bytes()).map_err(|e| e.to_string())?;
    stream.write_all(body).map_err(|e| e.to_string())?;
    let mut out = Vec::new();
    stream.read_to_end(&mut out).map_err(|e| format!("read response: {e}"))?;
    let end = find_head_end(&out).ok_or("response has no head")?;
    let head = String::from_utf8_lossy(&out[..end]);
    let status = head
        .split(' ')
        .nth(1)
        .and_then(|s| s.parse().ok())
        .ok_or("response has no status")?;
    Ok((status, out[end + 4..].to_vec()))
}
