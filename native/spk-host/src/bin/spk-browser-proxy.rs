//! Private loopback TLS entrance for one fixed custodian Unix socket.
//!
//! An owner-controlled SSH `-L` forwards this loopback port to a laptop. The
//! browser trusts an operator-provided certificate for this custodian's own
//! hostname; this binary never changes certificate trust or listens publicly.

#[cfg(target_os = "linux")]
mod linux {
    use minidregg_spk_host::hostd::Journal;
    use rustls::{ServerConfig, ServerConnection, StreamOwned};
    use std::fs::{self, File};
    use std::io::{self, BufReader, Read, Write};
    use std::net::{TcpListener, TcpStream};
    use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
    use std::os::unix::net::UnixStream;
    use std::path::Path;
    use std::sync::Arc;
    use std::time::{Duration, Instant};

    const MAX_HEAD: usize = 64 * 1024;
    const MAX_BODY: usize = 8 * 1024 * 1024;
    const MAX_RESPONSE: usize = 8 * 1024 * 1024 + 64 * 1024;
    const REQUEST_TIME: Duration = Duration::from_secs(10);
    const RESPONSE_TIME: Duration = Duration::from_secs(30);

    fn invalid(reason: &'static str) -> io::Error {
        io::Error::new(io::ErrorKind::InvalidData, reason)
    }

    fn private_file(path: &Path) -> io::Result<File> {
        let meta = fs::symlink_metadata(path)?;
        if !meta.is_file()
            || meta.file_type().is_symlink()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
        {
            return Err(invalid("private TLS file identity drift"));
        }
        File::open(path)
    }

    fn tls_config(directory: &Path) -> io::Result<Arc<ServerConfig>> {
        let mut cert = BufReader::new(private_file(&directory.join("tls.crt"))?);
        let certs: Vec<_> = rustls_pemfile::certs(&mut cert).collect::<Result<_, _>>()?;
        if certs.is_empty() || certs.len() > 8 {
            return Err(invalid("TLS certificate chain length refused"));
        }
        let mut key = BufReader::new(private_file(&directory.join("tls.key"))?);
        let key = rustls_pemfile::private_key(&mut key)?
            .ok_or_else(|| invalid("TLS private key missing"))?;
        let _ = rustls::crypto::ring::default_provider().install_default();
        let config = ServerConfig::builder()
            .with_no_client_auth()
            .with_single_cert(certs, key)
            .map_err(io::Error::other)?;
        Ok(Arc::new(config))
    }

    fn remaining(deadline: Instant) -> io::Result<Duration> {
        let left = deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "private TLS request deadline",
            ))
        } else {
            Ok(left)
        }
    }

    fn frame_length(head: &[u8]) -> io::Result<usize> {
        let text = std::str::from_utf8(head).map_err(|_| invalid("TLS HTTP head encoding"))?;
        let mut lines = text.split("\r\n");
        let first = lines
            .next()
            .ok_or_else(|| invalid("TLS HTTP request line"))?;
        if !first.ends_with(" HTTP/1.1") {
            return Err(invalid("TLS HTTP version unavailable"));
        }
        let mut content_length = None;
        for line in lines {
            if line.is_empty() {
                continue;
            }
            let (name, value) = line
                .split_once(':')
                .ok_or_else(|| invalid("TLS HTTP header"))?;
            if name.eq_ignore_ascii_case("transfer-encoding") {
                return Err(invalid("TLS HTTP transfer encoding unavailable"));
            }
            if name.eq_ignore_ascii_case("content-length") {
                if content_length.is_some() {
                    return Err(invalid("TLS HTTP duplicate length"));
                }
                let value = value.trim();
                if value.is_empty()
                    || (value.len() > 1 && value.starts_with('0'))
                    || !value.bytes().all(|byte| byte.is_ascii_digit())
                {
                    return Err(invalid("TLS HTTP length syntax"));
                }
                content_length = Some(
                    value
                        .parse::<usize>()
                        .map_err(|_| invalid("TLS HTTP length overflow"))?,
                );
            }
        }
        let length = content_length.unwrap_or(0);
        if length > MAX_BODY {
            return Err(invalid("TLS HTTP body bound"));
        }
        Ok(length)
    }

    fn read_frame(tls: &mut StreamOwned<ServerConnection, TcpStream>) -> io::Result<Vec<u8>> {
        let deadline = Instant::now() + REQUEST_TIME;
        let mut bytes = Vec::with_capacity(8192);
        let end = loop {
            if let Some(index) = bytes.windows(4).position(|part| part == b"\r\n\r\n") {
                break index + 4;
            }
            if bytes.len() > MAX_HEAD {
                return Err(invalid("TLS HTTP head bound"));
            }
            tls.sock.set_read_timeout(Some(remaining(deadline)?))?;
            let mut chunk = [0_u8; 8192];
            let count = tls.read(&mut chunk)?;
            if count == 0 {
                return Err(invalid("TLS HTTP request ended"));
            }
            bytes.extend_from_slice(&chunk[..count]);
        };
        if end > MAX_HEAD {
            return Err(invalid("TLS HTTP head bound"));
        }
        let length = frame_length(&bytes[..end - 4])?;
        let total = end
            .checked_add(length)
            .ok_or_else(|| invalid("TLS HTTP frame overflow"))?;
        if bytes.len() > total {
            return Err(invalid("TLS HTTP pipelining unavailable"));
        }
        while bytes.len() < total {
            tls.sock.set_read_timeout(Some(remaining(deadline)?))?;
            let mut chunk = [0_u8; 8192];
            let count = tls.read(&mut chunk)?;
            if count == 0 {
                return Err(invalid("TLS HTTP body ended"));
            }
            bytes.extend_from_slice(&chunk[..count]);
            if bytes.len() > total {
                return Err(invalid("TLS HTTP pipelining unavailable"));
            }
        }
        Ok(bytes)
    }

    fn handle(socket: &Path, raw: TcpStream, config: Arc<ServerConfig>) -> io::Result<()> {
        raw.set_read_timeout(Some(REQUEST_TIME))?;
        raw.set_write_timeout(Some(REQUEST_TIME))?;
        let connection = ServerConnection::new(config).map_err(io::Error::other)?;
        let mut tls = StreamOwned::new(connection, raw);
        let handshake_deadline = Instant::now() + REQUEST_TIME;
        while tls.conn.is_handshaking() {
            let left = remaining(handshake_deadline)?;
            tls.sock.set_read_timeout(Some(left))?;
            tls.sock.set_write_timeout(Some(left))?;
            tls.conn.complete_io(&mut tls.sock)?;
        }
        let frame = read_frame(&mut tls)?;
        let mut upstream = UnixStream::connect(socket)?;
        upstream.set_read_timeout(Some(RESPONSE_TIME))?;
        upstream.set_write_timeout(Some(REQUEST_TIME))?;
        upstream.write_all(&frame)?;
        upstream.shutdown(std::net::Shutdown::Write)?;
        let deadline = Instant::now() + RESPONSE_TIME;
        let mut response = Vec::new();
        loop {
            upstream.set_read_timeout(Some(remaining(deadline)?))?;
            let mut chunk = [0_u8; 8192];
            let count = upstream.read(&mut chunk)?;
            if count == 0 {
                break;
            }
            response.extend_from_slice(&chunk[..count]);
            if response.len() > MAX_RESPONSE {
                return Err(invalid("TLS HTTP response bound"));
            }
        }
        let mut sent = 0;
        while sent < response.len() {
            tls.sock.set_write_timeout(Some(remaining(deadline)?))?;
            let count = tls.write(&response[sent..])?;
            if count == 0 {
                return Err(invalid("TLS response write ended"));
            }
            sent += count;
        }
        tls.flush()
    }

    pub fn main() -> io::Result<()> {
        let args: Vec<String> = std::env::args().collect();
        if args.len() != 3 {
            return Err(invalid(
                "usage: spk-browser-proxy ABS_PRIVATE_CUSTODIAN_DIR LOOPBACK_PORT",
            ));
        }
        let directory = Path::new(&args[1]);
        let _ = Journal::open(directory)?;
        let port = args[2]
            .parse::<u16>()
            .map_err(|_| invalid("TLS port refused"))?;
        if port == 0 || args[2].starts_with('0') {
            return Err(invalid("TLS port refused"));
        }
        let config_file = private_file(&directory.join("custodian.json"))?;
        let config_value: serde_json::Value = serde_json::from_reader(config_file)?;
        let expected_host = config_value
            .get("expectedHost")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| invalid("custodian expectedHost missing"))?;
        if !expected_host.ends_with(&format!(":{port}")) {
            return Err(invalid("TLS loopback port differs from custodian origin"));
        }
        let config = tls_config(directory)?;
        let socket = directory.join("http.sock");
        let meta = fs::symlink_metadata(&socket)?;
        if !meta.file_type().is_socket()
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
        {
            return Err(invalid("custodian Unix socket identity drift"));
        }
        let listener = TcpListener::bind(("127.0.0.1", port))?;
        for connection in listener.incoming() {
            match connection {
                Ok(connection) => {
                    // The initial private deployment serves one request at a
                    // time; no unbounded per-connection threads are created.
                    let _ = handle(&socket, connection, Arc::clone(&config));
                }
                Err(_) => continue,
            }
        }
        Ok(())
    }
}

#[cfg(target_os = "linux")]
fn main() {
    if let Err(error) = linux::main() {
        eprintln!("spk-browser-proxy: {error}");
        std::process::exit(1);
    }
}

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("spk-browser-proxy requires Linux");
    std::process::exit(2);
}
