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
    use std::os::fd::AsRawFd;
    use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
    use std::os::unix::net::UnixStream;
    use std::path::Path;
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    use std::time::{Duration, Instant};

    const MAX_HEAD: usize = 64 * 1024;
    const MAX_BODY: usize = 8 * 1024 * 1024;
    const MAX_RESPONSE: usize = 8 * 1024 * 1024 + 64 * 1024;
    // This entrance can front class L (128 admitted sockets), with room for
    // HTTP requests and handshakes. Mini still owns per-grain admission/caps.
    const MAX_CONNECTIONS: usize = 136;
    const STREAM_BUFFER: usize = 64 * 1024;
    const CLOSE_DRAIN_TIME: Duration = Duration::from_secs(5);
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

    fn has_token(head: &[u8], name: &str, token: &str) -> bool {
        std::str::from_utf8(head).ok().is_some_and(|text| {
            text.split("\r\n")
                .skip(1)
                .filter_map(|line| line.split_once(':'))
                .any(|(key, value)| {
                    key.eq_ignore_ascii_case(name)
                        && value
                            .split(',')
                            .any(|part| part.trim().eq_ignore_ascii_case(token))
                })
        })
    }

    fn read_response_head(upstream: &mut UnixStream, deadline: Instant) -> io::Result<Vec<u8>> {
        let mut response = Vec::new();
        loop {
            upstream.set_read_timeout(Some(remaining(deadline)?))?;
            let mut chunk = [0; 8192];
            let count = upstream.read(&mut chunk)?;
            if count == 0 {
                return Err(invalid("TLS upstream response ended before head"));
            }
            response.extend_from_slice(&chunk[..count]);
            if let Some(end) = response.windows(4).position(|p| p == b"\r\n\r\n") {
                if end + 4 > MAX_HEAD {
                    return Err(invalid("TLS response head bound"));
                }
                return Ok(response);
            }
            if response.len() > MAX_HEAD {
                return Err(invalid("TLS response head bound"));
            }
        }
    }

    // rustls has one owner; a nonblocking poll loop drives both directions.
    // Every queue is bounded, so a slow peer applies backpressure rather than
    // causing unbounded buffering. Upgraded connections have no idle deadline.
    fn splice(
        mut tls: StreamOwned<ServerConnection, TcpStream>,
        mut upstream: UnixStream,
    ) -> io::Result<()> {
        tls.sock.set_nonblocking(true)?;
        upstream.set_nonblocking(true)?;
        tls.conn.set_buffer_limit(Some(STREAM_BUFFER));
        let mut pending = Vec::with_capacity(STREAM_BUFFER);
        let mut sent = 0;
        let mut upstream_eof = false;
        let mut client_eof = false;
        let mut client_shutdown = false;
        let mut close_deadline = None;
        loop {
            // Drain already-decrypted bytes even when the TCP fd isn't readable.
            if sent == pending.len() {
                pending.clear();
                sent = 0;
            }
            while !client_eof && pending.len() < STREAM_BUFFER {
                let mut chunk = [0; 8192];
                let room = chunk.len().min(STREAM_BUFFER - pending.len());
                match tls.conn.reader().read(&mut chunk[..room]) {
                    Ok(0) => {
                        client_eof = true;
                        break;
                    }
                    Ok(n) => pending.extend_from_slice(&chunk[..n]),
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock => break,
                    Err(e) => return Err(e),
                }
            }
            if client_eof && close_deadline.is_none() {
                close_deadline = Some(Instant::now() + CLOSE_DRAIN_TIME);
            }
            while sent < pending.len() {
                match upstream.write(&pending[sent..]) {
                    Ok(0) => return Err(invalid("TLS upstream stream write ended")),
                    Ok(n) => sent += n,
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock => break,
                    Err(e) => return Err(e),
                }
            }
            if sent == pending.len() {
                pending.clear();
                sent = 0;
            }
            if client_eof && pending.is_empty() && !client_shutdown {
                // TLS close-notify closes the sending half. Preserve an app's
                // final reply/close frame before closing the receiving half.
                upstream.shutdown(std::net::Shutdown::Write)?;
                client_shutdown = true;
            }
            while tls.conn.wants_write() {
                match tls.conn.write_tls(&mut tls.sock) {
                    Ok(0) => return Err(invalid("TLS stream write ended")),
                    Ok(_) => (),
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock => break,
                    Err(e) => return Err(e),
                }
            }
            if upstream_eof && !tls.conn.wants_write() {
                return Ok(());
            }
            let mut fds = [
                libc::pollfd {
                    fd: tls.sock.as_raw_fd(),
                    events: (if pending.len() < STREAM_BUFFER && !upstream_eof && !client_eof {
                        libc::POLLIN
                    } else {
                        0
                    }) | (if tls.conn.wants_write() {
                        libc::POLLOUT
                    } else {
                        0
                    }),
                    revents: 0,
                },
                libc::pollfd {
                    fd: upstream.as_raw_fd(),
                    events: (if !tls.conn.wants_write() && !upstream_eof {
                        libc::POLLIN
                    } else {
                        0
                    }) | (if sent < pending.len() {
                        libc::POLLOUT
                    } else {
                        0
                    }),
                    revents: 0,
                },
            ];
            // poll reports HUP even when events is zero. Suppress a stalled
            // direction completely until its bounded output queue drains.
            for fd in &mut fds {
                if fd.events == 0 {
                    fd.fd = -1;
                }
            }
            let timeout = match close_deadline {
                None => -1,
                Some(deadline) => {
                    let left = deadline.saturating_duration_since(Instant::now());
                    if left.is_zero() {
                        return Err(io::Error::new(
                            io::ErrorKind::TimedOut,
                            "TLS upgraded close drain deadline",
                        ));
                    }
                    left.as_millis().max(1).min(i32::MAX as u128) as i32
                }
            };
            let ready = unsafe { libc::poll(fds.as_mut_ptr(), fds.len() as _, timeout) };
            if ready < 0 {
                let e = io::Error::last_os_error();
                if e.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(e);
            }
            if fds.iter().any(|p| p.revents & libc::POLLNVAL != 0) {
                return Err(invalid("TLS stream fd closed"));
            }
            if fds[0].revents & (libc::POLLIN | libc::POLLHUP | libc::POLLERR) != 0 {
                match tls.conn.read_tls(&mut tls.sock) {
                    Ok(0) => {
                        client_eof = true;
                    }
                    Ok(_) => {
                        tls.conn.process_new_packets().map_err(io::Error::other)?;
                    }
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock => (),
                    Err(e) => return Err(e),
                }
            }
            if !upstream_eof
                && !tls.conn.wants_write()
                && fds[1].revents & (libc::POLLIN | libc::POLLHUP | libc::POLLERR) != 0
            {
                let mut chunk = [0; 8192];
                match upstream.read(&mut chunk) {
                    Ok(0) => {
                        upstream_eof = true;
                        tls.conn.send_close_notify();
                    }
                    Ok(n) => tls.conn.writer().write_all(&chunk[..n])?,
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock => (),
                    Err(e) => return Err(e),
                }
            }
        }
    }

    struct ConnectionSlot(Arc<AtomicUsize>);
    impl ConnectionSlot {
        fn reserve(count: &Arc<AtomicUsize>) -> Option<Self> {
            count
                .fetch_update(Ordering::AcqRel, Ordering::Relaxed, |n| {
                    (n < MAX_CONNECTIONS).then_some(n + 1)
                })
                .ok()
                .map(|_| Self(Arc::clone(count)))
        }
    }
    impl Drop for ConnectionSlot {
        fn drop(&mut self) {
            self.0.fetch_sub(1, Ordering::Release);
        }
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
        let request_head = frame
            .windows(4)
            .position(|p| p == b"\r\n\r\n")
            .map(|n| &frame[..n + 4])
            .ok_or_else(|| invalid("TLS request head missing"))?;
        let upgrade = has_token(request_head, "connection", "upgrade")
            && has_token(request_head, "upgrade", "websocket");
        if !upgrade {
            upstream.shutdown(std::net::Shutdown::Write)?;
        }
        let deadline = Instant::now() + RESPONSE_TIME;
        let mut response = read_response_head(&mut upstream, deadline)?;
        let status = response.split(|b| *b == b'\n').next().unwrap_or_default();
        let switching = status.starts_with(b"HTTP/1.1 101 ");
        if switching {
            let end = response.windows(4).position(|p| p == b"\r\n\r\n").unwrap() + 4;
            if !upgrade
                || !has_token(&response[..end], "connection", "upgrade")
                || !has_token(&response[..end], "upgrade", "websocket")
            {
                return Err(invalid("TLS unexpected upstream upgrade"));
            }
            // Include any first frame that arrived with the 101 head exactly once.
            tls.write_all(&response)?;
            tls.flush()?;
            return splice(tls, upstream);
        }
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

    #[cfg(test)]
    mod tests {
        use super::*;
        use rustls::{ClientConfig, ClientConnection, RootCertStore};
        use std::os::unix::net::UnixListener;
        use std::thread;

        const CERT: &[u8] = include_bytes!("../../tests/fixtures/browser-proxy-test.crt");
        const KEY: &[u8] = include_bytes!("../../tests/fixtures/browser-proxy-test.key");
        const OPEN: &[u8] = b"GET /socket HTTP/1.1\r\nHost: localhost\r\nConnection: keep-alive, Upgrade\r\nUpgrade: websocket\r\n\r\n";
        const SWITCH: &[u8] = b"HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\nUpgrade: websocket\r\n\r\n";

        fn configs() -> (Arc<ServerConfig>, Arc<ClientConfig>) {
            let _ = rustls::crypto::ring::default_provider().install_default();
            let certs: Vec<_> = rustls_pemfile::certs(&mut BufReader::new(CERT))
                .collect::<Result<_, _>>()
                .unwrap();
            let key = rustls_pemfile::private_key(&mut BufReader::new(KEY))
                .unwrap()
                .unwrap();
            let mut roots = RootCertStore::empty();
            roots.add(certs[0].clone()).unwrap();
            (
                Arc::new(
                    ServerConfig::builder()
                        .with_no_client_auth()
                        .with_single_cert(certs, key)
                        .unwrap(),
                ),
                Arc::new(
                    ClientConfig::builder()
                        .with_root_certificates(roots)
                        .with_no_client_auth(),
                ),
            )
        }

        fn harness<F>(
            upstream: F,
        ) -> (
            StreamOwned<ClientConnection, TcpStream>,
            thread::JoinHandle<io::Result<()>>,
            thread::JoinHandle<()>,
        )
        where
            F: FnOnce(UnixStream) + Send + 'static,
        {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let path = std::env::temp_dir().join(format!(
                "spk-proxy-{}-{}.sock",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let unix = UnixListener::bind(&path).unwrap();
            let tcp = TcpListener::bind(("127.0.0.1", 0)).unwrap();
            let addr = tcp.local_addr().unwrap();
            let (server, client) = configs();
            let app = thread::spawn(move || {
                let (stream, _) = unix.accept().unwrap();
                stream
                    .set_read_timeout(Some(Duration::from_secs(5)))
                    .unwrap();
                stream
                    .set_write_timeout(Some(Duration::from_secs(5)))
                    .unwrap();
                upstream(stream);
            });
            let proxy = thread::spawn(move || {
                let result = handle(&path, tcp.accept().unwrap().0, server);
                fs::remove_file(path).unwrap();
                result
            });
            let socket = TcpStream::connect(addr).unwrap();
            socket
                .set_read_timeout(Some(Duration::from_secs(5)))
                .unwrap();
            socket
                .set_write_timeout(Some(Duration::from_secs(5)))
                .unwrap();
            (
                StreamOwned::new(
                    ClientConnection::new(client, "localhost".try_into().unwrap()).unwrap(),
                    socket,
                ),
                proxy,
                app,
            )
        }

        fn request(stream: &mut UnixStream) -> Vec<u8> {
            let mut bytes = vec![];
            while !bytes.ends_with(b"\r\n\r\n") {
                let mut byte = [0];
                stream.read_exact(&mut byte).unwrap();
                bytes.push(byte[0]);
            }
            bytes
        }

        #[test]
        fn websocket_duplex_preserves_first_frame_and_backpressures_large_payload() {
            let payload = vec![b'x'; STREAM_BUFFER * 5 + 37];
            let expected = payload.clone();
            let (mut client, proxy, app) = harness(move |mut upstream| {
                assert_eq!(request(&mut upstream), OPEN);
                let mut response = SWITCH.to_vec();
                response.extend_from_slice(b"first-frame");
                upstream.write_all(&response).unwrap();
                let mut got = vec![0; expected.len()];
                upstream.read_exact(&mut got).unwrap();
                assert_eq!(got, expected);
                upstream.write_all(&got).unwrap();
            });
            client.write_all(OPEN).unwrap();
            client.flush().unwrap();
            let mut first = vec![0; SWITCH.len() + 11];
            client.read_exact(&mut first).unwrap();
            assert_eq!(&first[..SWITCH.len()], SWITCH);
            assert_eq!(&first[SWITCH.len()..], b"first-frame");
            client.write_all(&payload).unwrap();
            client.flush().unwrap();
            let mut echoed = vec![0; payload.len()];
            client.read_exact(&mut echoed).unwrap();
            assert_eq!(echoed, payload);
            let mut byte = [0];
            assert_eq!(client.read(&mut byte).unwrap(), 0);
            drop(client);
            app.join().unwrap();
            proxy.join().unwrap().unwrap();
        }

        #[test]
        fn ordinary_http_and_declined_upgrade_still_return_complete_response() {
            for frame in [
                b"GET / HTTP/1.1\r\nHost: localhost\r\n\r\n".as_slice(),
                OPEN,
            ] {
                let expected = frame.to_vec();
                let (mut client, proxy, app) = harness(move |mut upstream| {
                    assert_eq!(request(&mut upstream), expected);
                    upstream
                        .write_all(b"HTTP/1.1 403 Forbidden\r\nContent-Length: 6\r\n\r\ndenied")
                        .unwrap();
                });
                client.write_all(frame).unwrap();
                client.flush().unwrap();
                let mut got =
                    vec![0; b"HTTP/1.1 403 Forbidden\r\nContent-Length: 6\r\n\r\ndenied".len()];
                client.read_exact(&mut got).unwrap();
                assert_eq!(
                    &got,
                    b"HTTP/1.1 403 Forbidden\r\nContent-Length: 6\r\n\r\ndenied"
                );
                drop(client);
                app.join().unwrap();
                proxy.join().unwrap().unwrap();
            }
        }

        #[test]
        fn client_close_releases_upstream_and_unexpected_101_is_refused() {
            let (mut client, proxy, app) = harness(|mut upstream| {
                request(&mut upstream);
                upstream.write_all(SWITCH).unwrap();
                let mut byte = [0];
                let mut last = [0; 10];
                upstream.read_exact(&mut last).unwrap();
                assert_eq!(&last, b"last-frame");
                assert_eq!(upstream.read(&mut byte).unwrap(), 0);
            });
            client.write_all(OPEN).unwrap();
            client.flush().unwrap();
            let mut head = vec![0; SWITCH.len()];
            client.read_exact(&mut head).unwrap();
            client.write_all(b"last-frame").unwrap();
            client.conn.send_close_notify();
            client.flush().unwrap();
            drop(client);
            app.join().unwrap();
            proxy.join().unwrap().unwrap();

            let (mut client, proxy, app) = harness(|mut upstream| {
                request(&mut upstream);
                upstream.write_all(SWITCH).unwrap();
            });
            client
                .write_all(b"GET / HTTP/1.1\r\nHost: localhost\r\n\r\n")
                .unwrap();
            client.flush().unwrap();
            let mut byte = [0];
            assert!(client.read(&mut byte).is_err());
            drop(client);
            app.join().unwrap();
            assert!(proxy
                .join()
                .unwrap()
                .unwrap_err()
                .to_string()
                .contains("unexpected upstream upgrade"));
        }

        #[test]
        fn client_half_close_keeps_final_upstream_reply() {
            let (mut client, proxy, app) = harness(|mut upstream| {
                request(&mut upstream);
                upstream.write_all(SWITCH).unwrap();
                let mut received = Vec::new();
                upstream.read_to_end(&mut received).unwrap();
                assert_eq!(&received, b"client-close");
                upstream.write_all(b"server-close").unwrap();
            });
            client.write_all(OPEN).unwrap();
            client.flush().unwrap();
            let mut head = vec![0; SWITCH.len()];
            client.read_exact(&mut head).unwrap();
            client.write_all(b"client-close").unwrap();
            client.conn.send_close_notify();
            client.flush().unwrap();
            let mut reply = [0; 12];
            client.read_exact(&mut reply).unwrap();
            assert_eq!(&reply, b"server-close");
            let mut byte = [0];
            assert_eq!(client.read(&mut byte).unwrap(), 0);
            drop(client);
            app.join().unwrap();
            proxy.join().unwrap().unwrap();
        }

        #[test]
        fn connection_slots_are_bounded_and_returned_on_drop() {
            let count = Arc::new(AtomicUsize::new(0));
            let mut slots: Vec<_> = (0..MAX_CONNECTIONS)
                .map(|_| ConnectionSlot::reserve(&count).unwrap())
                .collect();
            assert!(ConnectionSlot::reserve(&count).is_none());
            slots.pop();
            assert!(ConnectionSlot::reserve(&count).is_some());
            drop(slots);
            assert_eq!(count.load(Ordering::Relaxed), 0);
        }
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
        let active = Arc::new(AtomicUsize::new(0));
        for connection in listener.incoming() {
            match connection {
                Ok(connection) => {
                    let Some(slot) = ConnectionSlot::reserve(&active) else {
                        continue;
                    };
                    let socket = socket.clone();
                    let config = Arc::clone(&config);
                    std::thread::Builder::new()
                        .name("spk-browser".into())
                        .spawn(move || {
                            let _slot = slot;
                            if let Err(error) = handle(&socket, connection, config) {
                                eprintln!("spk-browser-proxy: connection: {error}");
                            }
                        })?;
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
