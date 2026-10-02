//! Public ingress for one existing private Host. No Host process, admission
//! rules, retries or operator requests are introduced here. A stopped relay
//! severs public access while private lifecycle operations remain available.
use crate::transport;
use std::fs;
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

static SIGNAL_STOP: AtomicBool = AtomicBool::new(false);
extern "C" fn stop_signal(_: libc::c_int) {
    SIGNAL_STOP.store(true, Ordering::Relaxed);
}

struct Signals(libc::sigaction, libc::sigaction);
impl Signals {
    fn install() -> Result<Self, String> {
        // Installation happens before any worker exists. The handler only
        // stores to an atomic; all cleanup happens on ordinary Rust threads.
        unsafe {
            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = stop_signal as *const () as usize;
            libc::sigemptyset(&mut action.sa_mask);
            let mut term = std::mem::zeroed();
            let mut interrupt = std::mem::zeroed();
            if libc::sigaction(libc::SIGTERM, &action, &mut term) != 0 {
                return Err(format!(
                    "cannot install relay stop handler: {}",
                    io::Error::last_os_error()
                ));
            }
            if libc::sigaction(libc::SIGINT, &action, &mut interrupt) != 0 {
                libc::sigaction(libc::SIGTERM, &term, std::ptr::null_mut());
                return Err(format!(
                    "cannot install relay interrupt handler: {}",
                    io::Error::last_os_error()
                ));
            }
            Ok(Self(term, interrupt))
        }
    }
}
impl Drop for Signals {
    fn drop(&mut self) {
        unsafe {
            libc::sigaction(libc::SIGTERM, &self.0, std::ptr::null_mut());
            libc::sigaction(libc::SIGINT, &self.1, std::ptr::null_mut());
        }
    }
}

#[derive(Clone, Copy)]
struct Bounds {
    connections: usize,
    read: Duration,
    connect: Duration,
    write: Duration,
    response: Duration,
}
const BOUNDS: Bounds = Bounds {
    connections: 64,
    read: Duration::from_secs(10),
    connect: Duration::from_secs(10),
    write: Duration::from_secs(10),
    response: Duration::from_secs(600),
};

/// Whole-frame deadline, including partial writes and trickling reads. Every
/// wait is interruptible, including a saturated upstream listen backlog.
struct BoundedStream<'a> {
    stream: &'a mut UnixStream,
    stop: &'a AtomicBool,
    deadline: Instant,
}
fn wait_fd(fd: i32, events: i16, stop: &AtomicBool, deadline: Instant) -> io::Result<()> {
    loop {
        if stop.load(Ordering::Acquire) {
            return Err(io::Error::new(
                io::ErrorKind::ConnectionAborted,
                "public ingress stopping",
            ));
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "public ingress I/O deadline",
            ));
        }
        let mut item = libc::pollfd {
            fd,
            events,
            revents: 0,
        };
        let millis = remaining.as_millis().clamp(1, 100) as i32;
        let ready = unsafe { libc::poll(&mut item, 1, millis) };
        if ready > 0 {
            return Ok(());
        }
        if ready < 0 {
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        }
    }
}
impl Read for BoundedStream<'_> {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        loop {
            wait_fd(
                self.stream.as_raw_fd(),
                libc::POLLIN,
                self.stop,
                self.deadline,
            )?;
            match self.stream.read(bytes) {
                Err(e)
                    if matches!(
                        e.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                    ) => {}
                result => return result,
            }
        }
    }
}
impl Write for BoundedStream<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        loop {
            wait_fd(
                self.stream.as_raw_fd(),
                libc::POLLOUT,
                self.stop,
                self.deadline,
            )?;
            match self.stream.write(bytes) {
                Err(e)
                    if matches!(
                        e.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                    ) => {}
                result => return result,
            }
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn connect(path: &Path, stop: &AtomicBool, deadline: Instant) -> io::Result<UnixStream> {
    let bytes = path.as_os_str().as_bytes();
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if bytes.is_empty() || bytes.contains(&0) || bytes.len() >= address.sun_path.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "invalid Unix socket path",
        ));
    }
    address.sun_family = libc::AF_UNIX as _;
    for (to, from) in address.sun_path.iter_mut().zip(bytes) {
        *to = *from as _;
    }
    #[cfg(any(
        target_os = "macos",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd"
    ))]
    {
        address.sun_len = std::mem::size_of::<libc::sockaddr_un>() as _;
    }
    let fd = unsafe { libc::socket(libc::AF_UNIX, libc::SOCK_STREAM, 0) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    let stream = unsafe { UnixStream::from_raw_fd(fd) };
    if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } < 0 {
        return Err(io::Error::last_os_error());
    }
    stream.set_nonblocking(true)?;
    loop {
        if stop.load(Ordering::Acquire) {
            return Err(io::Error::new(
                io::ErrorKind::ConnectionAborted,
                "public ingress stopping",
            ));
        }
        let result = unsafe {
            libc::connect(
                fd,
                (&address as *const libc::sockaddr_un).cast(),
                std::mem::size_of_val(&address) as _,
            )
        };
        if result == 0 {
            return Ok(stream);
        }
        let error = io::Error::last_os_error();
        match error.raw_os_error() {
            Some(libc::EINPROGRESS | libc::EALREADY) => {
                wait_fd(fd, libc::POLLOUT, stop, deadline)?;
                if let Some(error) = stream.take_error()? {
                    return Err(error);
                }
                // A successful SO_ERROR read is sufficient only after a pending
                // connect. EAGAIN on Unix backlog-full did not start a connect.
                return Ok(stream);
            }
            Some(libc::EISCONN) => return Ok(stream),
            Some(libc::EAGAIN | libc::EINTR) => {
                if Instant::now() >= deadline {
                    return Err(io::Error::new(
                        io::ErrorKind::TimedOut,
                        "public ingress connect deadline",
                    ));
                }
                std::thread::sleep(Duration::from_millis(10));
            }
            _ => return Err(error),
        }
    }
}

fn private_directory(path: &Path) -> Result<(), String> {
    if !path.is_absolute() {
        return Err("public proxy socket paths must be absolute".into());
    }
    let parent = path.parent().ok_or("socket requires a parent directory")?;
    let metadata =
        fs::metadata(parent).map_err(|e| format!("cannot inspect {}: {e}", parent.display()))?;
    if !metadata.is_dir()
        || metadata.uid() != transport::effective_uid()
        || metadata.mode() & 0o077 != 0
    {
        return Err(format!(
            "socket directory {} must be owned by this user with mode 0700",
            parent.display()
        ));
    }
    Ok(())
}
fn check_upstream(path: &Path, config: &[u8]) -> Result<(), String> {
    private_directory(path)?;
    // Existing operator service pins are read, never created or changed here.
    for (pin, expected) in [
        (path.with_extension("mode"), b"operator-v1".as_slice()),
        (path.with_extension("config"), config),
    ] {
        let metadata =
            fs::symlink_metadata(&pin).map_err(|e| format!("cannot inspect upstream pin: {e}"))?;
        if !metadata.is_file()
            || metadata.uid() != transport::effective_uid()
            || metadata.mode() & 0o077 != 0
        {
            return Err("upstream pin is not an owner-private regular file".into());
        }
        if transport::read_config(&pin)? != expected {
            return Err("upstream operator mode/config pin mismatch".into());
        }
    }
    let metadata =
        fs::symlink_metadata(path).map_err(|e| format!("cannot inspect upstream socket: {e}"))?;
    if !metadata.file_type().is_socket()
        || metadata.uid() != transport::effective_uid()
        || metadata.mode() & 0o077 != 0
    {
        return Err("upstream is not an owner-private Unix socket".into());
    }
    Ok(())
}

fn refusal(stream: &mut UnixStream, stop: &AtomicBool, bounds: Bounds, reason: &str) {
    let mut frame = vec![254];
    frame.extend_from_slice(reason.as_bytes());
    let _ = transport::write_frame(
        &mut BoundedStream {
            stream,
            stop,
            deadline: Instant::now() + bounds.write,
        },
        &frame,
    );
}

fn connection(
    mut public: UnixStream,
    upstream: &Path,
    config: &[u8],
    catalog: bool,
    stop: &AtomicBool,
    bounds: Bounds,
    accepted: Instant,
) {
    if public.set_nonblocking(true).is_err() {
        return;
    }
    let frame = match transport::read_frame(&mut BoundedStream {
        stream: &mut public,
        stop,
        deadline: accepted + bounds.read,
    }) {
        Ok(Some(frame)) => frame,
        Ok(None) => return,
        Err(_) => {
            return refusal(
                &mut public,
                stop,
                bounds,
                "invalid socket frame or ingress deadline",
            )
        }
    };
    if let Err(reason) = transport::public_envelope(&frame, config, catalog) {
        return refusal(&mut public, stop, bounds, reason);
    }
    // Recheck retained config/mode on every request: a restarted backend must
    // not silently introduce a new deployment under a still-running relay.
    if check_upstream(upstream, config).is_err() {
        return refusal(
            &mut public,
            stop,
            bounds,
            "upstream operator mode/config pin mismatch",
        );
    }
    let mut private = match connect(upstream, stop, Instant::now() + bounds.connect) {
        Ok(stream) => stream,
        Err(_) => {
            return refusal(
                &mut public,
                stop,
                bounds,
                "public ingress upstream unavailable",
            )
        }
    };
    if transport::peer_uid(&private).ok() != Some(transport::effective_uid()) {
        return refusal(&mut public, stop, bounds, "upstream peer UID mismatch");
    }
    // Once the first write starts, failure is uncertain. Never manufacture a
    // 254 refusal after forwarding; an admitted request may have lost its reply.
    if transport::write_frame(
        &mut BoundedStream {
            stream: &mut private,
            stop,
            deadline: Instant::now() + bounds.write,
        },
        &frame,
    )
    .is_err()
    {
        return;
    }
    let response = match transport::read_frame(&mut BoundedStream {
        stream: &mut private,
        stop,
        deadline: Instant::now() + bounds.response,
    }) {
        Ok(Some(frame)) => frame,
        _ => return,
    };
    let _ = transport::write_frame(
        &mut BoundedStream {
            stream: &mut public,
            stop,
            deadline: Instant::now() + bounds.write,
        },
        &response,
    );
}

struct Workers {
    stop: Arc<AtomicBool>,
    handles: Vec<JoinHandle<()>>,
}
impl Drop for Workers {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Release);
        for handle in self.handles.drain(..) {
            let _ = handle.join();
        }
    }
}
fn run(
    listener: UnixListener,
    upstream: PathBuf,
    config: Vec<u8>,
    stop: Arc<AtomicBool>,
    bounds: Bounds,
    signals: bool,
) -> Result<(), String> {
    listener
        .set_nonblocking(true)
        .map_err(|e| format!("cannot bound public accept: {e}"))?;
    let catalog = transport::catalog_enabled(&config)?;
    let config = Arc::new(config);
    let upstream = Arc::new(upstream);
    let mut workers = Workers {
        stop: stop.clone(),
        handles: Vec::new(),
    };
    while !stop.load(Ordering::Acquire) && !(signals && SIGNAL_STOP.load(Ordering::Relaxed)) {
        let mut index = 0;
        while index < workers.handles.len() {
            if workers.handles[index].is_finished() {
                let _ = workers.handles.swap_remove(index).join();
            } else {
                index += 1;
            }
        }
        match listener.accept() {
            Ok((mut stream, _)) => {
                let accepted = Instant::now();
                stream
                    .set_nonblocking(true)
                    .map_err(|e| format!("cannot bound public connection: {e}"))?;
                if workers.handles.len() >= bounds.connections {
                    // Tiny refusal, one nonblocking attempt: overload must not
                    // stall acceptance or delay observing SIGTERM.
                    let _ = transport::write_frame(
                        &mut stream,
                        b"\xfebusy: public ingress connection limit",
                    );
                    continue;
                }
                let (config, upstream, stop) = (config.clone(), upstream.clone(), stop.clone());
                let handle = std::thread::Builder::new()
                    .name("mini-public-client".into())
                    .stack_size(256 * 1024)
                    .spawn(move || {
                        connection(stream, &upstream, &config, catalog, &stop, bounds, accepted)
                    })
                    .map_err(|e| format!("cannot start public client reader: {e}"))?;
                workers.handles.push(handle);
            }
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(10))
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(format!("public accept failed: {e}")),
        }
    }
    // Close the listener before joining workers; the RAII guard cancels and
    // joins all of them. No detached task can retain a socket after exit.
    drop(listener);
    drop(workers);
    Ok(())
}

struct SocketGuard<'a>(&'a Path, u64, u64);
impl Drop for SocketGuard<'_> {
    fn drop(&mut self) {
        if let Ok(metadata) = fs::symlink_metadata(self.0) {
            if metadata.file_type().is_socket()
                && (metadata.dev(), metadata.ino()) == (self.1, self.2)
            {
                let _ = fs::remove_file(self.0);
            }
        }
    }
}
pub(crate) fn serve(socket: &Path, upstream: &Path, config: &Path) -> Result<(), String> {
    private_directory(socket)?;
    private_directory(upstream)?;
    let resolved = |path: &Path| -> Result<PathBuf, String> {
        Ok(
            fs::canonicalize(path.parent().ok_or("socket has no parent")?)
                .map_err(|e| e.to_string())?
                .join(path.file_name().ok_or("socket has no name")?),
        )
    };
    if resolved(socket)? == resolved(upstream)? {
        return Err("public and upstream sockets must differ".into());
    }
    let config_bytes = transport::read_config(config)?;
    transport::catalog_enabled(&config_bytes)?;
    check_upstream(upstream, &config_bytes)?;
    let stop = Arc::new(AtomicBool::new(false));
    let probe = connect(upstream, &stop, Instant::now() + BOUNDS.connect)
        .map_err(|e| format!("upstream unavailable: {e}"))?;
    if transport::peer_uid(&probe)? != transport::effective_uid() {
        return Err("upstream peer UID mismatch".into());
    }
    drop(probe);
    let _lock = transport::service_lock(&socket.with_extension("lock"))?;
    transport::pin_service_mode(
        &socket.with_extension("mode"),
        false,
        socket.with_extension("config").exists(),
    )?;
    transport::clear_stale_socket(socket)?;
    transport::pin_config(&socket.with_extension("config"), &config_bytes)?;
    let listener =
        UnixListener::bind(socket).map_err(|e| format!("cannot bind public socket: {e}"))?;
    let metadata = fs::symlink_metadata(socket).map_err(|e| e.to_string())?;
    let _socket_guard = SocketGuard(socket, metadata.dev(), metadata.ino());
    fs::set_permissions(socket, fs::Permissions::from_mode(0o600)).map_err(|e| e.to_string())?;
    let _signals = Signals::install()?;
    eprintln!(
        "mini: serving public proxy {} -> {}",
        socket.display(),
        upstream.display()
    );
    run(
        listener,
        upstream.to_path_buf(),
        config_bytes,
        stop,
        BOUNDS,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc;
    const CONFIG: &[u8] = br#"{"domain":"7"}"#;
    fn envelope(config: &[u8], request: &[u8]) -> Vec<u8> {
        let mut frame = vec![2];
        frame.extend_from_slice(&(config.len() as u32).to_le_bytes());
        frame.extend_from_slice(config);
        frame.extend_from_slice(&[0xab; 32]);
        frame.extend_from_slice(request);
        frame
    }
    fn bounds() -> Bounds {
        Bounds {
            connections: 3,
            read: Duration::from_millis(150),
            connect: Duration::from_millis(150),
            write: Duration::from_millis(150),
            response: Duration::from_millis(400),
        }
    }
    struct Fixture {
        directory: PathBuf,
        private: PathBuf,
        public: PathBuf,
        stop: Arc<AtomicBool>,
        thread: Option<JoinHandle<Result<(), String>>>,
    }
    impl Fixture {
        fn new(bounds: Bounds) -> (Self, UnixListener) {
            let directory = std::env::temp_dir().join(format!(
                "mini-ingress-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            fs::create_dir(&directory).unwrap();
            fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
            let private = directory.join("private.sock");
            let public = directory.join("public.sock");
            fs::write(private.with_extension("mode"), b"operator-v1").unwrap();
            fs::write(private.with_extension("config"), CONFIG).unwrap();
            for p in [
                private.with_extension("mode"),
                private.with_extension("config"),
            ] {
                fs::set_permissions(p, fs::Permissions::from_mode(0o600)).unwrap();
            }
            let backend = UnixListener::bind(&private).unwrap();
            backend.set_nonblocking(true).unwrap();
            fs::set_permissions(&private, fs::Permissions::from_mode(0o600)).unwrap();
            let listener = UnixListener::bind(&public).unwrap();
            let stop = Arc::new(AtomicBool::new(false));
            let (path, stopping) = (private.clone(), stop.clone());
            let thread = std::thread::spawn(move || {
                run(listener, path, CONFIG.to_vec(), stopping, bounds, false)
            });
            (
                Self {
                    directory,
                    private,
                    public,
                    stop,
                    thread: Some(thread),
                },
                backend,
            )
        }
        fn client(&self) -> UnixStream {
            let stream = UnixStream::connect(&self.public).unwrap();
            stream
                .set_read_timeout(Some(Duration::from_secs(2)))
                .unwrap();
            stream
                .set_write_timeout(Some(Duration::from_secs(2)))
                .unwrap();
            stream
        }
        fn stop(&mut self) {
            let start = Instant::now();
            self.stop.store(true, Ordering::Release);
            self.thread.take().unwrap().join().unwrap().unwrap();
            assert!(start.elapsed() < Duration::from_secs(1));
            assert!(UnixStream::connect(&self.public).is_err());
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            if self.thread.is_some() {
                self.stop();
            }
            fs::remove_dir_all(&self.directory).unwrap();
        }
    }
    fn accept(listener: &UnixListener) -> UnixStream {
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            match listener.accept() {
                Ok((stream, _)) => {
                    stream
                        .set_read_timeout(Some(Duration::from_secs(2)))
                        .unwrap();
                    return stream;
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock && Instant::now() < deadline => {
                    std::thread::sleep(Duration::from_millis(5))
                }
                Err(e) => panic!("accept: {e}"),
            }
        }
    }
    #[test]
    fn exact_frames_and_replies_pass_without_rewriting_host_pin() {
        let (fixture, backend) = Fixture::new(bounds());
        for operation in [vec![0], vec![3, 9, 8], vec![12]] {
            let frame = envelope(CONFIG, &operation);
            let mut client = fixture.client();
            transport::write_frame(&mut client, &frame).unwrap();
            let mut private = accept(&backend);
            assert_eq!(transport::read_frame(&mut private).unwrap(), Some(frame));
            transport::write_frame(&mut private, &[operation[0], 99]).unwrap();
            assert_eq!(
                transport::read_frame(&mut client).unwrap(),
                Some(vec![operation[0], 99])
            );
        }
    }
    #[test]
    fn private_ops_and_config_substitution_never_reach_backend() {
        let (fixture, backend) = Fixture::new(bounds());
        for frame in [
            envelope(CONFIG, &[22, 1]),
            envelope(CONFIG, &[152, 1]),
            envelope(b"wrong", &[0]),
            vec![3, 0, 0, 0, 0],
        ] {
            let mut client = fixture.client();
            transport::write_frame(&mut client, &frame).unwrap();
            assert_eq!(transport::read_frame(&mut client).unwrap().unwrap()[0], 254);
            assert!(matches!(
                backend.accept().unwrap_err().kind(),
                io::ErrorKind::WouldBlock
            ));
        }
    }
    #[test]
    fn changed_upstream_pin_refuses_before_forwarding() {
        let (fixture, backend) = Fixture::new(bounds());
        fs::write(fixture.private.with_extension("config"), b"{}").unwrap();
        let mut client = fixture.client();
        transport::write_frame(&mut client, &envelope(CONFIG, &[0])).unwrap();
        assert_eq!(transport::read_frame(&mut client).unwrap().unwrap()[0], 254);
        assert_eq!(
            backend.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
    }
    #[test]
    fn stop_closes_idle_and_inflight_clients_but_private_remains_usable() {
        let (mut fixture, backend) = Fixture::new(bounds());
        let mut idle = fixture.client();
        let mut inflight = fixture.client();
        transport::write_frame(&mut inflight, &envelope(CONFIG, &[0])).unwrap();
        let mut private = accept(&backend);
        assert!(transport::read_frame(&mut private).unwrap().is_some());
        fixture.stop();
        assert_eq!(transport::read_frame(&mut idle).unwrap(), None);
        assert_eq!(transport::read_frame(&mut inflight).unwrap(), None);
        assert_eq!(transport::read_frame(&mut private).unwrap(), None);
        let mut direct = UnixStream::connect(&fixture.private).unwrap();
        let mut receiver = accept(&backend);
        transport::write_frame(&mut direct, b"still-private").unwrap();
        assert_eq!(
            transport::read_frame(&mut receiver).unwrap(),
            Some(b"still-private".to_vec())
        );
    }
    #[test]
    fn connection_limit_and_whole_frame_deadline_release_capacity() {
        let (fixture, backend) = Fixture::new(Bounds {
            connections: 1,
            read: Duration::from_millis(300),
            ..bounds()
        });
        let mut idle = fixture.client();
        idle.write_all(&100u32.to_le_bytes()).unwrap();
        std::thread::sleep(Duration::from_millis(40));
        let mut excess = fixture.client();
        assert!(
            String::from_utf8_lossy(&transport::read_frame(&mut excess).unwrap().unwrap())
                .contains("connection limit")
        );
        assert_eq!(transport::read_frame(&mut idle).unwrap().unwrap()[0], 254);
        std::thread::sleep(Duration::from_millis(30));
        let mut next = fixture.client();
        transport::write_frame(&mut next, &envelope(CONFIG, &[0])).unwrap();
        let mut private = accept(&backend);
        assert!(transport::read_frame(&mut private).unwrap().is_some());
        transport::write_frame(&mut private, &[0]).unwrap();
        assert_eq!(transport::read_frame(&mut next).unwrap(), Some(vec![0]));
    }
    #[test]
    fn stalled_response_is_uncertain_and_stalled_reader_does_not_hold_stop() {
        let (mut fixture, backend) = Fixture::new(bounds());
        let mut missing = fixture.client();
        transport::write_frame(&mut missing, &envelope(CONFIG, &[0])).unwrap();
        let mut private = accept(&backend);
        transport::read_frame(&mut private).unwrap().unwrap();
        assert_eq!(
            transport::read_frame(&mut missing).unwrap(),
            None,
            "no fabricated certain refusal after forwarding"
        );
        let mut no_read = fixture.client();
        transport::write_frame(&mut no_read, &envelope(CONFIG, &[0])).unwrap();
        let mut private = accept(&backend);
        transport::read_frame(&mut private).unwrap().unwrap();
        let (sent, done) = mpsc::channel();
        let host = std::thread::spawn(move || {
            let _ = transport::write_frame(&mut private, &vec![0; 4_000_000]);
            sent.send(()).unwrap();
        });
        done.recv_timeout(Duration::from_secs(2)).unwrap();
        fixture.stop();
        host.join().unwrap();
    }
    #[test]
    fn saturated_upstream_connect_has_a_deadline() {
        let (fixture, backend) = Fixture::new(bounds());
        assert_eq!(unsafe { libc::listen(backend.as_raw_fd(), 0) }, 0);
        let _filled = UnixStream::connect(&fixture.private).unwrap();
        let start = Instant::now();
        let result = connect(
            &fixture.private,
            &AtomicBool::new(false),
            start + Duration::from_millis(100),
        );
        assert!(result.is_err());
        assert!(start.elapsed() < Duration::from_secs(1));
    }
}
