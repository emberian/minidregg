//! Explicit broker transport custody. No environment-selected endpoint or fallback.
use super::*;
use minidregg_compatible_upgrade_custody as custody;
use std::os::unix::fs::FileTypeExt;

pub(super) fn resolve(root: &Path, configured: Option<&Path>) -> io::Result<PathBuf> {
    if !custody::canonical(root) {
        return Err(invalid("broker grains root must be canonical"));
    }
    let store=root.file_name().and_then(|n|n.to_str()).filter(|id|store_key(id))
        .ok_or_else(||invalid("broker endpoint requires store id in world root"))?;
    let expected=root.join(format!("runtime-{store}")).join("broker.sock");
    let socket=configured.unwrap_or(&expected);
    if socket!=expected { return Err(invalid("broker socket must be in the store-specific runtime directory")); }
    if !socket
        .as_os_str()
        .as_encoded_bytes()
        .iter()
        .all(|b| b.is_ascii_alphanumeric() || b"/_-.".contains(b))
    {
        return Err(invalid("broker socket contains unit syntax"));
    }
    if socket.as_os_str().len() >= 108 {
        return Err(invalid("broker socket exceeds Unix socket path limit"));
    }
    Ok(socket.to_owned())
}
fn socket_custody(path: &Path, uid: u32) -> io::Result<()> {
    let meta = fs::symlink_metadata(path)?;
    if !meta.file_type().is_socket() || meta.uid() != uid || meta.mode() & 0o7777 != 0o600 {
        return Err(invalid("broker socket custody refused"));
    }
    Ok(())
}
fn connect(path: &Path, uid: u32) -> io::Result<UnixStream> {
    socket_custody(path, uid)?;
    let stream = UnixStream::connect(path)?;
    if peer_credentials(&stream)?.uid != uid {
        return Err(invalid("broker peer is not the operator"));
    }
    Ok(stream)
}
fn exchange(mut stream: UnixStream, request: &Request) -> io::Result<Value> {
    stream.set_read_timeout(Some(Duration::from_secs(600)))?;
    stream.set_write_timeout(Some(Duration::from_secs(10)))?;
    let mut line = serde_json::to_vec(request)?;
    line.push(b'\n');
    stream.write_all(&line)?;
    stream.shutdown(std::net::Shutdown::Write)?;
    let mut reply = Vec::new();
    stream.take(1024 * 1024).read_to_end(&mut reply)?;
    let reply: Value =
        serde_json::from_slice(&reply).map_err(|_| invalid("mini-spk-broker reply is not JSON"))?;
    match reply.get("ok") {
        Some(Value::Bool(true)) => Ok(reply.get("result").cloned().unwrap_or(Value::Null)),
        _ => Err(invalid(format!(
            "mini-spk-broker refused: {}",
            reply
                .get("error")
                .and_then(Value::as_str)
                .unwrap_or("no reason")
        ))),
    }
}
fn selected_call(root: &Path, path: &Path, request: &Request, uid: u32) -> io::Result<Value> {
    // Connect both channels first and bind them to the same process. A replaced
    // socket between identity and action cannot redirect the mutation elsewhere.
    let identity = connect(path, uid)?;
    let action = connect(path, uid)?;
    if peer_credentials(&identity)?.pid != peer_credentials(&action)?.pid {
        return Err(invalid(
            "broker changed between identity and action connections",
        ));
    }
    let value = exchange(identity, &Request::Identify {})?;
    if value.get("protocol").and_then(Value::as_str) != Some("mini-spk-broker-identity-v1")
        || value.get("grainsRoot").and_then(Value::as_str) != root.to_str()
        || value.get("brokerSocket").and_then(Value::as_str) != path.to_str()
    {
        return Err(invalid(
            "selected broker identity differs from pinned installation",
        ));
    }
    exchange(action, request)
}
pub(super) fn call_at(root: &Path, socket: Option<&Path>, request: &Request) -> io::Result<Value> {
    let path = resolve(root, socket)?;
    protected_chain(root)?;
    protected_chain(path.parent().ok_or_else(||invalid("broker runtime parent"))?)?;
    let uid=unsafe{libc::geteuid()};
    let parent=fs::symlink_metadata(path.parent().unwrap())?;
    if !parent.is_dir() || parent.uid()!=uid || parent.mode()&0o7777!=0o700 { return Err(invalid("broker runtime directory custody refused")); }
    selected_call(root,&path,request,uid)
}
fn protected_chain(path: &Path)->io::Result<()> {
    for ancestor in path.ancestors() {
        let meta=fs::symlink_metadata(ancestor)?;
        if !meta.is_dir() || meta.file_type().is_symlink() || meta.mode()&0o022!=0
            || (!crate::namespace_identity::root_owned(ancestor,&meta) && meta.uid()!=unsafe{libc::geteuid()}) {
            return Err(invalid("broker endpoint ancestor custody refused"));
        }
    }
    Ok(())
}

/// An operator-private lifetime lock serializes restart/stale socket recovery. Even a
/// pre-lock legacy broker is detected by a successful connection and not unlinked.
pub(super) fn bind(path: &Path, gid: u32) -> io::Result<(UnixListener, File)> {
    protected_chain(path.parent().ok_or_else(||invalid("runtime parent"))?)?;
    bind_owned(path, gid, unsafe{libc::geteuid()})
}
fn bind_owned(path: &Path, gid: u32, owner: u32) -> io::Result<(UnixListener, File)> {
    let lock_path = path.with_extension("sock.lock");
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(&lock_path)?;
    let meta = lock.metadata()?;
    if !meta.is_file() || meta.uid() != owner || meta.nlink() != 1 || meta.mode() & 0o7777 != 0o600
    {
        return Err(invalid("broker socket lifetime lock custody refused"));
    }
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err(invalid("broker socket is already held"));
    }
    match fs::symlink_metadata(path) {
        Ok(_) => {
            socket_custody(path, owner)?;
            match UnixStream::connect(path) {
                Ok(_) => return Err(invalid("broker socket is occupied; refusing to unlink it")),
                Err(error) if error.kind() == io::ErrorKind::ConnectionRefused => {
                    fs::remove_file(path)?
                }
                Err(error) => return Err(error),
            }
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    let listener = UnixListener::bind(path)?;
    let meta=fs::symlink_metadata(path)?;
    if meta.uid()!=owner || meta.gid()!=gid { return Err(invalid("operator socket ownership differs")); }
    fs::set_permissions(path, fs::Permissions::from_mode(0o600))?;
    Ok((listener, lock))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    struct Fixture(PathBuf);
    impl Fixture {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "spk-endpoint-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::SeqCst)
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
        fn socket(&self, name: &str) -> (PathBuf, UnixListener) {
            let path = self.0.join(name);
            let listener = UnixListener::bind(&path).unwrap();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
            (path, listener)
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    fn reply(stream: &mut UnixStream, value: Value) {
        stream
            .write_all(
                serde_json::to_string(&json!({"ok":true,"result":value}))
                    .unwrap()
                    .as_bytes(),
            )
            .unwrap();
    }
    fn read_request(stream: &UnixStream) -> Vec<u8> {
        let mut bytes = Vec::new();
        stream
            .set_read_timeout(Some(Duration::from_secs(2)))
            .unwrap();
        BufReader::new(stream)
            .read_until(b'\n', &mut bytes)
            .unwrap();
        bytes
    }
    #[test]
    fn selected_endpoint_receives_action_and_other_endpoint_remains_untouched() {
        let fixture = Fixture::new();
        let (selected, listener) = fixture.socket("broker.sock");
        let (_, other) = fixture.socket("other.sock");
        other.set_nonblocking(true).unwrap();
        let root = fixture.0.clone();
        let path = selected.clone();
        let server = std::thread::spawn(move || {
            let (mut first, _) = listener.accept().unwrap();
            assert!(matches!(
                serde_json::from_slice::<Request>(&read_request(&first)).unwrap(),
                Request::Identify {}
            ));
            reply(
                &mut first,
                json!({"protocol":"mini-spk-broker-identity-v1","grainsRoot":root,"brokerSocket":path}),
            );
            drop(first);
            let (mut second, _) = listener.accept().unwrap();
            assert!(
                matches!(serde_json::from_slice::<Request>(&read_request(&second)).unwrap(), Request::InitStore{store} if store=="0123456789abcdef")
            );
            reply(&mut second, json!({"selected":true}));
        });
        assert_eq!(
            selected_call(
                &fixture.0,
                &selected,
                &Request::InitStore {
                    store: "0123456789abcdef".into()
                },
                unsafe { libc::geteuid() }
            )
            .unwrap(),
            json!({"selected":true})
        );
        server.join().unwrap();
        assert_eq!(
            other.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
    }
    #[test]
    fn mismatched_installation_never_sends_mutating_request() {
        let fixture = Fixture::new();
        let (selected, listener) = fixture.socket("broker.sock");
        let path = selected.clone();
        let server = std::thread::spawn(move || {
            let (mut first, _) = listener.accept().unwrap();
            read_request(&first);
            reply(
                &mut first,
                json!({"protocol":"mini-spk-broker-identity-v1","grainsRoot":"/different","brokerSocket":path}),
            );
            drop(first);
            let (second, _) = listener.accept().unwrap();
            assert!(read_request(&second).is_empty());
        });
        assert!(
            selected_call(&fixture.0, &selected, &Request::Backup {}, unsafe {
                libc::geteuid()
            })
            .is_err()
        );
        server.join().unwrap();
    }
    #[test]
    fn occupied_or_locked_socket_is_preserved_and_stale_socket_can_restart() {
        let fixture = Fixture::new();
        let (path, active) = fixture.socket("broker.sock");
        let uid = unsafe { libc::geteuid() };
        let gid = unsafe { libc::getegid() };
        let before = fs::symlink_metadata(&path).unwrap().ino();
        assert!(bind_owned(&path, gid, uid).is_err());
        assert_eq!(fs::symlink_metadata(&path).unwrap().ino(), before);
        drop(active);
        let (restarted, lock) = bind_owned(&path, gid, uid).unwrap();
        assert!(bind_owned(&path, gid, uid).is_err());
        drop(restarted);
        // Retaining the process lock refuses even a now-stale socket.
        assert!(bind_owned(&path, gid, uid).is_err());
        drop(lock);
        let (_again, _lock) = bind_owned(&path, gid, uid).unwrap();
        let file = fixture.0.join("file.sock");
        fs::write(&file, b"retained").unwrap();
        assert!(bind_owned(&file, gid, uid).is_err());
        assert_eq!(fs::read(&file).unwrap(), b"retained");
    }
    #[test]
    fn endpoint_paths_and_custody_fail_closed_without_fallback() {
        let root = Path::new("/var/lib/mini-spk-worlds/0123456789abcdef");
        let expected=root.join("runtime-0123456789abcdef/broker.sock");
        assert_eq!(resolve(root,None).unwrap(),expected);
        assert_eq!(resolve(root,Some(&expected)).unwrap(),expected);
        for bad in ["/run/mini-spk-broker.sock","/var/lib/mini-spk-worlds/fedcba9876543210/runtime-fedcba9876543210/broker.sock","/var/lib/mini-spk-worlds/0123456789abcdef/broker.sock"] {
            assert!(resolve(root,Some(Path::new(bad))).is_err());
        }
        assert!(resolve(Path::new("/var/lib/grains"),None).is_err());
        let fixture = Fixture::new();
        let (socket, _listener) = fixture.socket("broker.sock");
        let uid = unsafe { libc::geteuid() };
        assert!(connect(&socket, uid.wrapping_add(1)).is_err());
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o666)).unwrap();
        assert!(connect(&socket, uid).is_err());
        assert!(selected_call(
            &fixture.0,
            &fixture.0.join("missing.sock"),
            &Request::Backup {},
            uid
        )
        .is_err());
    }
}
