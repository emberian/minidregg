//! Where a route's `http.sock` is bound, connected to and published.
//!
//! A route directory is `<state>/apps/<app>/routes/<name>`. Its socket is
//! `<directory>/http.sock` whenever that path fits `sun_path`; the kernel refuses to
//! bind or connect a longer one. A member-namespace app id is up to 20 digits and a route
//! name up to 32 bytes, under a world root that already spends 58 bytes on the store tag
//! twice, so the direct path routinely does not fit. The route then has one bounded name,
//! `<state>/rt/<digest>/http.sock`, where `<state>/rt/<digest>` is a symlink to the route
//! directory: the socket file is created in the real directory (every identity and custody
//! check still reads it there) and every client, the browser proxy, the edge and the apps
//! worker, names it through the alias. The alias is a pure function of the directory path,
//! so the route verb, the resident and the proxy compute the same name without recording it.

use sha2::{Digest, Sha256};
use std::fs;
use std::io;
use std::os::unix::fs::{DirBuilderExt, MetadataExt};
use std::path::{Path, PathBuf};

const SOCKET: &str = "http.sock";
const ALIAS_ROOT: &str = "rt";

fn refuse(message: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

/// Bytes a `sun_path` holds, one of which is the terminating NUL.
fn sun_path_limit() -> usize {
    let address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    address.sun_path.len()
}

fn fits(path: &Path) -> bool {
    use std::os::unix::ffi::OsStrExt;
    path.as_os_str().as_bytes().len() < sun_path_limit()
}

fn named<'a>(path: Option<&'a Path>, name: &str) -> Option<&'a Path> {
    path.filter(|p| p.file_name().is_some_and(|n| n == name))
}

/// `<state>/rt/<digest>`, the alias of `directory`, and the state root beside which it lives.
fn alias_paths(directory: &Path) -> io::Result<(PathBuf, PathBuf)> {
    use std::os::unix::ffi::OsStrExt;
    let state = named(directory.parent(), "routes")
        .and_then(Path::parent)
        .and_then(Path::parent)
        .and_then(|apps| named(Some(apps), "apps"))
        .and_then(Path::parent)
        .ok_or_else(|| refuse(format!(
            "route socket path {} exceeds sun_path ({} bytes) and the route directory is not <state>/apps/<app>/routes/<name>, so it has no shorter alias",
            directory.join(SOCKET).display(), sun_path_limit() - 1)))?;
    let mut hash = Sha256::new();
    hash.update(b"mini-spk-route-socket-alias-v1\0");
    hash.update(directory.as_os_str().as_bytes());
    let digest = hash.finalize();
    let tag: String = digest.iter().take(8).map(|b| format!("{b:02x}")).collect();
    let root = state.join(ALIAS_ROOT);
    Ok((root.join(tag), state.to_path_buf()))
}

/// The socket path of the route in `directory`, without touching the filesystem.
pub fn route_socket(directory: &Path) -> io::Result<PathBuf> {
    let direct = directory.join(SOCKET);
    if fits(&direct) {
        return Ok(direct);
    }
    let (alias, _) = alias_paths(directory)?;
    let through = alias.join(SOCKET);
    if !fits(&through) {
        return Err(refuse(format!(
            "route socket path {} exceeds sun_path ({} bytes) and so does its alias {}; shorten the state root",
            direct.display(), sun_path_limit() - 1, through.display())));
    }
    Ok(through)
}

/// `route_socket`, with the alias in place for a route whose direct path does not fit.
/// An alias that names anything but this directory is refused, never replaced.
pub fn ensure_route_socket(directory: &Path) -> io::Result<PathBuf> {
    let socket = route_socket(directory)?;
    if socket == directory.join(SOCKET) {
        return Ok(socket);
    }
    let (alias, state) = alias_paths(directory)?;
    let root = state.join(ALIAS_ROOT);
    match fs::DirBuilder::new().mode(0o700).create(&root) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }
    let meta = fs::symlink_metadata(&root)?;
    if !meta.is_dir() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o777 != 0o700 {
        return Err(refuse(format!("route alias directory {} is not this operator's private directory", root.display())));
    }
    match std::os::unix::fs::symlink(directory, &alias) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }
    let meta = fs::symlink_metadata(&alias)?;
    if !meta.file_type().is_symlink() || fs::read_link(&alias)? != directory {
        return Err(refuse(format!("route alias {} names another directory", alias.display())));
    }
    Ok(socket)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::FileTypeExt;
    use std::os::unix::net::{UnixListener, UnixStream};

    fn scratch(tag: &str) -> PathBuf {
        // Padded so the long route below exceeds sun_path on Linux (108) and macOS (104).
        let base = PathBuf::from(format!("/tmp/rs-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&base);
        let state = base.join("w".repeat(30));
        fs::create_dir_all(&state).unwrap();
        state
    }

    fn long_route(state: &Path) -> PathBuf {
        let directory = state.join("apps").join("12199742976484049994").join("routes")
            .join("member-an-unreasonably-long-member");
        fs::create_dir_all(&directory).unwrap();
        directory
    }

    #[test]
    fn a_path_that_fits_is_the_direct_socket_and_creates_nothing() {
        let state = scratch("direct");
        let directory = state.join("apps").join("7").join("routes").join("owner");
        fs::create_dir_all(&directory).unwrap();
        assert_eq!(ensure_route_socket(&directory).unwrap(), directory.join("http.sock"));
        assert!(!state.join("rt").exists());
        fs::remove_dir_all(state.parent().unwrap()).unwrap();
    }

    #[test]
    fn a_path_over_sun_path_binds_and_connects_through_one_bounded_alias() {
        let state = scratch("long");
        let directory = long_route(&state);
        assert!(!fits(&directory.join("http.sock")), "fixture must exceed sun_path");
        let socket = ensure_route_socket(&directory).unwrap();
        assert!(fits(&socket));
        assert_eq!(socket, route_socket(&directory).unwrap());
        assert_eq!(ensure_route_socket(&directory).unwrap(), socket, "idempotent");
        let listener = UnixListener::bind(&socket).unwrap();
        assert!(fs::symlink_metadata(directory.join("http.sock")).unwrap().file_type().is_socket());
        let client = std::thread::spawn({ let socket = socket.clone(); move || UnixStream::connect(socket).is_ok() });
        listener.accept().unwrap();
        assert!(client.join().unwrap());
        fs::remove_dir_all(state.parent().unwrap()).unwrap();
    }

    #[test]
    fn an_alias_naming_another_directory_is_refused_not_replaced() {
        let state = scratch("clash");
        let directory = long_route(&state);
        let socket = ensure_route_socket(&directory).unwrap();
        let alias = socket.parent().unwrap().to_path_buf();
        fs::remove_file(&alias).unwrap();
        std::os::unix::fs::symlink(state.join("apps"), &alias).unwrap();
        let error = ensure_route_socket(&directory).unwrap_err();
        assert!(error.to_string().contains("names another directory"), "{error}");
        fs::remove_dir_all(state.parent().unwrap()).unwrap();
    }

    #[test]
    fn a_long_directory_outside_the_route_layout_names_its_clause() {
        let state = scratch("layout");
        let directory = state.join("x".repeat(sun_path_limit()));
        let error = route_socket(&directory).unwrap_err();
        assert!(error.to_string().contains("exceeds sun_path") && error.to_string().contains("no shorter alias"), "{error}");
        fs::remove_dir_all(state.parent().unwrap()).ok();
    }
}
