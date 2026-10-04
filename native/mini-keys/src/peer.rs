//! Who is on the other end of a connected Unix socket, as the kernel says.
use std::os::fd::AsRawFd;
use std::os::unix::net::UnixStream;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Peer {
    pub uid: u32,
    pub gid: u32,
    /// The peer's process id where the platform reports it (Linux), else -1.
    pub pid: i32,
}

/// The connected peer's credentials, captured by the kernel at connect.
#[cfg(any(target_os = "linux", target_os = "android"))]
pub fn of(stream: &UnixStream) -> Result<Peer, String> {
    let mut cred: libc::ucred = unsafe { std::mem::zeroed() };
    let mut len = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
    let rc = unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            &mut cred as *mut _ as *mut libc::c_void,
            &mut len,
        )
    };
    if rc != 0 || len as usize != std::mem::size_of::<libc::ucred>() {
        return Err("peer credentials unavailable".into());
    }
    Ok(Peer { uid: cred.uid, gid: cred.gid, pid: cred.pid })
}

/// The connected peer's credentials, captured by the kernel at connect.
#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
))]
pub fn of(stream: &UnixStream) -> Result<Peer, String> {
    let mut uid: libc::uid_t = 0;
    let mut gid: libc::gid_t = 0;
    if unsafe { libc::getpeereid(stream.as_raw_fd(), &mut uid, &mut gid) } != 0 {
        return Err("peer credentials unavailable".into());
    }
    Ok(Peer { uid, gid, pid: -1 })
}

pub fn euid() -> u32 {
    unsafe { libc::geteuid() }
}

pub fn egid() -> u32 {
    unsafe { libc::getegid() }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_socket_pair_names_this_process() {
        let (a, b) = UnixStream::pair().unwrap();
        for s in [&a, &b] {
            let peer = of(s).unwrap();
            assert_eq!(peer.uid, euid());
            assert_eq!(peer.gid, egid());
            #[cfg(target_os = "linux")]
            assert_eq!(peer.pid, std::process::id() as i32);
        }
    }
}
