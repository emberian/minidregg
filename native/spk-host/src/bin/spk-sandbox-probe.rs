//! Sandbox-floor probe. It is placed in a test SPK image and launched as the app by
//! the resident gate; it never runs in production. It prints one JSON object per
//! check to stdout (the app's private output pipe) and a final verdict, and exits 0
//! only if every check held:
//!
//! - fd census: `/proc/self/fd` is exactly {0, 1, 2, 3}; 1 and 2 are pipes, 3 a socket,
//!   and nothing is a directory. The sandbox's pid 1 (bubblewrap init) holds no
//!   directory either.
//! - `..` walk: `openat(fd, "..")` fails for every fd 3..=64 (4/5 were the image and
//!   /var directory handles before bubblewrap consumed them).
//! - network: an AF_INET/AF_INET6 connect to a public address fails with ENETUNREACH;
//!   loopback answers (ECONNREFUSED); netlink and packet sockets are refused.
//! - nested user namespace: `unshare(CLONE_NEWUSER)`, `clone(CLONE_NEWUSER)` and
//!   `setns` are refused.
//! - seccomp, capabilities and no_new_privs as reported by `/proc/self/status`, plus
//!   one refused call from each denied family and a positive control of what a web
//!   app needs (threads, fork, a loopback listener, /var and /tmp writes).
#![cfg_attr(not(target_os = "linux"), allow(dead_code))]

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("spk-sandbox-probe is Linux-only");
    std::process::exit(2);
}

#[cfg(target_os = "linux")]
fn main() {
    let mut report = linux::Report::default();
    linux::run(&mut report);
    std::process::exit(if report.finish() { 0 } else { 1 });
}

#[cfg(target_os = "linux")]
mod linux {
    use serde_json::{json, Value};
    use std::ffi::CString;
    use std::io::{Read, Write};
    use std::net::{SocketAddr, TcpListener, TcpStream};
    use std::time::Duration;

    #[derive(Default)]
    pub struct Report {
        failures: Vec<String>,
        checks: usize,
    }

    impl Report {
        pub fn check(&mut self, name: &str, held: bool, detail: Value) {
            self.checks += 1;
            if !held {
                self.failures.push(name.to_owned());
            }
            println!("{}", json!({"check": name, "held": held, "detail": detail}));
        }

        pub fn finish(&self) -> bool {
            let held = self.failures.is_empty() && self.checks > 0;
            println!(
                "{}",
                json!({
                    "verdict": if held { "floor-held" } else { "floor-breached" },
                    "checks": self.checks,
                    "failures": self.failures,
                })
            );
            let _ = std::io::stdout().flush();
            held
        }
    }

    /// Result of one raw syscall: Ok(return value) or Err(errno).
    pub type Outcome = Result<i64, i32>;

    pub fn outcome(ret: i64) -> Outcome {
        if ret < 0 {
            Err(std::io::Error::last_os_error().raw_os_error().unwrap_or(0))
        } else {
            Ok(ret)
        }
    }

    /// A refusal holds only if the call failed with exactly the expected errno.
    pub fn refused_with(result: Outcome, errno: i32) -> bool {
        result == Err(errno)
    }

    fn describe(result: Outcome) -> Value {
        match result {
            Ok(value) => json!({"ok": value}),
            Err(errno) => json!({"errno": errno, "error": std::io::Error::from_raw_os_error(errno).to_string()}),
        }
    }

    fn close(result: Outcome) {
        if let Ok(fd) = result {
            unsafe { libc::close(fd as i32) };
        }
    }

    /// Open fds of a process: (fd, readlink target, is_directory).
    fn census(pid: &str) -> Result<Vec<(i32, String, bool)>, String> {
        let dir = format!("/proc/{pid}/fd");
        let entries = std::fs::read_dir(&dir).map_err(|e| e.to_string())?;
        // read_dir holds one fd of its own, linked to this process's fd directory.
        let own = format!("/proc/{}/fd", std::process::id());
        let mut fds = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| e.to_string())?;
            let Ok(fd) = entry.file_name().to_string_lossy().parse::<i32>() else {
                continue;
            };
            let target = std::fs::read_link(entry.path())
                .map(|p| p.to_string_lossy().into_owned())
                .unwrap_or_else(|e| format!("<{e}>"));
            let is_dir = std::fs::metadata(entry.path()).map(|m| m.is_dir()).unwrap_or(false);
            if pid == "self" && target == own {
                continue;
            }
            fds.push((fd, target, is_dir));
        }
        fds.sort();
        Ok(fds)
    }

    pub fn fd_set_is_floor(fds: &[(i32, String, bool)]) -> bool {
        let numbers: Vec<i32> = fds.iter().map(|(fd, _, _)| *fd).collect();
        numbers == [0, 1, 2, 3]
            && fds[0].1 == "/dev/null"
            && fds[1].1.starts_with("pipe:")
            && fds[2].1.starts_with("pipe:")
            && fds[3].1.starts_with("socket:")
            && fds.iter().all(|(_, _, is_dir)| !is_dir)
    }

    fn status_field(status: &str, key: &str) -> Option<String> {
        status
            .lines()
            .find_map(|line| line.strip_prefix(key)?.strip_prefix(':').map(|v| v.trim().to_owned()))
    }

    fn connect_refusal(addr: &str) -> Result<(), i32> {
        let addr: SocketAddr = addr.parse().expect("constant address");
        match TcpStream::connect_timeout(&addr, Duration::from_secs(3)) {
            Ok(_) => Ok(()),
            Err(error) => Err(error.raw_os_error().unwrap_or(-1)),
        }
    }

    pub fn run(report: &mut Report) {
        let uid = unsafe { libc::getuid() };
        let map = |name: &str| {
            std::fs::read_to_string(format!("/proc/self/{name}"))
                .map(|text| text.split_whitespace().collect::<Vec<_>>().join(" "))
                .unwrap_or_else(|e| format!("<{e}>"))
        };
        println!(
            "{}",
            json!({"probe": "spk-sandbox-probe", "uid": uid, "euid": unsafe { libc::geteuid() },
                   "pid": std::process::id(), "uid_map": map("uid_map"), "gid_map": map("gid_map")})
        );

        // --- seccomp, capabilities, no_new_privs: read before any call that could change them ---
        let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
        let fields: Vec<(&str, Option<String>)> = [
            "Seccomp", "Seccomp_filters", "NoNewPrivs", "CapInh", "CapPrm", "CapEff", "CapBnd", "CapAmb",
        ]
        .into_iter()
        .map(|key| (key, status_field(&status, key)))
        .collect();
        let get = |key: &str| fields.iter().find(|(k, _)| *k == key).and_then(|(_, v)| v.clone());
        let caps_zero = ["CapInh", "CapPrm", "CapEff", "CapBnd", "CapAmb"]
            .iter()
            .all(|key| get(key).as_deref() == Some("0000000000000000"));
        let detail: serde_json::Map<String, Value> =
            fields.iter().map(|(k, v)| (k.to_string(), json!(v))).collect();
        report.check("capabilities-all-zero", caps_zero, Value::Object(detail.clone()));
        report.check(
            "seccomp-filter-active",
            get("Seccomp").as_deref() == Some("2")
                && get("Seccomp_filters").and_then(|v| v.parse::<u32>().ok()).unwrap_or(0) >= 1,
            Value::Object(detail.clone()),
        );
        report.check("no-new-privs", get("NoNewPrivs").as_deref() == Some("1"), Value::Object(detail));

        // --- fd census ---
        match census("self") {
            Ok(fds) => {
                let held = fd_set_is_floor(&fds);
                let listed: Vec<Value> = fds
                    .iter()
                    .map(|(fd, target, dir)| json!({"fd": fd, "target": target, "directory": dir}))
                    .collect();
                report.check("fd-census-self", held, json!(listed));
            }
            Err(error) => report.check("fd-census-self", false, json!({"error": error})),
        }
        match census("1") {
            Ok(fds) => {
                let held = fds.iter().all(|(_, _, dir)| !dir);
                let listed: Vec<Value> =
                    fds.iter().map(|(fd, target, dir)| json!({"fd": fd, "target": target, "directory": dir})).collect();
                report.check("fd-census-pid1-no-directory", held, json!(listed));
            }
            // Unreadable is as good as empty for an escape; record which.
            Err(error) => report.check("fd-census-pid1-no-directory", true, json!({"unreadable": error})),
        }

        // --- `..` from every inherited descriptor ---
        let dotdot = CString::new("..").unwrap();
        let mut walked = Vec::new();
        for fd in 3..=64 {
            let result = outcome(unsafe {
                libc::openat(fd, dotdot.as_ptr(), libc::O_PATH | libc::O_DIRECTORY | libc::O_CLOEXEC)
            } as i64);
            if result.is_ok() || !matches!(result, Err(libc::EBADF) | Err(libc::ENOTDIR)) {
                walked.push(json!({"fd": fd, "result": describe(result)}));
            }
            close(result);
        }
        let fd4 = outcome(unsafe { libc::openat(4, dotdot.as_ptr(), libc::O_PATH | libc::O_DIRECTORY) } as i64);
        let fd5 = outcome(unsafe { libc::openat(5, dotdot.as_ptr(), libc::O_PATH | libc::O_DIRECTORY) } as i64);
        let held = walked.is_empty() && refused_with(fd4, libc::EBADF) && refused_with(fd5, libc::EBADF);
        close(fd4);
        close(fd5);
        report.check(
            "dotdot-from-inherited-fd",
            held,
            json!({"fd4": describe(fd4), "fd5": describe(fd5), "walked": walked}),
        );

        // --- network ---
        let v4 = connect_refusal("1.1.1.1:80");
        let v6 = connect_refusal("[2606:4700:4700::1111]:80");
        report.check(
            "network-public-connect",
            v4 == Err(libc::ENETUNREACH) && v6 == Err(libc::ENETUNREACH),
            json!({"ipv4": format!("{v4:?}"), "ipv6": format!("{v6:?}")}),
        );
        let loopback = connect_refusal("127.0.0.1:1");
        report.check(
            "network-loopback-only",
            loopback == Err(libc::ECONNREFUSED),
            json!({"127.0.0.1:1": format!("{loopback:?}")}),
        );
        for (name, family) in [("netlink", libc::AF_NETLINK), ("packet", libc::AF_PACKET), ("vsock", libc::AF_VSOCK)] {
            let result = outcome(unsafe { libc::socket(family, libc::SOCK_RAW | libc::SOCK_CLOEXEC, 0) } as i64);
            close(result);
            report.check(
                &format!("socket-{name}-refused"),
                refused_with(result, libc::EAFNOSUPPORT),
                describe(result),
            );
        }

        // Each refused call runs in a forked child: under a weaker floor some of these
        // succeed (PTRACE_TRACEME, a new mount), and the probe itself must survive to
        // report the rest.
        type Attempt = fn() -> Outcome;
        let denied: [(&str, Attempt, i32); 9] = [
            ("mount", || outcome(unsafe {
                libc::mount(c"none".as_ptr(), c"/tmp".as_ptr(), c"tmpfs".as_ptr(), 0, std::ptr::null())
            } as i64), libc::EPERM),
            ("ptrace-traceme", || outcome(unsafe { libc::ptrace(libc::PTRACE_TRACEME, 0, 0, 0) }), libc::EPERM),
            ("bpf", || outcome(unsafe { libc::syscall(libc::SYS_bpf, 0, 0, 0) }), libc::EPERM),
            ("io_uring_setup", || outcome(unsafe { libc::syscall(libc::SYS_io_uring_setup, 1, 0) }), libc::EPERM),
            ("keyctl", || outcome(unsafe { libc::syscall(libc::SYS_keyctl, 0, 0, 0) }), libc::EPERM),
            ("open_by_handle_at", || outcome(unsafe { libc::syscall(libc::SYS_open_by_handle_at, 3, 0, 0) }), libc::EPERM),
            ("personality-addr-no-randomize", || outcome(unsafe { libc::personality(0x0040000) } as i64), libc::EPERM),
            ("ioctl-tiocsti-high-word", || outcome(unsafe {
                libc::syscall(libc::SYS_ioctl, 0, (1_u64 << 32) | libc::TIOCSTI, c"x".as_ptr())
            }), libc::EPERM),
            ("unlisted-syscall", || outcome(unsafe { libc::syscall(1023) }), libc::ENOSYS),
        ];
        for (name, attempt, errno) in denied {
            let result = in_child(attempt);
            report.check(&format!("{name}-refused"), refused_with(result, errno), describe(result));
        }

        // --- positive control: what a web app resident needs still works ---
        let thread = std::thread::spawn(|| 7).join().ok() == Some(7);
        let child = unsafe { libc::fork() };
        if child == 0 {
            unsafe { libc::_exit(3) };
        }
        let mut wstatus = 0;
        let forked = child > 0
            && unsafe { libc::waitpid(child, &mut wstatus, 0) } == child
            && libc::WIFEXITED(wstatus)
            && libc::WEXITSTATUS(wstatus) == 3;
        let listener = TcpListener::bind("127.0.0.1:0");
        let loop_ok = listener.as_ref().is_ok_and(|listener| {
            let addr = listener.local_addr().unwrap();
            let mut client = TcpStream::connect(addr).unwrap();
            let (mut server, _) = listener.accept().unwrap();
            client.write_all(b"ping").unwrap();
            let mut buf = [0_u8; 4];
            server.read_exact(&mut buf).is_ok() && &buf == b"ping"
        });
        let var_ok = std::fs::write("/var/.probe", b"x").is_ok() && std::fs::remove_file("/var/.probe").is_ok();
        let tmp_ok = std::fs::write("/tmp/.probe", b"x").is_ok();
        let root_ro = std::fs::write("/.probe", b"x").is_err();
        report.check(
            "web-app-positive-control",
            thread && forked && loop_ok && var_ok && tmp_ok && root_ro,
            json!({"thread": thread, "fork": forked, "loopback-listener": loop_ok,
                   "var-write": var_ok, "tmp-write": tmp_ok, "image-root-read-only": root_ro}),
        );

        // --- nested user namespace: last, each attempt in a forked child, so a
        // successful escape (which would grant a full capability set in the new
        // namespace) cannot change what the other checks measured ---
        let unshare = in_child(|| outcome(unsafe { libc::unshare(libc::CLONE_NEWUSER) } as i64));
        report.check("userns-unshare-refused", refused_with(unshare, libc::EPERM), describe(unshare));
        let clone = in_child(|| {
            let result = outcome(unsafe {
                libc::syscall(libc::SYS_clone, (libc::CLONE_NEWUSER | libc::SIGCHLD) as u64, 0, 0, 0, 0)
            });
            match result {
                Ok(0) => unsafe { libc::_exit(0) },
                Ok(pid) => {
                    unsafe { libc::waitpid(pid as i32, std::ptr::null_mut(), 0) };
                    Ok(pid)
                }
                Err(errno) => Err(errno),
            }
        });
        report.check("userns-clone-refused", refused_with(clone, libc::EPERM), describe(clone));
        let setns = in_child(|| outcome(unsafe { libc::setns(0, libc::CLONE_NEWUSER) } as i64));
        report.check("setns-refused", refused_with(setns, libc::EPERM), describe(setns));
        let max_userns = std::fs::read_to_string("/proc/sys/user/max_user_namespaces")
            .map(|s| s.trim().to_owned())
            .unwrap_or_else(|e| format!("<{e}>"));
        println!("{}", json!({"info": "max_user_namespaces", "value": max_userns}));
    }

    /// Run `attempt` in a forked child and return its outcome through a pipe.
    fn in_child(attempt: impl FnOnce() -> Outcome) -> Outcome {
        let mut pipe = [0_i32; 2];
        if unsafe { libc::pipe2(pipe.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
            return Err(-1);
        }
        let pid = unsafe { libc::fork() };
        if pid == 0 {
            let encoded: i64 = match attempt() {
                Ok(value) => value,
                Err(errno) => -(errno as i64) - 1,
            };
            unsafe {
                libc::write(pipe[1], encoded.to_ne_bytes().as_ptr().cast(), 8);
                libc::_exit(0);
            }
        }
        unsafe { libc::close(pipe[1]) };
        let mut bytes = [0_u8; 8];
        let n = unsafe { libc::read(pipe[0], bytes.as_mut_ptr().cast(), 8) };
        unsafe {
            libc::close(pipe[0]);
            libc::waitpid(pid, std::ptr::null_mut(), 0);
        }
        if pid < 0 || n != 8 {
            return Err(-1);
        }
        match i64::from_ne_bytes(bytes) {
            value if value >= 0 => Ok(value),
            value => Err((-value - 1) as i32),
        }
    }
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::linux::*;

    fn fd(n: i32, target: &str, dir: bool) -> (i32, String, bool) {
        (n, target.into(), dir)
    }

    #[test]
    fn refusal_requires_the_exact_errno() {
        assert!(refused_with(Err(libc::EPERM), libc::EPERM));
        assert!(!refused_with(Ok(0), libc::EPERM));
        assert!(!refused_with(Ok(5), libc::EPERM));
        assert!(!refused_with(Err(libc::ENOSPC), libc::EPERM));
        assert!(!refused_with(Err(libc::ENOSYS), libc::EPERM));
    }

    #[test]
    fn fd_floor_is_exactly_stdio_pipes_and_rpc_socket() {
        let floor = [
            fd(0, "/dev/null", false),
            fd(1, "pipe:[1]", false),
            fd(2, "pipe:[1]", false),
            fd(3, "socket:[2]", false),
        ];
        assert!(fd_set_is_floor(&floor));
        let mut leaked = floor.to_vec();
        leaked.push(fd(4, "/var/lib/minidregg/spk/packages/sha256-x/root", true));
        assert!(!fd_set_is_floor(&leaked));
        let mut host_stderr = floor.to_vec();
        host_stderr[2] = fd(2, "socket:[9]", false);
        assert!(!fd_set_is_floor(&host_stderr));
        let mut dir3 = floor.to_vec();
        dir3[3] = fd(3, "/", true);
        assert!(!fd_set_is_floor(&dir3));
        assert!(!fd_set_is_floor(&floor[..3]));
    }

    #[test]
    fn a_report_with_any_failure_is_breached() {
        let mut report = Report::default();
        report.check("a", true, serde_json::json!(null));
        assert!(report.finish());
        report.check("b", false, serde_json::json!(null));
        assert!(!report.finish());
        assert!(!Report::default().finish(), "no checks is not a pass");
    }
}
