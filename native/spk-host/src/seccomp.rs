//! Compile the operator-readable resident seccomp policy into a classic-BPF program for
//! bubblewrap's `--seccomp FD`. The policy text is `native/spk-host/seccomp/resident-web.policy`;
//! its header documents the grammar and the program shape.

use std::collections::BTreeSet;
use std::io;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};

/// The one policy every resident app runs under. Embedded so the launched filter is exactly
/// the reviewed file at the built commit.
pub const RESIDENT_WEB_POLICY: &str = include_str!("../seccomp/resident-web.policy");

const SECCOMP_RET_KILL_PROCESS: u32 = 0x8000_0000;
const SECCOMP_RET_ERRNO: u32 = 0x0005_0000;
const SECCOMP_RET_ALLOW: u32 = 0x7fff_0000;

const BPF_LD_W_ABS: u16 = 0x20;
const BPF_JMP_JEQ_K: u16 = 0x15;
const BPF_JMP_JGE_K: u16 = 0x35;
const BPF_JMP_JSET_K: u16 = 0x45;
const BPF_RET_K: u16 = 0x06;

/// `struct seccomp_data` offsets: nr, arch, then u64 args from byte 16. Little-endian only.
const OFFSET_NR: u32 = 0;
const OFFSET_ARCH: u32 = 4;
const fn offset_arg_low(index: u8) -> u32 {
    16 + 8 * index as u32
}

#[cfg(target_arch = "x86_64")]
const AUDIT_ARCH: u32 = 0xc000_003e;
#[cfg(target_arch = "aarch64")]
const AUDIT_ARCH: u32 = 0xc000_00b7;
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
compile_error!("spk-host seccomp tables exist only for x86_64 and aarch64");
#[cfg(target_endian = "big")]
compile_error!("spk-host seccomp argument offsets assume little-endian seccomp_data");

const X32_SYSCALL_BIT: u32 = 0x4000_0000;
/// Kernel limit on one filter program (BPF_MAXINSNS).
const MAX_INSNS: usize = 4096;

macro_rules! table {
    ($($name:ident),* $(,)?) => {
        &[$((stringify!($name), libc::$name as u32)),*]
    };
}

/// Syscalls present on both supported architectures.
const COMMON: &[(&str, u32)] = table![
    SYS_brk, SYS_mmap, SYS_munmap, SYS_mremap, SYS_mprotect, SYS_madvise, SYS_msync, SYS_mincore,
    SYS_mlock, SYS_mlock2, SYS_munlock, SYS_mlockall, SYS_munlockall, SYS_get_mempolicy,
    SYS_set_mempolicy, SYS_mbind, SYS_membarrier, SYS_rseq, SYS_set_tid_address,
    SYS_set_robust_list, SYS_get_robust_list, SYS_futex, SYS_futex_waitv, SYS_prctl, SYS_exit,
    SYS_exit_group, SYS_execve, SYS_execveat, SYS_wait4, SYS_waitid, SYS_clone, SYS_clone3,
    SYS_getpid, SYS_getppid, SYS_gettid, SYS_getpgid, SYS_getsid, SYS_setsid, SYS_setpgid,
    SYS_getuid, SYS_geteuid, SYS_getgid, SYS_getegid, SYS_getresuid, SYS_getresgid,
    SYS_getgroups, SYS_setuid, SYS_setgid, SYS_setreuid, SYS_setregid, SYS_setresuid,
    SYS_setresgid, SYS_setgroups, SYS_setfsuid, SYS_setfsgid, SYS_capget, SYS_capset,
    SYS_getrlimit, SYS_setrlimit, SYS_prlimit64, SYS_getrusage, SYS_getpriority, SYS_setpriority,
    SYS_sched_yield, SYS_sched_getaffinity, SYS_sched_setaffinity, SYS_sched_getparam,
    SYS_sched_setparam, SYS_sched_getscheduler, SYS_sched_setscheduler,
    SYS_sched_get_priority_max, SYS_sched_get_priority_min, SYS_sched_rr_get_interval,
    SYS_sched_getattr, SYS_sched_setattr, SYS_getcpu, SYS_ioprio_get, SYS_ioprio_set,
    SYS_pkey_alloc, SYS_pkey_free, SYS_pkey_mprotect, SYS_uname, SYS_sysinfo, SYS_umask,
    SYS_times, SYS_personality, SYS_seccomp, SYS_rt_sigaction, SYS_rt_sigprocmask,
    SYS_rt_sigreturn, SYS_rt_sigpending, SYS_rt_sigtimedwait, SYS_rt_sigqueueinfo,
    SYS_rt_tgsigqueueinfo, SYS_rt_sigsuspend, SYS_sigaltstack, SYS_kill, SYS_tkill, SYS_tgkill,
    SYS_pidfd_open, SYS_pidfd_send_signal, SYS_restart_syscall, SYS_nanosleep,
    SYS_clock_nanosleep, SYS_clock_gettime, SYS_clock_getres, SYS_gettimeofday, SYS_getitimer,
    SYS_setitimer, SYS_timer_create, SYS_timer_settime, SYS_timer_gettime, SYS_timer_getoverrun,
    SYS_timer_delete, SYS_timerfd_create, SYS_timerfd_settime, SYS_timerfd_gettime,
    SYS_signalfd4, SYS_eventfd2, SYS_read, SYS_write, SYS_readv, SYS_writev, SYS_pread64,
    SYS_pwrite64, SYS_preadv, SYS_pwritev, SYS_preadv2, SYS_pwritev2, SYS_lseek, SYS_openat,
    SYS_openat2, SYS_close, SYS_close_range, SYS_dup, SYS_dup3, SYS_pipe2, SYS_fcntl, SYS_flock,
    SYS_fsync, SYS_fdatasync, SYS_sync, SYS_syncfs, SYS_sync_file_range, SYS_fstat,
    SYS_newfstatat, SYS_statx, SYS_statfs, SYS_fstatfs, SYS_faccessat, SYS_faccessat2,
    SYS_readlinkat, SYS_getdents64, SYS_getcwd, SYS_chdir, SYS_fchdir, SYS_renameat,
    SYS_renameat2, SYS_mkdirat, SYS_linkat, SYS_unlinkat, SYS_symlinkat, SYS_mknodat,
    SYS_fchmod, SYS_fchmodat, SYS_fchmodat2, SYS_fchown, SYS_fchownat, SYS_truncate,
    SYS_ftruncate, SYS_fallocate, SYS_fadvise64, SYS_readahead, SYS_utimensat, SYS_getxattr,
    SYS_lgetxattr, SYS_fgetxattr, SYS_listxattr, SYS_llistxattr, SYS_flistxattr, SYS_setxattr,
    SYS_lsetxattr, SYS_fsetxattr, SYS_removexattr, SYS_lremovexattr, SYS_fremovexattr,
    SYS_sendfile, SYS_copy_file_range, SYS_splice, SYS_tee, SYS_vmsplice, SYS_memfd_create,
    SYS_inotify_init1, SYS_inotify_add_watch, SYS_inotify_rm_watch, SYS_ppoll, SYS_pselect6,
    SYS_epoll_create1, SYS_epoll_ctl, SYS_epoll_pwait, SYS_epoll_pwait2, SYS_io_setup,
    SYS_io_destroy, SYS_io_submit, SYS_io_cancel, SYS_io_getevents,
    SYS_getrandom, SYS_ioctl, SYS_socket, SYS_socketpair, SYS_bind, SYS_listen, SYS_accept,
    SYS_accept4, SYS_connect, SYS_getsockname, SYS_getpeername, SYS_sendto, SYS_recvfrom,
    SYS_sendmsg, SYS_recvmsg, SYS_sendmmsg, SYS_recvmmsg, SYS_shutdown, SYS_setsockopt,
    SYS_getsockopt, SYS_shmget, SYS_shmat, SYS_shmdt, SYS_shmctl, SYS_semget, SYS_semop,
    SYS_semtimedop, SYS_semctl, SYS_msgget, SYS_msgsnd, SYS_msgrcv, SYS_msgctl, SYS_mq_open,
    SYS_mq_unlink, SYS_mq_timedsend, SYS_mq_timedreceive, SYS_mq_notify, SYS_mq_getsetattr,
    SYS_unshare, SYS_setns, SYS_mount, SYS_umount2, SYS_pivot_root, SYS_chroot, SYS_move_mount,
    SYS_open_tree, SYS_fsopen, SYS_fsconfig, SYS_fsmount, SYS_fspick, SYS_mount_setattr,
    SYS_ptrace, SYS_process_vm_readv, SYS_process_vm_writev, SYS_pidfd_getfd, SYS_kcmp,
    SYS_process_madvise, SYS_bpf, SYS_perf_event_open, SYS_userfaultfd, SYS_keyctl,
    SYS_add_key, SYS_request_key, SYS_io_uring_setup, SYS_io_uring_enter, SYS_io_uring_register,
    SYS_open_by_handle_at, SYS_name_to_handle_at, SYS_fanotify_init, SYS_fanotify_mark,
    SYS_landlock_create_ruleset, SYS_landlock_add_rule, SYS_landlock_restrict_self,
    SYS_init_module, SYS_finit_module, SYS_delete_module, SYS_kexec_load, SYS_kexec_file_load,
    SYS_reboot, SYS_swapon, SYS_swapoff, SYS_acct, SYS_quotactl, SYS_quotactl_fd, SYS_syslog,
    SYS_vhangup, SYS_settimeofday, SYS_clock_settime, SYS_clock_adjtime, SYS_adjtimex,
    SYS_sethostname, SYS_setdomainname, SYS_memfd_secret, SYS_migrate_pages, SYS_move_pages,
];

/// Legacy entry points that exist on x86_64 and not on aarch64 (asm-generic dropped them).
const X86_64_ONLY_NAMES: &[&str] = &[
    "arch_prctl", "fork", "vfork", "getpgrp", "time", "pause", "alarm", "signalfd", "eventfd",
    "open", "creat", "dup2", "pipe", "stat", "lstat", "access", "readlink", "getdents", "rename",
    "mkdir", "rmdir", "link", "unlink", "symlink", "mknod", "chmod", "chown", "lchown", "utime",
    "utimes", "futimesat", "inotify_init", "poll", "select", "epoll_create", "epoll_wait", "iopl",
    "ioperm", "modify_ldt", "uselib",
];

#[cfg(target_arch = "x86_64")]
const ARCH_ONLY: &[(&str, u32)] = table![
    SYS_arch_prctl, SYS_fork, SYS_vfork, SYS_getpgrp, SYS_time, SYS_pause, SYS_alarm,
    SYS_signalfd, SYS_eventfd, SYS_open, SYS_creat, SYS_dup2, SYS_pipe, SYS_stat, SYS_lstat,
    SYS_access, SYS_readlink, SYS_getdents, SYS_rename, SYS_mkdir, SYS_rmdir, SYS_link,
    SYS_unlink, SYS_symlink, SYS_mknod, SYS_chmod, SYS_chown, SYS_lchown, SYS_utime, SYS_utimes,
    SYS_futimesat, SYS_inotify_init, SYS_poll, SYS_select, SYS_epoll_create, SYS_epoll_wait,
    SYS_iopl, SYS_ioperm, SYS_modify_ldt, SYS_uselib,
];
#[cfg(target_arch = "aarch64")]
const ARCH_ONLY: &[(&str, u32)] = &[];

fn invalid(message: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

enum Lookup {
    Present(u32),
    /// Named by the policy, legitimately absent on this architecture.
    Absent,
}

fn lookup(name: &str) -> io::Result<Lookup> {
    let found = COMMON
        .iter()
        .chain(ARCH_ONLY)
        .find(|(symbol, _)| symbol.strip_prefix("SYS_") == Some(name));
    match found {
        Some((_, number)) => Ok(Lookup::Present(*number)),
        None if X86_64_ONLY_NAMES.contains(&name) => Ok(Lookup::Absent),
        None => Err(invalid(format!("seccomp policy names unknown syscall {name}"))),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArgTest {
    In,
    NotIn,
    Clear,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Action {
    Allow,
    Deny(u32),
    AllowArg {
        arg: u8,
        test: ArgTest,
        values: Vec<u32>,
        otherwise: u32,
    },
}

/// A parsed policy: ordered (syscall number, action) rules and the default errno.
#[derive(Debug)]
pub struct Policy {
    rules: Vec<(u32, Action)>,
    default_errno: u32,
}

fn errno(word: &str) -> io::Result<u32> {
    match word {
        "EPERM" => Ok(libc::EPERM as u32),
        "ENOSYS" => Ok(libc::ENOSYS as u32),
        "EAFNOSUPPORT" => Ok(libc::EAFNOSUPPORT as u32),
        other => Err(invalid(format!("seccomp policy errno {other} is not allowed"))),
    }
}

fn number(word: &str) -> io::Result<u32> {
    let parsed = match word.strip_prefix("0x") {
        Some(hex) => u32::from_str_radix(hex, 16),
        None => word.parse(),
    };
    parsed.map_err(|_| invalid(format!("seccomp policy value {word} is not a u32")))
}

impl Policy {
    pub fn parse(text: &str) -> io::Result<Self> {
        let mut rules = Vec::new();
        let mut default_errno = None;
        let mut named = BTreeSet::new();
        let mut push = |name: &str, action: Action, rules: &mut Vec<(u32, Action)>| {
            if !named.insert(name.to_owned()) {
                return Err(invalid(format!("seccomp policy names {name} twice")));
            }
            if let Lookup::Present(nr) = lookup(name)? {
                rules.push((nr, action));
            }
            Ok(())
        };
        for (index, raw) in text.lines().enumerate() {
            let line = raw.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            let words: Vec<&str> = line.split_whitespace().collect();
            let bad = || invalid(format!("seccomp policy line {} malformed: {raw}", index + 1));
            match words.as_slice() {
                ["default", code] => {
                    if default_errno.replace(errno(code)?).is_some() {
                        return Err(bad());
                    }
                }
                ["allow", names @ ..] if !names.is_empty() => {
                    for name in names {
                        push(name, Action::Allow, &mut rules)?;
                    }
                }
                ["deny", code, names @ ..] if !names.is_empty() => {
                    let code = errno(code)?;
                    for name in names {
                        push(name, Action::Deny(code), &mut rules)?;
                    }
                }
                ["allow-arg", name, arg, test, rest @ ..] => {
                    let arg: u8 = arg.parse().map_err(|_| bad())?;
                    let test = match *test {
                        "in" => ArgTest::In,
                        "notin" => ArgTest::NotIn,
                        "clear" => ArgTest::Clear,
                        _ => return Err(bad()),
                    };
                    let [values @ .., "else", code] = rest else {
                        return Err(bad());
                    };
                    if arg > 5
                        || values.is_empty()
                        || values.len() > 16
                        || (test == ArgTest::Clear && values.len() != 1)
                    {
                        return Err(bad());
                    }
                    let values = values.iter().map(|v| number(v)).collect::<io::Result<_>>()?;
                    let action = Action::AllowArg { arg, test, values, otherwise: errno(code)? };
                    push(name, action, &mut rules)?;
                }
                _ => return Err(bad()),
            }
        }
        let default_errno =
            default_errno.ok_or_else(|| invalid("seccomp policy has no default".into()))?;
        Ok(Self { rules, default_errno })
    }

    /// The classic-BPF program, one `struct sock_filter` (8 bytes, native endian) per
    /// instruction, as bubblewrap's `--seccomp` reads it.
    pub fn compile(&self) -> io::Result<Vec<u8>> {
        let mut program = Program::default();
        program.load(OFFSET_ARCH);
        program.jump(BPF_JMP_JEQ_K, AUDIT_ARCH, 1, 0);
        program.ret(SECCOMP_RET_KILL_PROCESS);
        program.load(OFFSET_NR);
        if cfg!(target_arch = "x86_64") {
            program.jump(BPF_JMP_JGE_K, X32_SYSCALL_BIT, 0, 1);
            program.ret(SECCOMP_RET_ERRNO | libc::EPERM as u32);
        }
        for (nr, action) in &self.rules {
            match action {
                Action::Allow => {
                    program.jump(BPF_JMP_JEQ_K, *nr, 0, 1);
                    program.ret(SECCOMP_RET_ALLOW);
                }
                Action::Deny(code) => {
                    program.jump(BPF_JMP_JEQ_K, *nr, 0, 1);
                    program.ret(SECCOMP_RET_ERRNO | code);
                }
                Action::AllowArg { arg, test, values, otherwise } => {
                    // Every path through the block ends in RET, so the clobbered
                    // accumulator never reaches the next rule.
                    let block = 1 + values.len() + 2;
                    program.jump(BPF_JMP_JEQ_K, *nr, 0, u8::try_from(block).expect("<=16"));
                    program.load(offset_arg_low(*arg));
                    let refuse = SECCOMP_RET_ERRNO | otherwise;
                    match test {
                        ArgTest::In => {
                            // Match i jumps over the remaining matches and the refusal.
                            for (i, value) in values.iter().enumerate() {
                                let to_allow = (values.len() - i) as u8;
                                program.jump(BPF_JMP_JEQ_K, *value, to_allow, 0);
                            }
                            program.ret(refuse);
                            program.ret(SECCOMP_RET_ALLOW);
                        }
                        ArgTest::NotIn => {
                            for (i, value) in values.iter().enumerate() {
                                let to_refuse = (values.len() - 1 - i) as u8 + 1;
                                program.jump(BPF_JMP_JEQ_K, *value, to_refuse, 0);
                            }
                            program.ret(SECCOMP_RET_ALLOW);
                            program.ret(refuse);
                        }
                        ArgTest::Clear => {
                            program.jump(BPF_JMP_JSET_K, values[0], 0, 1);
                            program.ret(refuse);
                            program.ret(SECCOMP_RET_ALLOW);
                        }
                    }
                }
            }
        }
        program.ret(SECCOMP_RET_ERRNO | self.default_errno);
        if program.0.len() > MAX_INSNS {
            return Err(invalid("seccomp program exceeds BPF_MAXINSNS".into()));
        }
        Ok(program.0.iter().flat_map(|insn| insn.bytes()).collect())
    }
}

#[derive(Clone, Copy)]
struct Insn {
    code: u16,
    jt: u8,
    jf: u8,
    k: u32,
}

impl Insn {
    fn bytes(&self) -> [u8; 8] {
        let mut out = [0; 8];
        out[0..2].copy_from_slice(&self.code.to_ne_bytes());
        out[2] = self.jt;
        out[3] = self.jf;
        out[4..8].copy_from_slice(&self.k.to_ne_bytes());
        out
    }
}

#[derive(Default)]
struct Program(Vec<Insn>);

impl Program {
    fn load(&mut self, offset: u32) {
        self.0.push(Insn { code: BPF_LD_W_ABS, jt: 0, jf: 0, k: offset });
    }
    fn jump(&mut self, code: u16, k: u32, jt: u8, jf: u8) {
        self.0.push(Insn { code, jt, jf, k });
    }
    fn ret(&mut self, k: u32) {
        self.0.push(Insn { code: BPF_RET_K, jt: 0, jf: 0, k });
    }
}

/// The compiled resident program in a sealed, close-on-exec memfd positioned at offset 0.
/// bubblewrap reads it to EOF and closes it before the app runs.
pub(crate) fn resident_filter_fd() -> io::Result<OwnedFd> {
    let program = Policy::parse(RESIDENT_WEB_POLICY)?.compile()?;
    let name = c"spk-resident-seccomp";
    let raw = unsafe {
        libc::memfd_create(name.as_ptr(), libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING)
    };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    let fd = unsafe { OwnedFd::from_raw_fd(raw) };
    let mut written = 0;
    while written < program.len() {
        let n = unsafe {
            libc::write(
                fd.as_raw_fd(),
                program[written..].as_ptr().cast(),
                program.len() - written,
            )
        };
        if n < 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        written += n as usize;
    }
    let seals = libc::F_SEAL_SEAL | libc::F_SEAL_SHRINK | libc::F_SEAL_GROW | libc::F_SEAL_WRITE;
    if unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_ADD_SEALS, seals) } != 0
        || unsafe { libc::lseek(fd.as_raw_fd(), 0, libc::SEEK_SET) } != 0
    {
        return Err(io::Error::last_os_error());
    }
    Ok(fd)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Run a compiled program against one synthetic `seccomp_data`, as the kernel would.
    fn run(program: &[u8], arch: u32, nr: u32, args: [u64; 6]) -> u32 {
        let mut data = [0_u8; 64];
        data[0..4].copy_from_slice(&nr.to_ne_bytes());
        data[4..8].copy_from_slice(&arch.to_ne_bytes());
        for (i, arg) in args.iter().enumerate() {
            data[16 + 8 * i..24 + 8 * i].copy_from_slice(&arg.to_ne_bytes());
        }
        let insns: Vec<Insn> = program
            .chunks_exact(8)
            .map(|c| Insn {
                code: u16::from_ne_bytes([c[0], c[1]]),
                jt: c[2],
                jf: c[3],
                k: u32::from_ne_bytes([c[4], c[5], c[6], c[7]]),
            })
            .collect();
        let (mut pc, mut acc) = (0_usize, 0_u32);
        loop {
            let insn = insns[pc];
            pc += 1;
            match insn.code {
                BPF_LD_W_ABS => {
                    let at = insn.k as usize;
                    acc = u32::from_ne_bytes(data[at..at + 4].try_into().unwrap());
                }
                BPF_RET_K => return insn.k,
                code => {
                    let taken = match code {
                        BPF_JMP_JEQ_K => acc == insn.k,
                        BPF_JMP_JGE_K => acc >= insn.k,
                        BPF_JMP_JSET_K => acc & insn.k != 0,
                        other => panic!("unexpected opcode {other:#x}"),
                    };
                    pc += if taken { insn.jt } else { insn.jf } as usize;
                }
            }
        }
    }

    fn resident() -> Vec<u8> {
        Policy::parse(RESIDENT_WEB_POLICY).unwrap().compile().unwrap()
    }

    fn verdict(nr: i64, args: [u64; 6]) -> u32 {
        run(&resident(), AUDIT_ARCH, nr as u32, args)
    }

    const EPERM: u32 = SECCOMP_RET_ERRNO | libc::EPERM as u32;
    const ENOSYS: u32 = SECCOMP_RET_ERRNO | libc::ENOSYS as u32;

    #[test]
    fn resident_policy_compiles_within_kernel_limits() {
        let program = resident();
        assert_eq!(program.len() % 8, 0);
        assert!(program.len() / 8 <= MAX_INSNS);
        println!("resident seccomp program: {} instructions", program.len() / 8);
    }

    #[test]
    fn foreign_architecture_is_killed() {
        assert_eq!(
            run(&resident(), 0x4000_0003, libc::SYS_read as u32, [0; 6]),
            SECCOMP_RET_KILL_PROCESS
        );
    }

    #[test]
    fn plain_allow_deny_and_default() {
        assert_eq!(verdict(libc::SYS_read, [0; 6]), SECCOMP_RET_ALLOW);
        assert_eq!(verdict(libc::SYS_unshare, [0; 6]), EPERM);
        assert_eq!(verdict(libc::SYS_setns, [0; 6]), EPERM);
        assert_eq!(verdict(libc::SYS_mount, [0; 6]), EPERM);
        assert_eq!(verdict(libc::SYS_ptrace, [0; 6]), EPERM);
        assert_eq!(verdict(libc::SYS_bpf, [0; 6]), EPERM);
        assert_eq!(verdict(libc::SYS_io_uring_setup, [0; 6]), EPERM);
        assert_eq!(verdict(libc::SYS_clone3, [0; 6]), ENOSYS);
        assert_eq!(verdict(1023, [0; 6]), ENOSYS);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn x32_numbers_are_refused() {
        assert_eq!(verdict(X32_SYSCALL_BIT as i64 | libc::SYS_read, [0; 6]), EPERM);
    }

    #[test]
    fn clone_refuses_every_namespace_flag() {
        let thread = (libc::CLONE_VM | libc::CLONE_FS | libc::CLONE_FILES | libc::CLONE_SIGHAND
            | libc::CLONE_THREAD) as u64;
        assert_eq!(verdict(libc::SYS_clone, [thread, 0, 0, 0, 0, 0]), SECCOMP_RET_ALLOW);
        assert_eq!(verdict(libc::SYS_clone, [libc::SIGCHLD as u64, 0, 0, 0, 0, 0]), SECCOMP_RET_ALLOW);
        for flag in [
            libc::CLONE_NEWNS,
            libc::CLONE_NEWCGROUP,
            libc::CLONE_NEWUTS,
            libc::CLONE_NEWIPC,
            libc::CLONE_NEWUSER,
            libc::CLONE_NEWPID,
            libc::CLONE_NEWNET,
        ] {
            let flags = flag as u64 | libc::SIGCHLD as u64;
            assert_eq!(verdict(libc::SYS_clone, [flags, 0, 0, 0, 0, 0]), EPERM, "{flag:#x}");
        }
    }

    #[test]
    fn socket_family_ioctl_and_personality_arguments() {
        let afno = SECCOMP_RET_ERRNO | libc::EAFNOSUPPORT as u32;
        for family in [libc::AF_UNIX, libc::AF_INET, libc::AF_INET6] {
            assert_eq!(verdict(libc::SYS_socket, [family as u64, 1, 0, 0, 0, 0]), SECCOMP_RET_ALLOW);
        }
        for family in [libc::AF_NETLINK, libc::AF_PACKET, libc::AF_VSOCK, libc::AF_BLUETOOTH] {
            assert_eq!(verdict(libc::SYS_socket, [family as u64, 1, 0, 0, 0, 0]), afno);
        }
        assert_eq!(verdict(libc::SYS_ioctl, [0, libc::FIONREAD, 0, 0, 0, 0]), SECCOMP_RET_ALLOW);
        assert_eq!(verdict(libc::SYS_ioctl, [0, libc::TIOCSTI, 0, 0, 0, 0]), EPERM);
        // The kernel truncates the request to 32 bits; so does the filter.
        assert_eq!(verdict(libc::SYS_ioctl, [0, (1 << 32) | libc::TIOCSTI, 0, 0, 0, 0]), EPERM);
        assert_eq!(verdict(libc::SYS_ioctl, [0, 0x541c, 0, 0, 0, 0]), EPERM);
        assert_eq!(verdict(libc::SYS_personality, [0, 0, 0, 0, 0, 0]), SECCOMP_RET_ALLOW);
        assert_eq!(verdict(libc::SYS_personality, [0xffff_ffff, 0, 0, 0, 0, 0]), SECCOMP_RET_ALLOW);
        assert_eq!(verdict(libc::SYS_personality, [0x0040000, 0, 0, 0, 0, 0]), EPERM);
    }

    #[test]
    fn malformed_policies_are_refused() {
        for text in [
            "allow read",                                   // no default
            "default ENOSYS\ndefault EPERM",                // two defaults
            "default ENOSYS\nallow read read",              // duplicate
            "default ENOSYS\nallow read\ndeny EPERM read",  // duplicate across rules
            "default ENOSYS\nallow not_a_syscall",          // typo
            "default EACCES",                               // errno not in the set
            "default ENOSYS\nallow-arg socket 6 in 1 else EPERM",
            "default ENOSYS\nallow-arg socket 0 in else EPERM",
            "default ENOSYS\nallow-arg clone 0 clear 1 2 else EPERM",
            "default ENOSYS\nallow-arg socket 0 in 1",
        ] {
            assert!(Policy::parse(text).is_err(), "{text}");
        }
    }

    #[test]
    fn sealed_memfd_holds_exact_program() {
        let fd = resident_filter_fd().unwrap();
        let mut bytes = Vec::new();
        let mut buffer = [0_u8; 4096];
        loop {
            let n = unsafe { libc::read(fd.as_raw_fd(), buffer.as_mut_ptr().cast(), buffer.len()) };
            assert!(n >= 0);
            if n == 0 {
                break;
            }
            bytes.extend_from_slice(&buffer[..n as usize]);
        }
        assert_eq!(bytes, resident());
        assert!(unsafe { libc::write(fd.as_raw_fd(), b"x".as_ptr().cast(), 1) } < 0);
    }
}
