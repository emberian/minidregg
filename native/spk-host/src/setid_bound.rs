//! The de-rooted resident's one privilege, bounded.
//!
//! The resident runs as the Store operator with ambient CAP_SETUID and
//! CAP_SETGID so its spawn gate can become the app UID. Unbounded, those two
//! capabilities would let a compromised resident (the fd3 Cap'n Proto parser
//! reads app-controlled bytes) become any UID, root included. Before anything
//! else the resident installs this filter on every thread: `setresuid` and
//! `setresgid` are admitted only with all three ids equal to the broker-chosen
//! app UID/GID, `setgroups` only with an empty list, and every other set*id
//! call is refused. The filter is inherited by the gate child, bubblewrap and
//! the app, where it changes nothing (none of them switches identity).

use std::io;

const RET_KILL_PROCESS: u32 = 0x8000_0000;
const RET_ERRNO: u32 = 0x0005_0000;
const RET_ALLOW: u32 = 0x7fff_0000;
const LD_W_ABS: u16 = 0x20;
const JEQ_K: u16 = 0x15;
const JGE_K: u16 = 0x35;
const RET_K: u16 = 0x06;
const OFFSET_NR: u32 = 0;
const OFFSET_ARCH: u32 = 4;
const fn arg_low(index: u32) -> u32 {
    16 + 8 * index
}

#[cfg(target_arch = "x86_64")]
const AUDIT_ARCH: u32 = 0xc000_003e;
#[cfg(target_arch = "aarch64")]
const AUDIT_ARCH: u32 = 0xc000_00b7;
#[cfg(target_arch = "x86_64")]
const X32_SYSCALL_BIT: Option<u32> = Some(0x4000_0000);
#[cfg(target_arch = "aarch64")]
const X32_SYSCALL_BIT: Option<u32> = None;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Label {
    Nr,
    Dispatch,
    ResUid(u32),
    ResGid(u32),
    Groups,
    Allow,
    Deny,
    Kill,
}

enum Ins {
    At(Label),
    Ld(u32),
    Jeq(u32, Label, Label),
    Jge(u32, Label, Label),
    Ret(u32),
}

fn three_equal(at: fn(u32) -> Label, value: u32, out: &mut Vec<Ins>) {
    for index in 0..3 {
        out.push(Ins::At(at(index)));
        out.push(Ins::Ld(arg_low(index)));
        let next = if index == 2 {
            Label::Allow
        } else {
            at(index + 1)
        };
        out.push(Ins::Jeq(value, next, Label::Deny));
    }
}

/// The classic-BPF program, little-endian `seccomp_data` offsets.
pub(crate) fn program(app_uid: u32, app_gid: u32) -> io::Result<Vec<libc::sock_filter>> {
    if app_uid == 0 || app_gid == 0 || app_uid == u32::MAX || app_gid == u32::MAX {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "setid bound needs a non-root app UID/GID",
        ));
    }
    let deny = RET_ERRNO | libc::EPERM as u32;
    let mut flat = vec![
        Ins::Ld(OFFSET_ARCH),
        Ins::Jeq(AUDIT_ARCH, Label::Nr, Label::Kill),
        Ins::At(Label::Nr),
        Ins::Ld(OFFSET_NR),
    ];
    if let Some(bit) = X32_SYSCALL_BIT {
        flat.push(Ins::Jge(bit, Label::Kill, Label::Dispatch));
    }
    // A comparison chain: `Dispatch` as a target means "fall through to the
    // next comparison".
    let mut chain: Vec<(u32, Label)> = vec![
        (libc::SYS_setresuid as u32, Label::ResUid(0)),
        (libc::SYS_setresgid as u32, Label::ResGid(0)),
        (libc::SYS_setgroups as u32, Label::Groups),
    ];
    chain.extend(
        [
            libc::SYS_setuid,
            libc::SYS_setgid,
            libc::SYS_setreuid,
            libc::SYS_setregid,
            libc::SYS_setfsuid,
            libc::SYS_setfsgid,
        ]
        .iter()
        .map(|nr| (*nr as u32, Label::Deny)),
    );
    for (nr, target) in chain {
        flat.push(Ins::Jeq(nr, target, Label::Dispatch));
    }
    flat.push(Ins::Ret(RET_ALLOW));
    three_equal(Label::ResUid, app_uid, &mut flat);
    three_equal(Label::ResGid, app_gid, &mut flat);
    flat.push(Ins::At(Label::Groups));
    flat.push(Ins::Ld(arg_low(0)));
    flat.push(Ins::Jeq(0, Label::Allow, Label::Deny));
    flat.push(Ins::At(Label::Allow));
    flat.push(Ins::Ret(RET_ALLOW));
    flat.push(Ins::At(Label::Deny));
    flat.push(Ins::Ret(deny));
    flat.push(Ins::At(Label::Kill));
    flat.push(Ins::Ret(RET_KILL_PROCESS));
    assemble(&flat)
}

fn assemble(code: &[Ins]) -> io::Result<Vec<libc::sock_filter>> {
    // Position of each label; `Dispatch` as a jump target means "the next
    // instruction" (a fall-through in the comparison chain).
    let mut positions = Vec::new();
    let mut pc = 0usize;
    for ins in code {
        match ins {
            Ins::At(label) => positions.push((*label, pc)),
            _ => pc += 1,
        }
    }
    let target = |label: Label, here: usize| -> io::Result<u8> {
        let to = if label == Label::Dispatch {
            here + 1
        } else {
            positions
                .iter()
                .find(|(l, _)| *l == label)
                .map(|(_, p)| *p)
                .ok_or_else(|| io::Error::other("unresolved BPF label"))?
        };
        to.checked_sub(here + 1)
            .and_then(|delta| u8::try_from(delta).ok())
            .ok_or_else(|| io::Error::other("BPF jump out of range"))
    };
    let mut out = Vec::new();
    for ins in code {
        let here = out.len();
        let filter = match ins {
            Ins::At(_) => continue,
            Ins::Ld(offset) => libc::sock_filter {
                code: LD_W_ABS,
                jt: 0,
                jf: 0,
                k: *offset,
            },
            Ins::Jeq(value, yes, no) => libc::sock_filter {
                code: JEQ_K,
                jt: target(*yes, here)?,
                jf: target(*no, here)?,
                k: *value,
            },
            Ins::Jge(value, yes, no) => libc::sock_filter {
                code: JGE_K,
                jt: target(*yes, here)?,
                jf: target(*no, here)?,
                k: *value,
            },
            Ins::Ret(value) => libc::sock_filter {
                code: RET_K,
                jt: 0,
                jf: 0,
                k: *value,
            },
        };
        out.push(filter);
    }
    Ok(out)
}

/// Install the bound on every thread of this process (TSYNC). Requires
/// no_new_privs, which the resident unit sets and this call re-asserts.
pub(crate) fn install(app_uid: u32, app_gid: u32) -> io::Result<()> {
    let filters = program(app_uid, app_gid)?;
    let prog = libc::sock_fprog {
        len: filters.len() as u16,
        filter: filters.as_ptr() as *mut libc::sock_filter,
    };
    if unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) } != 0 {
        return Err(io::Error::last_os_error());
    }
    const SECCOMP_SET_MODE_FILTER: libc::c_long = 1;
    const SECCOMP_FILTER_FLAG_TSYNC: libc::c_long = 1;
    let rc = unsafe {
        libc::syscall(
            libc::SYS_seccomp,
            SECCOMP_SET_MODE_FILTER,
            SECCOMP_FILTER_FLAG_TSYNC,
            &prog as *const libc::sock_fprog,
        )
    };
    if rc != 0 {
        return Err(if rc < 0 {
            io::Error::last_os_error()
        } else {
            io::Error::other(format!("setid bound: thread {rc} could not synchronize"))
        });
    }
    Ok(())
}

#[repr(C)]
struct CapHeader {
    version: u32,
    pid: libc::c_int,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct CapData {
    effective: u32,
    permitted: u32,
    inheritable: u32,
}

/// Async-signal-safe: clear the effective, permitted and inheritable sets
/// (called in the forked gate child after the UID switch).
pub(crate) fn clear_capabilities() -> bool {
    const LINUX_CAPABILITY_VERSION_3: u32 = 0x2008_0522;
    let header = CapHeader {
        version: LINUX_CAPABILITY_VERSION_3,
        pid: 0,
    };
    let data = [CapData {
        effective: 0,
        permitted: 0,
        inheritable: 0,
    }; 2];
    unsafe { libc::syscall(libc::SYS_capset, &header as *const CapHeader, data.as_ptr()) == 0 }
}

/// The calling thread's effective set holds CAP_SETUID (7) and CAP_SETGID (6).
pub(crate) fn holds_setid_capabilities() -> io::Result<bool> {
    let status = std::fs::read_to_string("/proc/thread-self/status")?;
    let effective = status
        .lines()
        .find_map(|line| line.strip_prefix("CapEff:"))
        .and_then(|value| u64::from_str_radix(value.trim(), 16).ok())
        .ok_or_else(|| io::Error::other("CapEff unreadable"))?;
    Ok(effective & (1 << 6) != 0 && effective & (1 << 7) != 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A classic-BPF interpreter over exactly the opcodes this filter uses.
    fn run(program: &[libc::sock_filter], arch: u32, nr: u32, args: [u64; 3]) -> u32 {
        let mut data = [0u8; 64];
        data[0..4].copy_from_slice(&nr.to_le_bytes());
        data[4..8].copy_from_slice(&arch.to_le_bytes());
        for (index, arg) in args.iter().enumerate() {
            data[16 + 8 * index..24 + 8 * index].copy_from_slice(&arg.to_le_bytes());
        }
        let mut acc = 0u32;
        let mut pc = 0usize;
        loop {
            let ins = program[pc];
            pc += 1;
            match ins.code {
                LD_W_ABS => {
                    let k = ins.k as usize;
                    acc = u32::from_le_bytes(data[k..k + 4].try_into().unwrap());
                }
                JEQ_K => pc += if acc == ins.k { ins.jt } else { ins.jf } as usize,
                JGE_K => pc += if acc >= ins.k { ins.jt } else { ins.jf } as usize,
                RET_K => return ins.k,
                other => panic!("unexpected opcode {other:#x}"),
            }
        }
    }

    const U: u32 = 993;
    const G: u32 = 978;

    #[test]
    fn only_the_app_ids_are_reachable() {
        let p = program(U, G).unwrap();
        let deny = RET_ERRNO | libc::EPERM as u32;
        let resuid = libc::SYS_setresuid as u32;
        let resgid = libc::SYS_setresgid as u32;
        let u = U as u64;
        let g = G as u64;
        assert_eq!(run(&p, AUDIT_ARCH, resuid, [u, u, u]), RET_ALLOW);
        assert_eq!(run(&p, AUDIT_ARCH, resgid, [g, g, g]), RET_ALLOW);
        for args in [
            [0, 0, 0],
            [u, u, 0],
            [u, 0, u],
            [0, u, u],
            [u, u, u32::MAX as u64],
        ] {
            assert_eq!(run(&p, AUDIT_ARCH, resuid, args), deny, "{args:?}");
        }
        assert_eq!(run(&p, AUDIT_ARCH, resgid, [g, g, 0]), deny);
        assert_eq!(run(&p, AUDIT_ARCH, resgid, [u, u, u]), deny);
        // High bits are ignored by the kernel's uid_t read, and by the filter.
        assert_eq!(run(&p, AUDIT_ARCH, resuid, [u | 1 << 32, u, u]), RET_ALLOW);
        assert_eq!(
            run(&p, AUDIT_ARCH, libc::SYS_setgroups as u32, [0, 0, 0]),
            RET_ALLOW
        );
        assert_eq!(
            run(&p, AUDIT_ARCH, libc::SYS_setgroups as u32, [1, 0, 0]),
            deny
        );
        for nr in [
            libc::SYS_setuid,
            libc::SYS_setgid,
            libc::SYS_setreuid,
            libc::SYS_setregid,
            libc::SYS_setfsuid,
            libc::SYS_setfsgid,
        ] {
            assert_eq!(run(&p, AUDIT_ARCH, nr as u32, [u, u, u]), deny, "{nr}");
        }
        assert_eq!(
            run(&p, AUDIT_ARCH, libc::SYS_read as u32, [0, 0, 0]),
            RET_ALLOW
        );
        assert_eq!(
            run(&p, AUDIT_ARCH, libc::SYS_capset as u32, [0, 0, 0]),
            RET_ALLOW
        );
        assert_eq!(run(&p, AUDIT_ARCH ^ 1, resuid, [u, u, u]), RET_KILL_PROCESS);
        if let Some(bit) = X32_SYSCALL_BIT {
            assert_eq!(
                run(&p, AUDIT_ARCH, resuid | bit, [0, 0, 0]),
                RET_KILL_PROCESS
            );
        }
    }

    #[test]
    fn root_ids_are_refused_at_build() {
        assert!(program(0, G).is_err());
        assert!(program(U, 0).is_err());
    }
}
