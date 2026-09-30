# Resident sandbox floor: fd audit and escape probe, 2026-09-30

Source commit `a28cf6b` (branch `m11-sandbox-floor`), persvati, kernel 6.17.0-40-generic,
`/usr/bin/bwrap` bubblewrap 0.11.0-2ubuntu0.1, SHA-256
`7bbffeb19f312d5503232e1502f0f97f2ac4ffcb51dec47d9a58bffbad1f12d5`. Unprivileged user
namespaces are enabled (`kernel.unprivileged_userns_clone=1`); Ubuntu's AppArmor userns
restriction is on and bubblewrap has its profile.

## What ran

`scripts/spk-platform/sandbox-floor-audit.sh` builds a throwaway image (the probe, `ld-linux`,
`libc`, `libgcc_s`, hashes in `audit/environment.txt`), mounts a 16 MiB tmpfs owned by the app
UID 65534 as the separate `/var`, and runs two `#[ignore]` root tests from the spk-host lib test
executable in transient system units (MemoryMax 256M, KillMode=control-group, no
PrivateNetwork, so the network result is the sandbox's own). Both tests call
`PreparedResident::prepare` and then `spawn_gate::spawn_bounded`, the same calls
`PreparedResident::start` makes, without the journal. The gate runs as root, pins bwrap by
SHA-256, drops to UID/GID 65534 with no_new_privs, and execs bwrap, which execs
`/spk-sandbox-probe` as the app. The probe writes to stdout, which is the app's private output
pipe; the host pump writes that to `app-output-*.log`.

| run | argument list | probe verdict | test |
|---|---|---|---|
| `floor` | the committed `bwrap_args` | `floor-held`, 24/24 | pass |
| `pre-floor` (negative control) | the abe988d list: no `--disable-userns`, `--cap-drop`, `--seccomp` | `floor-breached`, 15/24 failed | pass (it must breach) |

Transcripts: `audit/floor.transcript`, `audit/pre-floor.transcript`; probe output:
`audit/app-output-floor.log`, `audit/app-output-pre-floor.log`.

## Floor run, what the probe measured inside the sandbox

- **fds.** `/proc/self/fd` = 0 `/dev/null`, 1 and 2 the same `pipe:[…]`, 3 `socket:[…]`.
  Nothing else and no directory. The sandbox's pid 1 (bwrap init) holds 0/1/2 and an eventfd
  (8), no directory.
- **`..` walk.** `openat(fd, "..")` for every fd 3..=64 returned EBADF or ENOTDIR;
  fd 4 and fd 5 are EBADF. bubblewrap closed the image and `/var` handles before exec.
- **Network.** connect to 1.1.1.1:80 and [2606:4700:4700::1111]:80: ENETUNREACH (101).
  127.0.0.1:1: ECONNREFUSED (111), so only loopback exists. AF_NETLINK, AF_PACKET and
  AF_VSOCK sockets: EAFNOSUPPORT (97).
- **Nested user namespace.** `unshare(CLONE_NEWUSER)`, `clone(CLONE_NEWUSER)` and `setns`:
  EPERM. Each runs in a forked child, so a success could not change what the other checks saw.
- **Privilege.** CapInh/Prm/Eff/Bnd/Amb all zero, NoNewPrivs 1, Seccomp 2, one filter.
- **Refused families.** mount, PTRACE_TRACEME, bpf, io_uring_setup, keyctl,
  open_by_handle_at, personality(ADDR_NO_RANDOMIZE), and ioctl TIOCSTI with the high word set
  are all EPERM. Syscall 1023 is ENOSYS.
- **Positive control.** A thread, fork+wait, a 127.0.0.1 listener with a round trip, a
  `/var` write, and a `/tmp` write all work, and the image root is read-only.

## Negative control, what the pre-floor list allowed

With the gate unchanged and only the bubblewrap list reverted, the probe saw:

- Seccomp 0.
- fd 6, the unconsumed seccomp memfd, left open.
- Netlink sockets were opened; packet (EPERM) and vsock (ESOCKTNOSUPPORT) gave the wrong errno.
- `PTRACE_TRACEME` and `personality(ADDR_NO_RANDOMIZE)` succeeded.
- `unshare(CLONE_NEWUSER)` and `clone(CLONE_NEWUSER)` **succeeded**: a nested user namespace.
- bpf, io_uring, keyctl and open_by_handle_at reached the kernel (EINVAL/EFAULT, not refused).

Capabilities were already zero under the pre-floor list: in this unprivileged mode bubblewrap
drops them itself, so `--cap-drop ALL` makes the drop explicit rather than changing it. fds 4
and 5 were EBADF there too. What was missing pre-floor was the syscall filter and the userns
block, not the fd close.

## Layers

`layers/disable-userns-alone.txt`: with no seccomp filter, `unshare -U` inside bwrap succeeds
without `--disable-userns` and fails with ENOSPC with it. So the nested-userns block has two
independent layers: seccomp (EPERM, what the probe sees) and bubblewrap's
`user.max_user_namespaces=1` in an unescapable parent namespace.

## A real web app under the floor

`gitweb/`: the signed GitWeb SPK (SHA-256 `2bbfe6d3…2caa`, the 2026-09-27 fixture) ran
`gitweb-smoke create` through `spawn_sandbox`, which uses the same `bwrap_args`. It ran as
UID 995 in a transient unit, against a fresh 256 MiB tmpfs `/var`; the retained 09-27 volume was
not touched. nginx, fcgiwrap, perl and git all ran under the seccomp allowlist:

- the developer push returned 200 and installed the commit;
- the guest receive-pack advertisement returned 403;
- the guest clone fetched the commit and the README hash;
- the owner browser GET returned HTML 200 (5418 bytes).

The app's own `set -x` trace is in `gitweb/app-output.log`, not in the unit log.

## Limits of this evidence

- The Mini lifecycle (BEGIN, claim, `Journal::enter_and_spawn`) did not run: no full resident
  journey exists on persvati yet. The audit calls the same two functions `start` calls, minus
  the journal write.
- The allowlist is qualified against one real package (GitWeb) and the probe's positive
  control. Another runtime may need a syscall this file leaves at ENOSYS. The fix is a reviewed
  line in `resident-web.policy`, not a broader default.
- The negative control ran through the new gate. So it shows the argument-list difference only.
  The old gate's stdout/stderr pass-through is covered by
  `spawn_gate::tests::child_never_inherits_launcher_stdout_or_stderr`, which failed under a
  mutation that removed the dup2s.
