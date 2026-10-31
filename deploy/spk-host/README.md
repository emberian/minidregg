# SPK host

`native/spk-host` is the physical half of a Sandstorm SPK grain under Mini:
it installs, launches, sandboxes, routes, stops and recovers one app per Mini
application resource. It decides no authority. Install, START, every HTTP
request and WebSocket open, and STOP are authored, signed and admitted by the
Lean Host; Rust holds the processes, the files and the evidence.

Deployment steps (root install, operator user units, subuid ranges) are in
[USER-TENANCY.md](USER-TENANCY.md). At runtime nothing here runs as root except
the one-shot `mini-spk-volume-helper`, which the root-run `install-user-world`
admits through sudoers; the broker's own endpoint is described in
[BROKER-RUNTIME-UPGRADE.md](BROKER-RUNTIME-UPGRADE.md).

## Who runs what

| process | identity | what it does |
|---|---|---|
| `mini-spk-broker@STORE.service` | operator, systemd **user** unit | one JSON line per connection on `WORLD/runtime-STORE/broker.sock` (operator-owned 0600, peer uid = operator); the verbs are the `Request` enum in `native/spk-host/src/broker.rs`; renders the per-generation resident unit (the `Request::InstallUnit` arm of `Broker::handle`), the app's slice under its class slice (`Request::SetCgroup`; the class slices are `render_static`'s) and its hardening drop-in (`hardening` in `broker_home.rs`) |
| `mini-spk-s<store>-a<app>-g<gen>.service` | operator, user unit | `spk-host resident-bootstrap`: bwrap creates a user namespace, `newuidmap`/`newgidmap` map exactly {operator, app} into it, the resident joins it, forks the launch worker as the app, drops every capability, and serves the app's routes |
| the app | the broker-placed app uid inside that namespace | bubblewrap with the floor below; fd 3 is its Cap'n Proto bridge |
| `mini-spk-volume-helper` | root, via sudoers | creates, bounds (project quota), attests, captures and destroys the app's `/var` directory; see `VOLUMES.md` |

The resident unit keeps `NoNewPrivileges=no` because the setuid mapping
helpers must run; for the same reason it cannot take `ProtectSystem`,
`ProtectHome`, `PrivateTmp` or a `SystemCallFilter` (in a user manager each
implies `PrivateUsers=yes` or no-new-privileges). Its drop-in carries
`LimitCORE=0`, `LimitNOFILE=8192` and `KeyringMode=private`. A compromised
resident is the operator of the world (it holds every participant seed); the
resident's own filesystem confinement is still owed.

Names carry the Store: `<store>` is the pinned Host's `profile.storeTag`
(16 hex digits), so two Stores on one host never share a unit, slice or
volume.

## The app's sandbox floor

`sandbox::FIXED_ARGS` (`native/spk-host/src/sandbox.rs`) and `native/spk-host/seccomp/resident-web.policy`:

- new user, PID, IPC, UTS, cgroup and network namespaces (loopback only),
  `--disable-userns`, `--cap-drop ALL`, hostname `sandbox`;
- the package root read-only from an open fd, the bounded ext4 `/var`, a
  128 MiB `/tmp`, `/proc`, and a read-only 64 KiB `/dev` holding only null,
  zero, full, random, urandom and the /dev/fd link;
- RLIMIT_NOFILE 1024 (hard), set at spawn (`APP_MAX_FILES` in `spawn_gate.rs`);
- a default-ENOSYS seccomp allowlist: AF_UNIX/INET/INET6 sockets only, no
  namespaces, mounts, ptrace, bpf, io_uring, keyrings or module calls; and,
  as Sandstorm's supervisor refuses them, no `seccomp`/`PR_SET_SECCOMP`,
  legacy AIO, `vmsplice` or memory-policy calls;
- fds 0-3 only: `/dev/null`, the private output pipe (16 MiB kept per
  generation) and fd 3.

`scripts/spk-platform/sandbox-floor-audit.sh` measures this floor through
the production bootstrap and spawn path, run as the operator on Linux, inside
a transient user unit carrying the resident unit's hardening properties
(`RESIDENT_PROPS` in the script), and names the openat2 class if bwrap's own
stderr reports `Function not implemented` (the detector matches only bwrap's own
`bwrap: ...` lines). The recorded run on `dregg-build` (Debian 13.7, bubblewrap 0.12.0,
audit root `/var/lib/spk-floor-audit`) exits 0 for both audit tests: 32 floor checks held
and the 21 expected pre-floor breaches
(`docs/evidence/2026-10-27-sandbox-floor-dregg-build/README.md`; that run's
`results.txt` shows an openat2 line from an earlier detector that also matched the
probe's JSON).

**bwrap version dependence.** bubblewrap 0.11 and later (Debian 13 ships
0.12.0) need `openat2` (the test
`hardening_drop_in_is_never_empty_and_never_blocks_newuidmap` in `broker_home.rs`). Any unit setting that installs a
systemd seccomp layer returning ENOSYS for `openat2` kills bwrap at its first
mount (`bwrap: Can't mkdir parents for /dev: Function not implemented`).
systemd 257's `RestrictSUIDSGID=yes` does; so the resident and every
bwrap-launching unit must not carry it (the resident cannot take
`NoNewPrivileges=yes` or `NoExecPaths=` either, see above; the app's `/var` is
mounted `nosuid,nodev` and bwrap's own mounts are nosuid). The pinned bwrap
(`MINI_SPK_BWRAP_SHA256`, or a profiled copy such as
`/usr/local/libexec/mini-grain-bwrap`) is therefore qualified per version:
re-run the floor audit on the target host whenever the pinned binary changes.
The app's own seccomp policy allows `openat2` (`seccomp/resident-web.policy:72`).

## Requests, lifecycle, recovery

- Routes and the HTTP entrance: [HTTP-CUSTODIAN-CONTRACT.md](HTTP-CUSTODIAN-CONTRACT.md).
- The dispatch fence and outcomes: [MINI-CLAIM-DISPATCH-CONTRACT.md](MINI-CLAIM-DISPATCH-CONTRACT.md).
- WebSockets and their authority leases: [BROWSER-WEBSOCKETS.md](BROWSER-WEBSOCKETS.md),
  [WS-AUTHORITY-LEASES.md](WS-AUTHORITY-LEASES.md), [STREAM-CONTINUITY.md](STREAM-CONTINUITY.md).
- Adding a participant route to a running resident: [HOT-ROUTE-ENROLLMENT.md](HOT-ROUTE-ENROLLMENT.md).
- Rebinding retained generations to a compatible upgraded profile: [PROFILE-UPGRADE.md](PROFILE-UPGRADE.md).
- Attaching SPK apps to an existing Store, and ordinary checkpoints: [SAME-STORE-AND-CHECKPOINT.md](SAME-STORE-AND-CHECKPOINT.md).
- A separate controller account per world: [CONTROLLER-SETUP.md](CONTROLLER-SETUP.md).
- START and STOP are lifecycle v3 (`lifecycle_v3_*_native.rs`); a governed
  repeat CREATE uses the v4 lane (`lifecycle_v4_retry_*_native.rs`). The
  opcodes live in the Lean kernel (`Kernel/ApplicationGrain.lean`), not here.
  A lost submit reply is answered by the lookup, never a resend.
- A crashed generation fails its unit; `OnFailure=` starts the broker-rendered
  supervisor instance (`supervisor_text` in `broker_runtime_adoption.rs`, `Restart=on-failure`),
  which runs `spk-host grain supervise-instance GRAINS_ROOT STORE-APP`
  (`supervise` in `grain.rs`). It STOPs the dead generation through Mini and continues on
  the same `/var`; an uncertain record is reported, never retried (exit 3: `unresolved`
  in `grain.rs`, mapped by `main.rs`). A START that failed after its claim is reconciled
  through `reconcileFailedStart` (`reconcile_failed_start` in `grain_export.rs`), on either lane's
  retained artifacts.

## Ingest and volumes

`deploy/spk-host/spk-ingest` (its usage line names the arguments: `--root SPK_ROOT [--import-profile PROFILE] HOST HOST_SHA256 INBOX_SPK APP_UID`) parses and materializes a
signed SPK as the Store operator (never root) in a short-lived **user** unit
with a 2 GiB memory cap (no swap), one CPU, a 16-task cap (`spk-ingest:44-48`), the import
profile's bounds from the pinned host (`spk-host import-limits PROFILE RAW_BYTES`: the raw and
decoded caps, and a wall clock of 60 s plus 3 s per raw MiB, at most 900 s for `standard-v1`
and 1800 s for `market-large-v1` and `operator-appliance-v1`; the profile is selected only by
the operator broker's config) and a SHA-pinned host
executable. The unit sets `NoNewPrivileges` and those caps only: it is not
network- or filesystem-confined. A killed unit is not an installed package. The
parser verifies the signature, archive hash and manifest, refuses escaping
names, and publishes a read-only image by no-replace rename. The volume helper
(`broker_volume_dir.rs`, called only through the one-shot helper; the statement of what it
guarantees is `VOLUMES.md`) makes the app's `/var` a directory on an ext4 or xfs with project
quotas, whose project limit is the class size, and publishes the
`DREGG/SPK-VAR-CUSTODY/v1+projdir` witness the resident checks against the Mini-selected volume
before launch. There is no loop device, image or filesystem UUID. Imported images are parsed in
userspace by e2fsprogs as the app uid and never mounted.

Size classes are `broker::CLASSES` (S/M/L memory, CPU, tasks, IO weight,
`/var` size, WebSocket caps); they are operator policy until a Lean
declaration pins them.

### Slice tree (the class is in the name)

The broker renders, and only `broker::{grains_slice, class_slice, app_slice}` name:

```text
s{STORE}-{PREFIX}-grains.slice                      supervisors (no class)
  s{STORE}-{PREFIX}-grains-{S|M|L}.slice            one size class (rendered at broker start)
    s{STORE}-{PREFIX}-grains-{S|M|L}-a{APP}.slice   one app: its limits, its resident unit
```

The class is the one `set-cgroup` recorded (`grain.rs` `place`, from the app's declared
size class); `install-unit` refuses an app with no class, so no grain lands outside a class
slice, and a class change is refused once a unit is installed (the unit names its slice).
Resident units are `mini-spk-s{STORE}-a{APP}-g{GEN}.service` (a pinned grammar; the class
is in the slice, not the unit name). Per-grain CPU ceilings are drop-ins on the class
prefix, one per class, bounding each app of that class and not the class together:

```ini
# ~/.config/systemd/user/s{STORE}-{PREFIX}-grains-S-.slice.d/60-cpu.conf   (M: 50%, L: 100%)
[Slice]
CPUQuota=25%
```

A drop-in on `s{STORE}-{PREFIX}-grains-S.slice.d/` instead would cap every S app together.
The Hermes `mini-grain-controller@` / `mini-grain-resident@` units are not SPK grains and
are not in this tree.
