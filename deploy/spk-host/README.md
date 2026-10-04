# SPK host construction checkpoint

This package is the physical half of Mini's planned long-lived application
resource. It does **not** admit an application or authorize a request. Mini must
authorize installation, first creation, wake, each RPC dispatch, snapshot,
upgrade, and shutdown against current grants and an exact resource generation.
`spk-host` deliberately has no `run` CLI until that admission is connected.

`native/spk-host` reuses Bread's pinned `sandstorm-package` parser to verify the
real SPK signature, archive hash and manifest before writing a package tree.
It rejects duplicate and escaping names, verifies mountpoints are real
directories, writes all regular files before any symlink, keeps staging private,
and publishes a complete read-only image by no-replace rename. Absolute symlinks
such as `/lib/...` are retained because they are rooted in the eventual jail;
the installer never follows them on the host. The raw signed SPK remains beside
the tree. Package identity is the raw SPK SHA-256 and signing-key-derived app ID,
not a claim inferred from file names.

Run package parsing only through `spk-ingest HOST_BINARY HOST_SHA256 INBOX_SPK
APP_UID` after placing a root-owned mode-0600 SPK directly in
`/var/lib/minidregg/spk/inbox`. It starts a short-lived system unit with a
2 GiB memory cap (no swap), 120-second runtime cap, 16-task cap, no network, a
read-only host filesystem except the package store, and a SHA-pinned host
executable. The host hands the parser a 768 MiB decompressed-output cap
(`materialize::MAX_DECOMPRESSED_PACKAGE_BYTES`) instead of Bread's 256 MiB
default, which refused 4 of 10 market packages (TT-RSS, Etherpad, Davros,
Wekan; SPK-APPS 2026-10-01). The parse holds the plain stream and the decoded
archive at once, about 2.2x the decompressed size (Wekan: 1.17 GB, 16 s).
That cap is **not** a peak-memory bound by itself:
the xz library can allocate an entire block before writing to the bounded
sink. The cgroup is therefore part of the ingest boundary. A killed or failed
unit is not an installed package.

## Who runs what: the operator, the broker, the resident, the app

`spk-host grain` runs as the Store operator (`mini`), never as root, and
refuses root. Every root-only step is one typed request to **`mini-spk-broker`**
(`native/spk-host/src/broker.rs`), a root service on
`/run/mini-spk-broker.sock` (`0660 root:<operator group>`) that answers only
the operator UID (`SO_PEERCRED`) and logs every request with the peer's
pid/uid/gid to `GRAINS/broker/broker.log` and its journal. Its verbs are the
whole surface; an unknown verb or field refuses at decode:

| verb | what root does |
|---|---|
| `init-store {store}` | creates `GRAINS/<store>` (operator 0700) and reports the host identity |
| `place {store, app}` | allocates the app UID from the broker's own pool (the operator never names a UID) |
| `set-cgroup {store, app, class}` | records the size class and renders `<prefix>-grains-s<store>a<app>.slice` |
| `ingest {store, app, sha256}` | copies the Store's staged SPK into the inbox and runs `spk-ingest` |
| `mount-volume {store, app, volumeId, importSha256?}` | creates once (`spk-var-volume create` / `create-from`), then attests |
| `unmount {store, app}` | unmounts a volume none of whose units is active |
| `install-unit {store, app, generation}` | renders `mini-spk-a<app>-g<gen>.service` from the broker's template |
| `start {unit}` / `stop {unit}` | only units this broker installed; `stop` resets a failed unit to inactive |
| `export-volume {store, app}` | copies a stopped app's image (fs frozen during the copy) to `GRAINS/<store>/exports/` |
| `backup {}` | `mini-spk-broker backup` into `GRAINS/backups/<time>/` |

The client passes parameters, never unit text, paths or UIDs. Every path the
broker touches is below its grains root, whose ancestors must be root-owned and
not group/world writable; operator files it reads (a staged SPK, an import
image, a resident config's existence) are opened by an `O_NOFOLLOW` walk that
requires operator ownership. Store keys are 16 lowercase hex; app ids and
generations are canonical decimals.

**Names carry the Store.** `<store>` is Mini's `storeTag`: the low 64 bits of
the deployment's genesis seed identity (`Config.expectedSeed`) in 16 lowercase
hex digits, which the pinned Host prints in its `profile` and the SPK host
never derives itself (`grain init-store GRAINS MINI_HOST MINI_CONFIG` names the
state root `GRAINS/<store>/host` by it, and every profile load re-reads it from
the pinned Host and refuses a state root that differs). Volumes, mounts,
witnesses and slices are named `<store>-<app>` / `s<store>a<app>`; the resident
unit is `mini-spk-s<store>-a<app>-g<gen>.service`, pinned by Mini
(`Kernel/ApplicationLifecycleResidentProfile.processIdentity`) and signed into
every lifecycle BEGIN. Two Stores on one host, a scratch copy beside a live
world included, never name the same unit or adopt each other's `/var`. The
broker records which Store installed each unit and refuses a start or stop
whose record differs from the Store in the name.

**The resident unit** (rendered per generation, runtime, not enabled):
`User=`/`Group=` the operator, `Slice=` the app's class slice,
`AmbientCapabilities=CAP_SETUID CAP_SETGID` (and the same bounding set),
`NoNewPrivileges=yes`, `ProtectSystem=strict` with write access to the Store's
grain state and the app's `/var` mount only, `ProtectHome`, `PrivateTmp`,
`KillMode=control-group`, `OnFailure=<prefix>-spk-supervisor@<store>-<app>`, and
`Environment=` the broker-chosen app UID/GID, grains root and Store key. The
resident's first act is to install a seccomp filter on every thread
(`setid_bound.rs`): `setresuid`/`setresgid` only with all three ids equal to
that app UID/GID, `setgroups` only empty, every other set*id call `EPERM`, x32
numbers and a foreign arch killed. A compromised resident (the fd-3 Cap'n Proto
parser reads app bytes) therefore cannot become root or another grain; it is
the operator. Why not a per-app resident UID: the resident authors Mini
lifecycle writes as the host's management subject through the operator socket,
which Mini requires to be owned by the caller (`PrivateOperator`); a per-grain
resident UID would need that socket opened to every grain, or the management
key split per grain (K-SPK). The descriptors survive the UID switch because the
gate child `dup2`s 3/4/5/6 and the output pipe **before** `setresgid`/
`setresuid`; file descriptors are not re-checked against the new UID, and 4/5
are `O_PATH` opens, so the app UID needs no permission on the image ancestors.
After the switch the child clears ambient, permitted, effective and
inheritable capabilities, then `execveat`s the pinned bwrap.

**The supervisor.** A generation is one START claim; it is never relaunched in
place (the resident journal refuses a second launch without fd 3). The resident
exits when its app exits (a pidfd on the bwrap child is in its poll set), so a
crashed app or a killed resident fails the unit, whose `OnFailure=` starts
`<prefix>-spk-supervisor@<store>-<app>.service` (`Type=oneshot`,
`Restart=on-failure`, `RestartSec=30`, `StartLimitBurst=3` per 30 min,
`RestartPreventExitStatus=3`). It runs `spk-host grain supervise`: the dead
generation is STOPped through Mini (the exact-unit audit accepts a dead
incarnation: same InvocationID, no cgroup, MainPID 0, failed/inactive), and a
continue-START of the next generation follows on the same `/var`. An uncertain
record exits 3 and is never retried. A START that failed after its claim
(phase 9: the journal says Entered, no child, and the manager shows the same
dead invocation with an empty cgroup) is reconciled through Mini's
`reconcileFailedStart` (kernel 9 -> 2, generation + 1): the supervisor authors
the custodian-signed failed-START report from that read-only audit, prepares
(op 206), signs, assembles (207) and submits (208) the recovery, retaining
every artifact in `g<N>/failed-start-recovery-v1/` and writing
`submit-requested.json` before the submission. After that marker it only asks
Mini: lookup (209) of the exact retained bytes, and, when Mini holds no receipt
for them, the same bytes again (the ingress's stable nullifier admits one
recovery per START). The confirmed receipt lands in
`g<N>/failed-start-recovered-v1.json`, and `grain status` then reports g<N>
stopped with g<N+1> consumed; the next START is g<N+2>.

**Size classes** (`broker::CLASSES`; the kernel will pin the class in the app
birth descriptor, K-SPK): S = `MemoryMax=512M`, `CPUWeight=50`, `TasksMax=256`,
`IOWeight=50`, 512 MiB `/var`; M = `1G`, `100`, `512`, `100`, 1 GiB `/var`;
L = `2G`, `200`, `1024`, `200`, 2 GiB `/var` (a Meteor+Mongo app such as
Wekan, or a file store). `MemorySwapMax=0`. The class slices sit in `<prefix>-grains.slice`; with
`mini.slice` at 3 GB, two class-S grains plus the Store fit, or one class M.

**Backups and export.** `mini-spk-broker backup CONFIG OUT` (root, called by
`mini-backup`) copies every registered volume with its filesystem frozen for
the copy: a running app's image is captured at one crash-consistent instant
(SQLite inside is built to recover from exactly that), a stopped one exactly;
each copy is `e2fsck -fn`-checked and its root listed with `debugfs` without
mounting. `spk-host grain export PROFILE APP OUT` requires the app's latest
generation STOPped by a completed STOP and writes `var.ext4`, `manifest.json`
(image SHA-256, package, class, volume id, the STOP receipt and its SHA-256)
and `manifest.sig` (the Store's completion custodian over the manifest bytes).
`grain install … --import DIR --exporter-key HEX` verifies signature, image
bytes, package and class before any Mini effect, installs on a **new**
application resource, and the broker creates the volume from the image. The
broker itself checks only the SHA-256 its requester names, so the image is
treated as untrusted bytes: it is never mounted (see `create-from` below).

Deployment: install `mini-spk-broker.service` and `/etc/mini/spk-broker.json`
(root 0600; `mini-spk-broker.example.json`), the binaries root-owned, the app
UID pool accounts (nologin, primary group not the operator's). The broker
renders the supervisor template and `<prefix>-grains.slice` itself at start.

The package root is bound read-only from an open directory fd; a separate
preallocated ext4 loop filesystem is mounted at `/var`; `/tmp` is a size-limited
tmpfs. A new user, PID, IPC, UTS, cgroup and network namespace exposes loopback
but no host interface or route. The app runs with every capability dropped
(`--cap-drop ALL`), cannot create a further user namespace (`--disable-userns`),
and runs under the seccomp allowlist `native/spk-host/seccomp/resident-web.policy`
(compiled in-tree and passed as `--seccomp 6`). bubblewrap consumes and closes
the image, `/var` and seccomp descriptors before exec, so the app holds only
fds 0-3: `/dev/null`, its private output pipe on 1 and 2, and the fd-3 socket.
Its stdout/stderr go to a new per-generation file
`JOURNAL_DIR/app-output-rRESOURCE-gGENERATION.log` (16 MiB kept, the rest
counted and dropped), never to the resident service's own streams.
`scripts/spk-platform/sandbox-floor-audit.sh` re-measures all of this inside a
resident sandbox. The jailed root does not bind host `/usr`, Mini
keys, Store, control sockets or resolver configuration. The manifest's command
argv and ordered environment are validated before use. First creation uses the
selected `action.command`; wake uses `continueCommand`. A failed first creation
is uncertain until Mini and the app's retained state reconcile; it must not be
blindly repeated.

`spk-var-volume --root GRAINS create STORE RESOURCE_ID APP_UID SIZE_MIB SOURCE_VOLUME_HEX`
(called only by the broker) provisions a root-private backing image
`GRAINS/volumes/STORE-RESOURCE_ID.ext4`, mounts it at the task-traversable
`GRAINS/vars/STORE-RESOURCE_ID`, and verifies the loop device, backing path,
size, owner and ext4 type; `create-from` makes and mounts the same fresh
filesystem and then copies the import into it: the import must be exactly the
class size, and e2fsprogs (`blkid -p`, `e2fsck -fn`, `debugfs rdump`) parse it
in userspace as the application uid with no privileges, so the kernel never
mounts operator bytes. Device nodes, sockets and FIFOs are dropped, symlinks
are recreated unfollowed, and the copy is bounded by the fresh filesystem;
per-entry copy errors go to `GRAINS/attest/STORE-RESOURCE_ID.import.log`
(`deploy/spk-host/tests/var-volume-import-untrusted.sh`). `verify`
only checks an existing mount. Sizes are 64 MiB–16 GiB. `SOURCE_VOLUME_HEX` is
the exact 32-byte lowercase-hex volume identity authored by Mini for the
deployment domain and application; an arbitrary identifier or an empty
directory is not launch authority.

Before creating volumes, provision `/etc/minidregg/spk/host-identity` as a
root-owned mode-0600 regular file with exactly two lines:

```text
deployment_id=<64 lowercase hexadecimal characters>
host_id=<64 lowercase hexadecimal characters>
```

Creation records them, the Mini source volume ID, app UID and quota in
`GRAINS/volumes/STORE-RESOURCE_ID.conf`. Replacing or moving an established
volume requires a separate migration contract; do not rewrite its registration
to make a mismatch disappear.

`spk-var-volume --root GRAINS attest STORE RESOURCE_ID` reads that protected
registration and publishes `GRAINS/attest/STORE-RESOURCE_ID.witness` (root
0644; the witness tag stays `DREGG/SPK-VAR-CUSTODY/v1`, which Mini checks, and
its `backing=`/`mount=` lines carry the Store-keyed paths). It checks the
backing filesystem's UUID or ZFS dataset GUID, backing inode/size, ext4 image
UUID and mounted volume. The resident checks the witness against its
Mini-selected volume, the deployment/host pins and the broker-given grains root
and Store key, then checks the open mount before launch. A witness is physical
custody evidence, not a Mini permit.

See the [bounded volume evidence](../../docs/evidence/2026-09-27-spk-volume-custody/README.md)
for isolated physical checks. Source-qualified v3 BEGIN/claim/completion and
the integrated resident launch remain required; these provisioning commands
do not establish a running Mini-authorized grain.

The initial Linux namespace qualification used persvati. Its probe on Linux
6.17/systemd 257/bubblewrap 0.11 confirmed a private netns with UP loopback and
no routes, fd 3 duplex through bubblewrap under a transient unit with
`NoNewPrivileges=yes`, fd-backed root and `/var` mounts, read-only root, and
tmpfs `/tmp`. Direct `unshare -Urn` was denied by Ubuntu AppArmor; it is not a
valid proxy for the tested bubblewrap route. That probe does not establish
current host capacity. Recheck disk and resource budgets before provisioning;
hbox storage work should use `/tank`.

The retained real sample SPK with SHA-256
`5830d70137cdae158118884da8790870fb095a07996cfe7708fb0155df45232e`
was parsed and materialized in private persvati scratch without execution:
2,089 regular files, 21 symlinks, 462 directories, and no writable file or
directory in the published root. Duplicate installation refused without a
staging residue. This qualifies archive extraction only. It does not establish
that the app launches, that its bridge speaks the pinned Cap'n Proto schema,
that Mini admission is wired, or that the sandbox equals Sandstorm's seccomp
profile. This early extraction checkpoint did not run a third-party process.
That early sample extraction used a private path-override build before the
bounded `spk-ingest` wrapper existed; repeat it under the bounded unit after
the hardened Bread parser revision is pinned.

Before arbitrary package execution: qualify the quota-backed `/var` mount,
source-review the system unit and executable/config pin guard, inspect the
post-bubblewrap syscall/namespace boundary, connect the typed fd 3 RPC server,
and enforce Mini admission and uncertain-delivery reconciliation. App access
must stay behind the Mini-authorized broker; loopback web/database sockets must
not be exposed to the host network.
