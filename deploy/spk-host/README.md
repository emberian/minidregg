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
1 GiB memory cap, 120-second runtime cap, 16-task cap, no network, a read-only
host filesystem except the package store, and a SHA-pinned host executable.
The parser's 256 MiB decompressed-output cap is **not** a peak-memory bound:
the xz library can allocate an entire block before writing to the bounded
sink. The cgroup is therefore part of the ingest boundary. A killed or failed
unit is not an installed package.

The planned direct `mini-spk@RESOURCE.service` runs under one locked app UID and
starts `spk-host` as MainPID. The host creates an AF_UNIX stream socketpair in
that service, keeps the supervisor end for `native/spk-rpc`, and gives the
packaged bridge the other end on fd 3 through bubblewrap. The app, bridge and
its localhost database live in that service's cgroup. AgentGrain workers have
different units; a Hermes hard disconnect does not stop the shared app.

The package root is bound read-only from an open directory fd; a separate
preallocated ext4 loop filesystem is mounted at `/var`; `/tmp` is a size-limited
tmpfs. A new user, PID, IPC, UTS, cgroup and network namespace exposes loopback
but no host interface or route. The jailed root does not bind host `/usr`, Mini
keys, Store, control sockets or resolver configuration. The manifest's command
argv and ordered environment are validated before use. First creation uses the
selected `action.command`; wake uses `continueCommand`. A failed first creation
is uncertain until Mini and the app's retained state reconcile; it must not be
blindly repeated.

`spk-var-volume create RESOURCE_ID APP_UID SIZE_MIB` is a separate privileged,
explicit operator action. It provisions a root-private backing image under
`/var/lib/minidregg/spk/images`, mounts it at the task-traversable
`/var/lib/minidregg/spk/vars/RESOURCE_ID`, and verifies the loop device,
backing path, size, owner and ext4 type. `verify` only checks an existing mount.
Sizes are 64 MiB–16 GiB. No public port, key, account, unit start or automatic
enable is created by this helper. A system unit and lifecycle installer are not
yet installed.

Persvati is the selected Linux host. The harmless namespace probe on Linux
6.17/systemd 257/bubblewrap 0.11 confirmed a private netns with UP loopback and
no routes, fd 3 duplex through bubblewrap under a transient unit with
`NoNewPrivileges=yes`, fd-backed root and `/var` mounts, read-only root, and
tmpfs `/tmp`. Direct `unshare -Urn` was denied by Ubuntu AppArmor; it is not a
valid proxy for the tested bubblewrap route. Persvati had about 214 GiB free;
hbox `/tank` had about 3.4 GiB free and is not the persistent image lane.

The retained real sample SPK with SHA-256
`5830d70137cdae158118884da8790870fb095a07996cfe7708fb0155df45232e`
was parsed and materialized in private persvati scratch without execution:
2,089 regular files, 21 symlinks, 462 directories, and no writable file or
directory in the published root. Duplicate installation refused without a
staging residue. This qualifies archive extraction only. It does not establish
that the app launches, that its bridge speaks the pinned Cap'n Proto schema,
that Mini admission is wired, or that the sandbox equals Sandstorm's seccomp
profile. No third-party SPK process has been run by this lane.
That early sample extraction used a private path-override build before the
bounded `spk-ingest` wrapper existed; repeat it under the bounded unit after
the hardened Bread parser revision is pinned.

Before arbitrary package execution: qualify the quota-backed `/var` mount,
source-review the system unit and executable/config pin guard, inspect the
post-bubblewrap syscall/namespace boundary, connect the typed fd 3 RPC server,
and enforce Mini admission and uncertain-delivery reconciliation. App access
must stay behind the Mini-authorized broker; loopback web/database sockets must
not be exposed to the host network.
