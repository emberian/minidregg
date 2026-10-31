# Package volumes: what the helper guarantees

Present-state statement for the per-grain `/var` of an SPK application. Written before the
implementation; the code and `tests` are answerable to it. Replaces the loop-mounted ext4 image
design (`spk-var-volume`, deleted): a loop device cannot be had in a user namespace or in most
containers, and a container's root filesystem has no UUID for the old witness to name.

## The object

A **volume** is one directory, `GRAINS_ROOT/vars/<store>-<resource>`, on a host ext4 or xfs
filesystem mounted with **project quotas** (`prjquota`). It carries:

* a **project id** `P` (kernel inode attribute `fsx_projid`, with `FS_XFLAG_PROJINHERIT` set on
  the directory, so everything created below it belongs to `P`);
* a **hard and soft block limit** and an **inode limit** on `P` equal to the class size
  (`quota_bytes`, `quota_bytes / 16384` inodes: the ratio `mkfs.ext4` used for the old images).

The directory is bind-mounted into the grain's sandbox as `/var` (the sandbox already receives it
as an open directory descriptor; nothing about the launch changes). There is no image, no loop
device, no per-volume mount and no filesystem UUID anywhere in the design.

The helper is the only code that sets `P` and the limits. It is the root-owned, sudo-admitted,
registry-checked one-shot `mini-spk-volume-helper`; `spk-var-volume` (bash) no longer exists.

## Environment requirement (checked, refused by name)

The grains root must lie on ext4 or xfs with project quota enabled, and the helper needs the
privilege to change a project id and a quota (`CAP_SYS_ADMIN`/`CAP_FOWNER` in the init user
namespace: root on a host, in a microVM, or in a container run with those capabilities). Linux
5.14 or newer (`quotactl_fd`: no block-device node is needed, which a container lacks).

* Host or microVM: put `/var/lib/mini-spk-worlds` on an ext4 made with `-O quota,project` and
  mounted `prjquota`, or an xfs mounted `prjquota`.
* Container: bind-mount such a host directory at `/var/lib/mini-spk-worlds`.
* The overlay root filesystem of a container does not support project quotas. The helper refuses
  with `volume-helper: grains root is on <fstype>, which has no project quota: ...` and names the
  fix. It never falls back to an unbounded directory.

## What it guarantees

**G1 Size bound.** For every registered volume, the kernel refuses (`EDQUOT`) any write by any
process that would take the blocks charged to `P` past `quota_bytes`, or the inodes past the
inode limit. `verify` re-reads the limit from the kernel (`Q_GETQUOTA`) and compares it exactly;
the resident re-checks it unprivileged at every launch from `statfs` of the open `/var`
descriptor (an inherit-project directory reports the project limit as the filesystem size), and
refuses a `/var` whose reported size is zero or exceeds the class bound.

**G2 Isolation between grains.** Each volume has its own project id, never shared: `create`
claims `P` under a host-wide lock and refuses an id that the kernel shows in use (non-zero usage
or any limit) and one already registered. A hard link or rename between two project trees fails
`EXDEV` in the kernel, so no grain's data can be linked into another's quota. The directory is
owned by the grain's registered uid, mode 0700, and the registered uid ranges of different
grains do not overlap; a grain sees only its own directory through its own descriptor.

**G3 No symlink escapes.** Every host-side step on a volume is relative to a descriptor and
`O_NOFOLLOW`: the helper never resolves a name inside a grain-written tree. Import recreates
symlinks and never follows them; ownership repair is `lchown`; destroy unlinks, never follows;
export hands the tree to `mke2fs -d` running as the grain's uid with no privileges, which stores
symlinks as symlinks. A grain-planted symlink, hard link, FIFO or device-like entry cannot make
the helper read, write, chown or delete anything outside the volume.

**G4 Custody keyed to project and directory.** The witness the resident checks
(`DREGG/SPK-VAR-CUSTODY/v1+projdir`, below) names the deployment, host, resource, volume id,
uid, quota, **project id**, filesystem type and the **directory inode and path**; at launch the
resident compares its open `/var` descriptor against the path (device and inode) and against the
witness's inode, and requires `statfs` of it to report a size below its parent filesystem's and within
the class bound (an inherit-project directory reports its project limit). The resident runs as the
operator and cannot open the app-private directory to read the project id itself; the helper, as root,
set and verified it, and the inode pin means a replaced or moved directory does not match. A directory
re-projected to a looser limit changes the reported size and is refused. The witness is root-written, 0644, root-owned ancestors, fresh within 120 s.

**G5 Clean teardown.** `destroy` removes the tree (descriptor-relative, no-follow), then clears
the project limit, then removes the registration and witness, in an order such that a crash
leaves either a complete volume or a registration-less leftover that `create` refuses to
overwrite and `destroy` finishes. A failed `create` removes what it made. After a world is torn
down no directory, project limit or registration remains (`removal_assertions`).

**G6 Capture consistency.** `freeze` (export and backup) captures a stopped volume exactly. A
running volume is captured with the app's cgroups frozen (`cgroup.freeze`) for the duration of
the copy, behind a durable pending file so that a killed helper's next run thaws exactly those
cgroups. The copy is checked: the tree fingerprint (entry count, bytes, newest ctime) before and
after must match, else the capture is refused. This replaces `FIFREEZE` of the private
filesystem, which a shared filesystem cannot be given.

**G7 Import is never trusted.** An imported `var.ext4` is parsed in userspace by e2fsprogs as the
grain's uid (`blkid`, `e2fsck -fn`, `debugfs rdump`); nothing is mounted from operator bytes
(there is no mount at all). The copy lands inside the quota; a tree that does not fit fails with
`EDQUOT` and the half-made volume is removed.

## The custodian: when the helper cannot set a project id itself

The kernel changes a project id and a quota limit only in the initial user namespace. A container
run with a user namespace (`systemd-nspawn -U`) cannot, whatever it has bound. For that case the
work the kernel reserves is done by a small root service on the host, and the helper in the container
asks it. One code path chooses: the registry's optional `custodianSocket` names the socket; absent,
the helper does everything itself as above (hbox, plain installs).

`spk-host volume-custodian ROOT SOCKET UID_BASE UID_LIMIT SOCKET_GID`, unit
`deploy/spk-host/mini-volume-custodian.service` (a template: `deploy/spk-host/install-volume-custodian` writes the literal ROOT into it, since systemd does not expand environment variables in `ReadWritePaths=`). `ROOT` is a host directory on ext4/xfs with
`prjquota`; its volumes are `ROOT/vars/<id>`, where `<id>` is `<store>-<resource>`. The container
sees `ROOT/vars` bound at `GRAINS_ROOT/vars`. The container's uid space starts at `UID_BASE` on the
host (the container's root), `UID_LIMIT` wide; a request names the grain's uid inside the container
and the custodian adds the base.

Request, one line, then one reply line (`MINI-VOLUME/1`, any other version is `bad-version`):

```
MINI-VOLUME/1 create <ID> <SIZE_MIB> <APP_UID>   ->  OK project=P bytes=B inodes=I
MINI-VOLUME/1 usage <ID>                         ->  OK project= uid= inode= bhard_kib= bsoft_kib= ihard= isoft= cur_bytes= cur_inodes=
MINI-VOLUME/1 destroy <ID>                       ->  OK removed=0|1
                                                 or  REFUSED <name> <text>
```

**C1 It touches only its root.** Every path is `ROOT/vars/<ID>` reached by `openat` from a descriptor
opened at start, `O_NOFOLLOW`; `<ID>` is two canonical fields (16 lower-case hex, a decimal), so it
cannot hold a `/`, a `..` or any other byte. Nothing else from a caller reaches a path: the request
has no path, no command and no uid outside `1..UID_LIMIT`.
**C2 A request cannot name another grain's directory.** `usage` and `destroy` refuse (`not-a-volume`)
any name that is not a plain directory on `vars`' filesystem, owned inside the container's uid range,
carrying a custodian project id with inheritance. A directory the custodian did not make is never
emptied or removed.
**C3 Limits come first.** `create` makes the directory 0700 owned by root, sets its project id and
hard block and inode limits (`SIZE_MIB`, 64..=16384, and `bytes/16384` inodes), and only then gives it
to the grain's uid. A project id is claimed under one lock, from a deterministic probe sequence, and
only if the kernel shows it unused. A failure removes everything the call made.
**C4 Destroy is idempotent and leaves nothing.** Contents, then the limit, then the name, in that
order; an absent volume answers `removed=0`; a destroy cut short is finished by running it again.
**C5 Refusals are named:** `bad-version`, `bad-request`, `bad-id`, `bad-size`, `bad-uid`, `exists`,
`absent`, `not-a-volume`, `no-project-id`, `kernel` (the OS error follows). The custodian refuses to
start unless it is root in the initial user namespace and `ROOT` has project quota.
**C6 Access** is the socket's mode 0660 and group `SOCKET_GID`; the directory holding it is 0755 root.

What stays in the container: the registration, the witness, import into the directory, freeze and
export. The helper's `verify` re-reads the project from the directory (any namespace can) and the
limits from `usage`, and compares them exactly as before. Not guaranteed: a compromised container
root can still ask the custodian to destroy any volume it can name, and can write a witness; the
resident re-checks the directory's inode and reported size at every launch.

## What it does not guarantee

* Not a performance partition: grains share the host filesystem's journal and IO.
* The size bound is on blocks and inodes charged to `P`. Metadata outside the project
  (e.g. directory growth is charged; the filesystem's own tables are not) is not counted.
* Soft state: the project id of a file moved in from outside the tree is the tree's (kernel
  `PROJINHERIT` rules); a grain cannot change it (no `CAP_SYS_ADMIN` in the init namespace).
* xfs/ext4 only. zfs is refused by name.

## Witness `DREGG/SPK-VAR-CUSTODY/v1+projdir`

Eleven newline-terminated lines, in this order:

```
DREGG/SPK-VAR-CUSTODY/v1+projdir
deployment_id=<64 hex>
host_id=<64 hex>
resource=<decimal>
volume_id=<64 hex>
app_uid=<decimal>
quota_bytes=<decimal>
project_id=<decimal>
fs_type=ext4|xfs
directory_inode=<decimal>
directory=<GRAINS_ROOT/vars/<store>-<resource>>
```

The Lean kernel (`Kernel/ApplicationLifecycleLaunchBinding.lean`, `Custody.validFor`) treats the
witness as opaque bytes and checks only that it begins with `DREGG/SPK-VAR-CUSTODY/v1`; this
layout begins with exactly that prefix, so no Lean change is needed to land it. OWED to the next
Lean batch: rename the frame (and `spk_var_custody_v1` in `Compiler/PersistedCodecTags.lean`) to
a `v2`, so the layout is named by the part Lean checks.

## Verbs (unchanged names; `Mount`/`Unmount` no longer mount)

| verb | effect |
|---|---|
| `create` | claim `P`, make the directory, set project and limits, optional import, register, attest |
| `mount` | verify and attest an existing registration (what a reboot used to need a loop mount for) |
| `unmount` | verify only; there is nothing to unmount |
| `freeze` | G6 capture to an operator-owned `var.ext4` export (format unchanged: ext4 image, manifest, signature) |
| `thaw` | recover a pending capture |
| `destroy` | G5 |
| `volumes-status` | inventory; `present` replaces `mounted` |

Exported images are sized `quota + 12.5% + 8 MiB` so that a full volume fits an ext4 image with
its own metadata; import accepts any image up to that size (older exports at exactly the class
size included).
