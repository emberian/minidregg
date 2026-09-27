# Stable SPK volume custody, bounded component check

2026-09-27. This cut adds a root-owned physical attestation for a fresh SPK
application volume. It does not select create versus continue, launch an app,
submit a Mini lifecycle event, or install/enable the service unit. Those steps
still require the source-qualified v3 BEGIN/claim/completion routes.

`spk-var-volume create` now requires the exact source volume ID as 32-byte
lowercase hex. It stores that ID with the deployment/host IDs, app UID and
quota in a root-only per-resource registration. `attest RESOURCE` accepts no
caller-selected path, UID or size. It rechecks that immutable registration,
loop BACK-FILE, ext4 image UUID, root/app ownership, quota, and a stable
backing-filesystem identity before and after publishing a root-owned witness.
The witness omits loop number, device number, PID and service invocation, so
same-host remounts produce the same bytes. A changed deployment identity
refuses the old volume. The Rust consumer reads the fixed root-owned handoff,
requires fresh metadata and source-pinned IDs, and rechecks the opened `/var`
directory against the path before launch. Mini's `Custody` binds the exact
witness bytes but cannot independently verify the filesystem facts.

The backing identity is tagged `ext4:<UUID>`, `btrfs:<UUID>`, or `zfs:<dataset
GUID>`. A root helper on hbox observed the actual ZFS bind source
`tank[/chreatures/...]`; it resolves the dataset GUID from `tank`, then pins
the backing inode/size, fixed path and ext4 image UUID. No `st_dev` enters the
stable witness. A cross-host move, image replacement, new deployment, or
changed backing identity needs an explicit migration contract.

| Owned source | SHA-256 |
| --- | --- |
| `deploy/spk-host/spk-var-volume` | `c9c03020be2ba9029cf7193c3f63047d2bea295c710c4774c6c81a9109d4f13b` |
| `deploy/spk-host/mini-spk-volume-attest@.service` | `5fbcc32fdd9154524e50fd984af219bcc3f72aaea762e61b8a9772373242dd49` |
| `native/spk-host/src/volume_custody.rs` | `8439400ba4ed2a94c5cd43c07bd0a83e5fe1bfd039bb68ebf920a34b804c1807` |

The shared `lib.rs` module declaration was SHA-256
`82b03a9f5d59b555d23444f12a55f7533654b5230b195c1535bf9d6ebce106e9`
in the Rust test snapshot. That snapshot also included separately owned
`launch_descriptor_native.rs` SHA `83c7466c`, `install_service.rs` SHA
`f071c753`, `install_v3.rs` SHA `175a7faf`, and `descriptor_native.rs` SHA
`7b604fea`; no claim of v3 native admission follows from their compilation.

The final script SHA above was run by the fresh concurrent-create fixture;
its `attest` action also checked the winner. The earlier remount and changed
deployment-ID log measured a prior script cut. It remains evidence for those
observed behaviors, not an exact-source rerun of the final lock change. Both
fixtures used private hbox mount namespaces with a ZFS-backed image
bind-mounted at the production fixed path. The root
transient units were capped at 512 MiB, 100% CPU, 64 tasks and 300 seconds.
No app process or public listener ran, and the host mountpoints and loop
devices were absent after each unit. Resource 991025 retained a synthetic
source volume ID only for this physical test. Its witness was byte-identical
after an unmount/remount, and a changed deployment identity refused. Resource
991026 ran two simultaneous `create` calls under one resource lock: one
succeeded, one refused, and the final image/config each had link count one.
The earlier 991024 first attempt is retained as historical evidence of the
ZFS bind-source form; it was not replayed or adopted by the final profile.

| Check | Result |
| --- | --- |
| [Attestation/remount log](attest-r4.log) | PASS, root unit exited 0; peak 5.8 MiB |
| [Concurrent create log](race-r1.log) | PASS, root unit exited 0; peak 10.1 MiB |
| [Systemd handoff log](systemd-handoff-r3.log) | PASS, two concurrent root oneshots; both witnesses survived each unit stopping |
| [Rust nextest log](rust-r3.log) | 8/8 focused tests passed, 106 skipped; 4 GiB/2-job hbox unit, 419.6 MiB peak |
| [Strict Clippy log](clippy-r1.log) | `--locked --all-targets -- -D warnings` passed; 478.9 MiB peak |
| `bash -n`, `shellcheck`, `rustfmt --check`, `git diff --check` | PASS |
| `systemd-analyze verify` on a scratch unit with ExecStart pointed at the root-owned test copy | PASS; production unit/executable not installed |

The attestation unit uses `RuntimeDirectoryPreserve=yes`. The separate
[handoff lifecycle fixture](run-systemd-handoff-hbox.sh) exercised the same
`Type=oneshot`, `RuntimeDirectory` and preservation properties under actual
systemd: after one shared-directory instance stopped, its witness and the
other instance's witness were both present; both remained after the second
stopped. The fixture used a separate `/run/mini-spk-volume-handoff-check-*`
directory, removed it afterward, and did not install the production unit.

The retained [ZFS witness](zfs-witness.txt) is from the root test fixture, not
an accepted Mini app. `spk-var-volume` and the fixed unit must be installed
under protected root paths and invoked by the resident service's START
preflight before `read_attested_volume` may qualify a real launch. The current
resident START remains fail-closed pending exact v3 source action selection,
volume comparison, and physical completion.

The subsequent resident FD5 seam in `native/spk-host/src/resident_launch.rs`
(SHA-256 `bfcc138cf6a354a4b4e448cdd12b902f13cffbf3c77997c63e1d6947089cf85b`)
compares the retained witness against the exact preopened `/var` directory and
rechecks the same handoff immediately before one-shot spawn. Its bounded
[Linux Clippy check](resident-fd5-clippy-r2.log) passed against a private hbox
snapshot with this file copied byte-for-byte (2 jobs, 4 GiB cap, 393.6 MiB
peak). No v3 Mini claim or app launch was run, and this physical comparison
does not by itself grant START authority.

The next staged `resident_service.rs` config cut (SHA-256
`029c4efcf8ca107d8abef215fafd984ac4ffcccfadac24e769c008577b7a1145`)
requires protected, canonical `deploymentId` and `hostId` pins for the future
root-witness comparison. It still refuses START before opening the Journal or
calling Mini. The [focused resident config test](resident-config-v3-r1.log)
passed 1/1 on hbox (122 skipped, 4 GiB/2-job cap), and
[strict all-targets Clippy](resident-config-clippy-r1.log) passed on the same
copied source. No volume ID was inferred by Rust; the source v3 inspector must
provide lowercase hex of Mini's exact 32-byte little-endian digest before
the physical START join can proceed.
