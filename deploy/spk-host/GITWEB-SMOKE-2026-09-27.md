# Private signed GitWeb process qualification — 2026-09-27

This was one isolated persvati test of a real signed GitWeb SPK, outside Mini
application admission. No public listener, Mini Store, paid provider, or live
780x/9301/fn service was involved. The source-owned harness is
`native/spk-host/src/bin/gitweb-smoke.rs` SHA-256
`518cbe3e7fb66ce5de502dfe154a91625982f2f1fd53667d58ace1c2540f706a`;
its `Cargo.toml` and `Cargo.lock` are respectively
`1dec68a2278c2dd516101f276764e2d80ee4031796b34f05a089db934311e90d`
and `2fd7f108d990e53b743a332cf2f94e1a6131a1ac1618232aaa949877e577bf26`.
The bounded Linux release build and strict Clippy passed. The exact tested ELF,
`/opt/minidregg-gitweb-smoke-20260927/bin/gitweb-smoke`, hashes
`fb1c484e18ca73ce4ff24df40d1058a390c649b6d5a5b6b926761f51e8f3bac6`.
The prior scoped `spk-host` Nextest passed 3/3; the final harness-only changes
were release-built and Clippy-checked, not retested by Nextest.

The SPK SHA-256 is `2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa`,
app ID `6va4cjamc21j0znf5h5rrgnv0rpyvh1vaxurkrgknefvj0x63ash`, version 10.
The bounded ingester verified its signature and installed its root-owned,
read-only image at `/var/lib/minidregg/spk/packages/sha256-<SPK SHA>`; the
published manifest SHA-256 is
`9b50542eaedc7c7ec1c0ab89e4576f89b812be84662d4dc80e2df28d99a56424`.
Ingest unit `mini-spk-ingest-20260927045915-3649530.service` finished
`Result=success`, exit 0, peak 178.9 MiB. Dedicated locked UID 995
(`mini_spk_gitweb26`) owns only resource 991003's mounted 512 MiB ext4 `/var`;
the root-owned backing image is inaccessible in the jail. The mount is
`rw,nosuid,nodev,noatime` and remains mounted for review.

Create and wake ran in separate transient system units
`mini-spk-gitweb-991003-{create,wake}.service` with `User=mini_spk_gitweb26`,
`NoNewPrivileges=yes`, `PrivateNetwork=yes`, `KillMode=control-group`,
`MemoryMax=1G`, `TasksMax=64`, `CPUQuota=100%`, and `RuntimeMaxSec=300`.
`spawn_sandbox` used the signed ordered action command on create and the
signed `continueCommand` on wake; its fd 3 Unix socketpair connected the
packaged bridge to the typed `spk-rpc` supervisor. The image root was
read-only, `/tmp` tmpfs, and `/var` the same ext4 volume. The harness's
loopback Git-CLI HTTP adapter lived only in the outer unit's private network
namespace. The app's nginx/fcgiwrap listeners lived in its inner namespace.

Create completed successfully in 1.835 seconds, peak 162.4 MiB. One
developer smart-HTTP receive-pack POST returned 200 and installed commit
`27c7e7dbe3c66cc5d8381748d0b0e5fbae05bafc` in `/var/repo.git`.
Guest receive-pack **advertisement** returned 403. A guest smart-HTTP clone
fetched the exact source commit and README SHA-256
`fa2447c2dc837cb77e517024df9363e276bd12eae115190fc2dc2c3c95e32403`.
An owner WebSession GET returned HTML status 200, 5,418 bytes, and identified
the expected commit hash or its exact subject. The retained keyless
`docs/evidence/2026-09-27-spk-gitweb/create-unit.log` SHA-256 is
`27e134c8c09afc29056ed787b1389e6966171f8df24996db52da317fa0becc41`.
The bare repo's branch tip was independently read from the retained volume
before wake and matched the source commit. No second push was attempted.

Wake used the same volume and the exact retained expected commit as a CLI
argument. It completed successfully in 1.757 seconds, peak 162.1 MiB. Guest
receive-pack advertisement was again 403, smart-HTTP clone fetched the same
commit and README, and owner browser GET returned HTML 200 identifying that
commit hash or subject. The retained keyless
`docs/evidence/2026-09-27-spk-gitweb/wake-unit.log` SHA-256 is
`782937898224a01020c031795dc1aff7edeb80dff58183e7a2b4ab39fef0d0db`.
Afterward both units were inactive with MainPID 0 and empty ControlGroup;
the retained repo tip remained the exact commit. No host TCP listener on the
tested app/adapter ports or surviving app process was observed.

The physical result qualifies this one package's create, smart-HTTP push and
fetch, browser read, and same-volume wake path. It does not prove denial of a
malicious guest receive-pack POST, Mini-authorized deployment, general SPK
compatibility, or Sandstorm-equivalent syscall confinement.
