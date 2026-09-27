# SPK launch descriptor v2: pure source checkpoint

`Kernel/ApplicationSpkLaunchDescriptor.lean` (SHA-256
`fa25ebfa13ac9d64c4e95b9e679b0e15350854690e8ea9410f7bbfae2ebf1d4a`)
and `Host/ApplicationSpkLaunchDescriptorAuthoring.lean` (SHA-256
`8b18b03a9add550a28b1c521dbe08f9efd9f5d980404a2735df6c91fb0cc6e03`)
passed separate `LEAN_NUM_THREADS=2 lake env lean -o ...` direct checks in
`/tank/dregg-build/minidregg-55d3868-launch-v2-narrow` on hbox. Both commands
exited 0 with empty diagnostics in `launch-descriptor.log` and
`launch-authoring.log`. That isolated overlay imported the immutable qualified
module-183 OLean prefix from the exact `55d3868` source archive; the prefix
manifest is SHA-256
`3d7d2f86d9c8649b44a94d13d10337af42ea0b21699d90f94a6c2916e80a4e7f`.
Only this pure descriptor and helper are source-qualified by these checks.

`source.json` (SHA-256
`7902b3bf6e87d1daa0826d625987f9e72cb9f148dfe250e7c4066652d76770d5`)
contains exact ordered GitWeb signed command bytes projected from a verified
SPK parse by the physical Rust qualifier, plus previously source-authored v1
package identity bytes. This is a mixed-provenance authoring fixture, not the
later integrated one-parse native gate. The raw SPK was SHA-256
`2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa`.

To repeat the bounded Lean fixture from a source/OLean-qualified overlay,
copy `source.json` there as `launch-source.json` and run:

```sh
LEAN_NUM_THREADS=2 lake env lean --run docs/evidence/2026-09-27-spk-launch-lean-v2/Check.lean
```

The retained `check.log` records exit 0 and root
`89066044197087243500897137644433855781716276082669749278782223953933431354679`.
`descriptor.bin` is 489 canonical bytes (SHA-256
`d5cc3190f8b3fe35209a41d8e2fec181512ffad4482b68085ba9ec8cac723419`);
`inspect.json` is the source-owned inspection (SHA-256
`93de52fd08090c821d88c16a42e87846c8a707a054ea0796a32966d59e819448`).
The executable check verifies the round-trip root/type and refuses an empty
source object and truncated descriptor. The inspector preserves one signed
create action with `start.sh` and the signed `continue.sh` command, retaining
ordered argv and environment bytes.

The additive `Host/Json.lean` author/inspect arms (whole source SHA-256
`daef81cee11fac18001a46caafe8a932522353959894b59f2839e04180aa7038`)
then passed a direct Lean check against the exact immutable completed
module-292 prefix (manifest SHA-256
`0c0b8fd0aedf4f97650d3ad4d369629e955943fd472c0ec089eb4de0f017d1cd`).
`Host.Json.log` (SHA-256
`616480c41cbfd5457524c926373cbc617422864137a7b70f11f011005bccb31d`)
has existing unrelated policy proof warnings and axiom reports, with no error.
`CheckRoute.lean` (SHA-256
`19bae840939f922bfd48dfa4dc667183b55a3ebdac6ab2b3540287131384abdd`)
ran through the actual `Host.Json.parse`, `author`, and `inspect` functions:

```sh
LEAN_NUM_THREADS=2 lake env lean --run docs/evidence/2026-09-27-spk-launch-lean-v2/CheckRoute.lean
```

Run this from the repository root after building the named modules; it reads
the retained evidence files directly from this directory.

`route.log` (SHA-256
`305d7aa9078715a520f8b1a1a47407f90a43f219d4e4ed5e049f03587aa3bfb8`)
records exit 0: author and inspect reproduced the retained bytes and JSON
exactly; duplicate JSON keys and a wrong descriptor frame were refused.
These checks are source-only: no new native Host was linked, and no Store, app
birth, launch, lifecycle permit, or resident process is established.
