# Combined UInt64 and exact-readback Mini native checkpoint (2026-09-26)

These Mac and Linux images combine the proved UInt64 cSHAKE core from `b609133`
with the five committed exact-readback source modules recorded in the
[changed-source manifest](linux-changed-source-sha256.txt). `Host.Main` includes
the grain-origin CLI permission repair. The combined full source manifest
differs from the separately certified [pre-UInt64 exact image](../2026-09-26-mini-exact-session/README.md)
only at `Compiler/Sp800185Cshake256Core.lean`: pre-UInt64 SHA-256 `c4c8aa4b…`
becomes proved UInt64 SHA-256
`aa4e9294eab4243590a51b3ecfbb54c7e613f6807a37b055800cc649437949c0`.
The Mac and Linux 169-module manifests are byte-identical. All source files
came from independent copied snapshots, excluding concurrent foreign
working-tree edits.

The Linux x86-64 host is
`/home/ember/build/minidregg-overnight-20260926/evidence/minidregg-host-u64-exact-session`,
SHA-256 `d413081bb6c6ac1c0699b5fdc22cf3a13fb87930ff49ac147ae994e2c364e7a3`.
Its snapshot is
`/home/ember/build/minidregg-overnight-20260926/source-u64-exact-session`.
It incrementally rebuilt all 52 modules from `Compiler.DurableReceiverIO`
through `Host.Main` against the certified [UInt64-only baseline](../2026-09-26-keccak-u64/README.md),
linked 3,102 response objects, and completed in 349 seconds under a bounded
32 GiB/200% CPU systemd scope. The guarded preflight revalidated the baseline
binary and reusable artifacts, 117 unchanged earlier modules, 47 unchanged
later sources, four declared later changes, and 2,933 package objects. All
169 source and four output artifact hashes were rechecked. The no-argument
`usage_exit=1` is expected. See the [manifest](linux-manifest.txt),
[source hashes](linux-source-sha256.txt),
[artifact hashes](linux-artifact-sha256.txt),
[incremental validation](linux-incremental-validation.txt), and
[verification](linux-verify.log).

The Mac arm64 host is
`/tmp/minidregg-overnight-20260926/minidregg-host-u64-exact-session`, SHA-256
`a7dd4605ef80d49a3cc9a9e5eeaed5cb8fc4bac4554ce7ea7562475aaa70717f`.
Its independent APFS snapshot is `/tmp/minidregg-u64-exact-session-native`.
The same guarded 52-module suffix and 3,102-object link completed in 387
seconds. The source, artifact, changed-source, and baseline-package checks
all passed, with the same source counts as Linux. See the
[manifest](mac-manifest.txt), [source hashes](mac-source-sha256.txt),
[artifact hashes](mac-artifact-sha256.txt),
[incremental validation](mac-incremental-validation.txt), and
[verification](mac-verify.log).

This directory certifies the native builds. The separate
[combined runtime evidence](../2026-09-26-grain-performance/u64-exact-session.md)
records four physical readback cases on fresh Mac Stores, rollback and
same-height fork poisoning, and a matched Linux persistent 734,222-byte call.
That call returned the exact 132-byte Outcome and final SQLite image in 23.22
seconds, versus 96.55 seconds on the standalone pre-UInt64 exact image and
172.92 seconds on the earlier persistent baseline; each timing is one run.
No binary, private config, Store, key, or signed call is copied into this
directory.
