# Current-birth Mini client (2026-09-27)

The immutable Persvati `mini` client at
`/tmp/minidregg-bd883d8-resource-client-evidence/bin/mini` has SHA-256
`29809a46e5cd64d49246ddcbb164012f993d7abd7eb623cafafe654a6ea7e1e7`.
It was built with `CARGO_BUILD_JOBS=2`, `--locked --release`, and a private
Cargo target from an exact `git archive bd883d8` of
`native/resource-client`, archive SHA-256
`5bb6de81c8144d9ab5770110034047be683eb6f3b12047d3bc3348adf317cd56`.
The [20-file source manifest](source-sha256.txt) has SHA-256
`57af3a56b3d20e8a10ef3f97837ea6d5295f6a3624d027e48f72dc6033d22d34`.

The [binary check](binary-check.log) passed, and focused
[`cargo nextest`](nextest.log) passed 56/56 tests. The [build log](build.log)
and [binary hash](binary-sha256.txt) retain the bounded evidence. The client
supports current-birth authoring for the pending op30/31 fixture; its
source-qualified Host image is a separate gate.
