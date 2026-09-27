# 776ba59 Linux helpers (2026-09-27)

These immutable Persvati executables were built from the full committed
`git archive 776ba59` at `/tmp/minidregg-776ba59-source.tar`, SHA-256
`d8fc3c53c9f1ef0cc2ba67d53674d5afa4d6d08e102f526b8c3ba52de3111798`.
The private source cut is `/tmp/minidregg-776ba59-helpers-source`. The
[source manifest](source-sha256.txt) records 30 files across the three crates
and the SQLite test fixtures, SHA-256
`568717989b3258b78814e3b64095686c0d675b6c78877382d7c842bc55d90331`.
Each crate used its committed lockfile, a separate private Cargo target,
`CARGO_BUILD_JOBS=2`, and a release build.

| Program | Immutable Persvati path | SHA-256 | Focused tests |
| --- | --- | --- | --- |
| Mini | `/tmp/minidregg-776ba59-helpers-evidence/bin/mini` | `5597e6cfc7809460b773799795ffefb206546e8925f94d48a1e68e119eff2dfd` | 49/49 |
| SQLite store | `/tmp/minidregg-776ba59-helpers-evidence/bin/minidregg-link-sqlite-store` | `ad03aede839259c1884383fc97f141a3fe106ba2f2cbae0df6f7916676fe193f` | 10/10 |
| Credential verifier | `/tmp/minidregg-776ba59-helpers-evidence/bin/minidregg-credential-signature-verifier` | `c84004123ae6f02654cb6749e4105e351199618aaefce5755a2a0bb10bd0892b` | 10/10 |

The [binary manifest](binary-sha256.txt) and [readback check](binary-check.log)
show all three installed copies byte-verified. The adjacent build and nextest
logs retain actual verdicts. These helpers are ready for a fresh private
selected-release fixture after its separate source-matched Host link; they
were not installed over any live service.
