# Combined UInt64 cSHAKE and exact-readback session

The combined certified Linux host SHA-256
`d413081bb6c6ac1c0699b5fdc22cf3a13fb87930ff49ac147ae994e2c364e7a3`
uses `Compiler/Sp800185Cshake256Core.lean` SHA-256 `aa4e9294…` and the same
five exact-readback module bytes as the pre-UInt64 exact host. The certified
Mac counterpart has SHA-256
`a7dd4605ef80d49a3cc9a9e5eeaed5cb8fc4bac4554ce7ea7562475aaa70717f`.
The full Core and changed-module hashes and both build manifests are copied
here as `u64-exact-*-source-sha256.txt`, `u64-exact-core-source-sha256.txt`,
and `u64-exact-*-build-manifest.txt`.

The same retained 734,222-byte signed B call (SHA-256 `59b6a3ac…`) was
submitted through a warmed persistent session on a fresh private copy of
the accepted-one SQLite image (SHA-256 `8eff8dd1…`). The combined host took
**23.22 seconds** of client wall time. Its 132-byte Outcome SHA-256
`caf4009a…` and final SQLite SHA-256 `0066f07f…` match the earlier certified
persistent runs byte-for-byte. Those runs took 172.92 seconds before exact
readback and 96.55 seconds with exact readback and the old cSHAKE core.
These are three single-case measurements on private copies under shared
load, not a general latency bound. The bounded time and exact input/output
SHA records are `u64-exact-linux-retry.time`,
`u64-exact-linux-input-sha256.txt`, and
`u64-exact-linux-output-sha256.txt`; the full private case remains at
`/tmp/minidregg-large-b-profile-20260926/session-u64-exact-v1/` on Persvati.

The combined Mac host passed the same source-owned four-case physical
[`exact-readback-session.sh`](../../../scripts/overnight-tests/exact-readback-session.sh)
probe (script SHA-256 `8d9728e4…`) on fresh private Stores. Normal CAS,
lost successful CAS reply, failed first post-CAS readback, and a valid
concurrent suffix produced the expected typed outcomes. The original
four-field receipt stayed exact, while the later suffix left the Store at
the byte-exact count-three image. The bounded result and physical-image
SHA records are `u64-exact-physical-results.jsonl` and
`u64-exact-physical-sha256.txt`; the full case directory is
`/tmp/minidregg-u64-exact-readback-physical-20260926/`.

The same combined Mac image also passed the real native
[`replay-poison.sh`](../../../scripts/overnight-tests/replay-poison.sh)
driver on another fresh private fixture. Replacing the live accepted image
with a valid earlier prefix was refused as rollback at entry one; replacing
it with a valid same-height different branch was refused as a changed
accepted-record prefix at entry two. Both sessions closed and kept the next
frame closed. Bounded logs `u64-exact-rollback.log` (SHA-256 `2299a1c4…`)
and `u64-exact-same-height-fork.log` (`7c8e793e…`) are copied here; their
bytes match the pre-UInt64 exact-host poison logs. The full private driver
directory is `/tmp/minidregg-u64-exact-session-poison-20260926/`.
