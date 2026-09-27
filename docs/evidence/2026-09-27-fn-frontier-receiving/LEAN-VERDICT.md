# Fn frontier source-only Lean gate

The seven modules in [LEAN-SOURCE-MANIFEST.txt](LEAN-SOURCE-MANIFEST.txt)
compiled serially with exit 0 and no Lean diagnostics. For each row, the
command was `LEAN_NUM_THREADS=2 lake env lean PATH.lean -o
.lake/build/lib/lean/PATH.olean`, run from the private hbox copy at
`/tank/dregg-build/minidregg-fn-frontier-narrow-20260927`. All seven final
`fn-*.log` files there have length zero. The initial plan and Main compiler
errors were corrected before this final pass; their earlier logs are not
included as verdicts.

The private source came from the exact 55d3868 source archive
`/tank/dregg-build/minidregg-55d3868-source.tar` (archive SHA-256 begins
`4ba1f55e`). Its imported 292-module OLean closure was ordinarily copied from
`/tank/dregg-build/minidregg-55d3868-evidence/prefix-292`, manifest SHA-256
`0c0b8fd0aedf4f97650d3ad4d369629e955943fd472c0ec089eb4de0f017d1cd`.
Copied `Host.Main.olean` matched the immutable prefix hash
`a8e587f659e254fa52efe8059c52a63a8044691bf6d5c578d9f680ce61d787da`;
the two copies had distinct inodes and link count one. Package OLeans were
read through a symlink; all generated OLeans remained private. The seven
source files were overlaid from their exact local hashes in manifest order.

This is a narrow Lean source/OLean check. It does not qualify a linked Host
binary or claim native event17/19 admission, fn POST, Mini receipt, or ACK.
The first three upper modules predated this lane and remain separately owned;
their direct compilation is included here solely as a required dependency
gate. The build seat was released after the final pass.
