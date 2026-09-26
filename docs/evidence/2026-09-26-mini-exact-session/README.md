# Mini exact-readback native checkpoint (2026-09-26)

These are separate native images from the certified permission-tail hosts. The
source snapshots retain the pre-UInt64 cSHAKE core for a matched receiver
comparison. They overlay exactly five committed modules: `Compiler.DurableReceiverIO`
and `Kernel.DeclaredResourceController` from `5126264`, and `Kernel.NativeHostReplay`,
`Kernel.NativeHost` and `Host.Main` from `b25e9f8`. Their exact
hashes are in the [changed-source manifest](linux-changed-source-sha256.txt).
The Mac and Linux full 169-module source manifests are byte-identical. Foreign
working-tree edits, including `Compiler.lean`, are excluded.

The Linux x86-64 host is
`/home/ember/build/minidregg-overnight-20260926/evidence/minidregg-host-exact-session-2`,
SHA-256 `5c6bf412b2e77675874dc820ac6bd2f6d0b20c3f6752e5e4728228649d63daab`.
It was built in the independent
`/home/ember/build/minidregg-overnight-20260926/source-exact-session` snapshot
under a 32 GiB, 200% CPU systemd scope. The guarded suffix recipe validated the
permission-tail baseline binary and reusable artifacts, 117 unchanged earlier
modules, 47 unchanged later sources, and 2,933 package objects. It compiled
all 52 modules from `Compiler.DurableReceiverIO` through `Host.Main`, linked
3,102 response objects, and completed in 266 seconds. All 169 source and four
output artifact hashes were reverified. The no-argument `usage_exit=1` is the
expected CLI contract. See the [manifest](linux-manifest.txt),
[source hashes](linux-source-sha256.txt),
[artifact hashes](linux-artifact-sha256.txt),
[incremental validation](linux-incremental-validation.txt), and
[verification](linux-verify.log).

The Mac arm64 host is
`/tmp/minidregg-overnight-20260926/minidregg-host-exact-session-2`, SHA-256
`2ae1f166685e45e4fd1f3aeda49236af2a14e6719602bca89a7fe24d2fd406c0`.
It was built in independent `/tmp/minidregg-exact-session-native` with the same
guarded 52-module suffix and 3,102-object link. Its baseline/package/source
checks matched the Linux counts, the build completed in 439 seconds, and all
169 source and four artifact hashes were reverified. See the
[manifest](mac-manifest.txt), [source hashes](mac-source-sha256.txt),
[artifact hashes](mac-artifact-sha256.txt),
[incremental validation](mac-incremental-validation.txt), and
[verification](mac-verify.log).

The guarded builder is committed as `5355ecd`. Three private pre-Lean refusal
checks covered an undeclared changed source, a declared source before the
restart point, and a declared but unchanged source; see
[refusal checks](refusal-checks.txt). This checkpoint is a source-matched native
build, not a full umbrella or runtime acceptance claim. Separate private
receiver, replay-poison, and matched performance gates consume these immutable
hosts. No binary, private config, Store, key, or signed call is copied into this
evidence directory.
