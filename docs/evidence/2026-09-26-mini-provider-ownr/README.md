# Mini catalog own-R native checkpoint (2026-09-27 UTC)

These independent source snapshots extend the certified
[provider-metering image](../2026-09-26-mini-provider-metering/README.md)
with committed `Host/FnInboxView.lean` from `6828c7f`, new
`Kernel/FnCatalogOwnRProgress.lean` from `b43083c`, and the exact accepted
carrier check in `Host/Main.lean` from `b5adace`. The relevant source SHA-256
values are `7c2f69f9c34a521b0ce0ea32eefc3fd2a741240ef60bc7cc35128610887afe7b`,
`8b57aea263479c805c202d7d0b061b12261a1019b7f94726dbd6dcf050830ae2`,
and `73de8760f0dfa26efef7b3f8345d4b558fc573ff774825e3ba4746c45be97ddd`,
respectively. Against the provider base, those are the only two changed
existing sources and one inserted native module. The base pins the earlier
`Kernel/ResourceBirthController.lean` blob as documented there; these images
do not claim to be the entire `b5adace` tree. No live Host, config, or Store
was replaced.

The new import changes the closure from 171 to **172** modules, so both
platforms used full bounded builds instead of bypassing the guarded suffix
builder. Every module compiled, 3,105 response objects linked, all 172
source hashes and four output artifacts reverified, and the Mac/Linux source
manifests are byte-identical (SHA-256
`f7b62df2a539f96e9b2fa3c0025ae0554bf3936bc976caa0bc8c1cf96479399e`).
The no-argument `usage_exit=1` is the expected usage response.

- Mac arm64: `/tmp/minidregg-overnight-20260926/minidregg-host-provider-ownr`,
  SHA-256 `031258701b7b9b51b218eb19186d0ca57c2468909bd0487913664a92388c0d0b`;
  [manifest](mac-manifest.txt), [source hashes](mac-source-sha256.txt),
  [artifact hashes](mac-artifact-sha256.txt), and [closure](mac-source-modules.txt).
- Linux x86-64: `/home/ember/build/minidregg-overnight-20260926/evidence/minidregg-host-provider-ownr`,
  SHA-256 `0c988147b0fc016f847a962e8fa0e68e24a2424d37ed999c41465cccb70d2c71`;
  [manifest](linux-manifest.txt), [source hashes](linux-source-sha256.txt),
  [artifact hashes](linux-artifact-sha256.txt), and [closure](linux-source-modules.txt).

This is a source-qualified build checkpoint. The fresh A catalog own-R
runtime gate is separate and has been assigned the immutable Mac binary.
No private Store, key, request, response, or executable is copied here.
