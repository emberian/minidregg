# Mini provider metering native checkpoint (2026-09-27 UTC)

The independent source snapshots combine the exact committed `567fa58`
provider modules and audit with `2ef2192` `Host.Main` (op6 metering profile).
They do **not** claim to be the entire `2ef2192` tree: 170 of 171 native
sources match that commit, while `Kernel/ResourceBirthController.lean` remains
the prior `8056f9b` blob SHA-256
`ae96c1984fc369ba811785a677b9a228c59c70460712a1328d754a566fc57522`,
before the unrelated `a933651` composite refactor (the later commit has
SHA-256 `7b9b2b7b…`). The full source manifests pin this mixed closure
explicitly. Exact source SHA-256 values are recorded in the verification
logs. The base is the certified
[UInt64-plus-exact image](../2026-09-26-mini-u64-exact-session/README.md).
Concurrent foreign work, including new grain-birth and fn modules, was
excluded. Neither binary replaced a live Host or config.

The `Host.Main` native import closure grew from 169 to **171** modules:
`Kernel.ProviderMetering` is module 169, `Host.ProviderUsage` module 170,
and `Host.Main` module 171. The separate `Host.ProviderUsageAudit` is not
linked; it and the two new modules passed a narrow warm `lake build` check,
and the final op6 `Host.Main` passed a second check. A full bounded build was
used because the existing incremental suffix guard correctly requires an
unchanged import closure.

The Linux x86-64 executable is
`/home/ember/build/minidregg-overnight-20260926/evidence/minidregg-host-provider-metering-op6`,
SHA-256 `51f790fa55f734772c37330dc0ab7408f3438d4e168b74bd6432d0b1cdb111f6`.
The source snapshot is
`/home/ember/build/minidregg-overnight-20260926/source-provider-metering`.
The 32 GiB/200% CPU systemd scope compiled all 171 Lean modules with two
threads, linked 3,104 response objects with two C jobs, and completed in
799 seconds. The 2,933 package objects came from the pinned independent
snapshot. The no-argument `usage_exit=1` is expected. All 171 source and
four output artifact hashes were reverified. See the
[manifest](linux-manifest.txt), [source hashes](linux-source-sha256.txt),
[artifact hashes](linux-artifact-sha256.txt),
[closure](linux-source-modules.txt), and [verification](linux-verify.log).

The Mac arm64 executable is
`/tmp/minidregg-overnight-20260926/minidregg-host-provider-metering-op6`,
SHA-256 `b7a0dd64e20aa2bdf1dc60c151152cee866d526e131beb1cd97fb4a6ade4c412`.
Its independent source snapshot is `/tmp/minidregg-provider-metering-op6-native`.
The same 171-module/two-thread, 3,104-object/two-job build completed in
987 seconds. All 171 source and four artifact hashes were reverified; the
Mac and Linux full source manifests are byte-identical. See the
[manifest](mac-manifest.txt), [source hashes](mac-source-sha256.txt),
[artifact hashes](mac-artifact-sha256.txt),
[closure](mac-source-modules.txt), and [verification](mac-verify.log).

This is a source-qualified native build checkpoint. The private valid,
truncated, missing-usage, and over-reserve op19 semantic fixture is a
separate runtime gate. No private Store, key, request, response, or executable
is copied into this directory.
