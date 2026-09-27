# Composite grain birth native build (2026-09-27 UTC)

This is the immutable first composite route image from the source cut at
`fbd4401` (composite route `fa7d4c4`, qualified fn prefix `4089f24`, and
optional genesis `grainBirthTariff` authoring `fbd4401`). The Mac and Linux
builds each compiled all 181 native Host source modules and linked 3,114
response objects. Their source manifests are byte-identical (SHA-256
`d856d411b8e066ecc7cccaf09852c4909daa67fbf78060da2952ff1ad5a5e042`);
the four recorded output artifacts on each machine passed their hash check.
The no-argument `usage_exit=1` is expected.

The Mac executable is
`/tmp/minidregg-overnight-20260926/minidregg-host-provider-composite`,
SHA-256 `ea7d99c5765612cd29f2d4a5b21cf5ea084025ec25da49f67d1fbe89aa96495a`.
The Linux executable is
`/home/ember/build/minidregg-overnight-20260926/evidence/minidregg-host-provider-composite`,
SHA-256 `c6c21859e54b3ef96e0ff60b345ef705a6a3b3e359345a26894fd054aa248c5a`.
The [Mac](mac-manifest.txt) and [Linux](linux-manifest.txt) manifests carry
the exact source roots, toolchains, module counts, and artifact hashes.

This is a source and build checkpoint, not deployment or signed grain-birth
acceptance. It predates the later-height `birth.height` fix in `Host.Json`
(`f608c3b`) and the stable fn control binding fix in `Host.Main` (`2b6db7d`).
The first isolated r1/r2 composite fixture was diagnostic; fresh acceptance
requires a separate source-matched image containing those fixes.
