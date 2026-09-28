# Fail-fast accepted lifetime grant inspection Host (2026-09-27)

This exact-source Linux image combines the accepted-grant ingress prefilter and the share-issue ticket digest projection from Mini commit `8c13c42`. Production Lean changes relative to the certified d48aa81 Host are only `Host/ApplicationAgentLifetimeGrantInspection.lean` SHA-256 `e6724dc608079ee1ec5711faabc95c7a9fe6c2b590188152928edc9e61ea3860` and `Host/ApplicationShareIssueGrainInspection.lean` SHA-256 `21af0707bf8d129d20e7d4ade9b681c7fb7dc6dd5c0cecf1af0ed5cbb7869975`. The committed archive `/home/ember/build/minidregg-8c13c42-source.tar` has SHA-256 `e9121524db5eaf31c2296bc374e43fea91e09ec6f240894989617341b08890ec`. All 353 production closure sources matched that archive byte-for-byte, and the whole tracked source-tree comparison found zero differences. The manifest's inherited `git_head=791a6d2c` is warm-cache metadata, not code provenance.

The guarded suffix build used an independent writable copy of the certified d48aa81 snapshot, restarting at `Host.ApplicationAgentLifetimeGrantInspection` (module 329) and declaring `Host.ApplicationShareIssueGrainInspection` (module 336) as the only other changed source. It checked 328 earlier modules, 23 later unchanged sources and 2,933 package objects, recompiled all 25 suffix Lean modules through `Host.Json` and `Host.Main`, then rebuilt native project C objects with two jobs. The bounded `minidregg-8c13c42-grant-host-r1.service` terminated successfully. Source SHA readback passed 353/353; output artifact readback 4/4; reusable artifact readback 10,211/10,211. The response contains 3,286 objects. The CLI usage probe exit 1 is expected without arguments.

Qualified ELF: `/home/ember/build/minidregg-8c13c42-evidence/minidregg-host-8c13c42-r1`, SHA-256 `370a9396c2109d1181d726361559f1f4a76ead1184a082bdacc4e23f22c648f9`. Manifest SHA-256 `f047f55651a64072f94a8bc9cb1d6ed399c812191afde8bf49c904d9ec904ac6`. A protected mode-0500 hbox copy is `/tank/dregg-build/minidregg-8c13c42-host/bin/minidregg-host-8c13c42-r1` and read back with the same hash. The full reusable-artifact inventory remains in private Persvati output, SHA-256 `962eb84109270a690963ca0be37f9168cf3e7138a0541b1a80c695ff049894d5`.

Native negative check used the **same private copied event22 Store and config** as the earlier d48 probe, with a one-byte malformed ingress. The 8c Host returned `noncanonical agent lifetime grant ingress`, exit 1, in 5.49 seconds, wrote no output, and left the SQLite Store SHA unchanged. The prior d48 Host hit a 180-second timeout before any verdict because historical replay preceded ingress parsing; [that result remains recorded as inconclusive](../2026-09-27-native-host-d48aa81/README.md). The new result demonstrates fail-fast malformed rejection. It does not demonstrate a valid-but-absent lookup or accepted event27; neither canonical fixture exists yet.

Build command in the independent exact-archive snapshot (`MINIDREGG_LEAN_THREADS=2`, `MINIDREGG_NATIVE_JOBS=2`, CPU quota 200%, memory cap 16 GiB):

```sh
scripts/build-native-host.sh \
  --incremental-suffix-from \
  /home/ember/build/minidregg-d48aa81-native-20260927 \
  /home/ember/build/minidregg-d48aa81-evidence/build-r3 \
  Host.ApplicationAgentLifetimeGrantInspection \
  --allow-suffix-change Host.ApplicationShareIssueGrainInspection \
  --output /home/ember/build/minidregg-8c13c42-evidence/build-r1 \
  --binary /home/ember/build/minidregg-8c13c42-evidence/minidregg-host-8c13c42-r1
```

The adjacent bounded manifest, 353-source hash inventory, validation log, 25-module Lean log, link log, and malformed rejection stderr are suitable for source/build review. No live Store or service was changed.
