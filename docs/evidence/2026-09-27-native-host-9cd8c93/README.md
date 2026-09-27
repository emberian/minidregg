# Exact `9cd8c93` Linux native Host

This Host was built from the committed source cut `9cd8c938bcac93d097c8696dd18ffca45a4fdf3d`, using an independent writable copy of the certified f450 snapshot. The exact Git archive SHA-256 was `3b7cc86fb8bcde603c8d8a38a518e897eda541f6fb54bc0054ce1b653fc29156`; only `Kernel/ResourceBirthPolicyController.lean` (`92e28ed05a2de77a3ae70acb4beef956ff031ab479e97886e7c232b0ac6df9ff`) and `Host/ApplicationAgentLifetimeDispatchInspection.lean` (`dd97aeaad4f193256fa1a3d9a227fd21b703ea66d435ba9234eac26903b83660`) differed from the f450 Host closure. All 353 project source files in that closure were compared byte-for-byte to the extracted committed archive before compilation, and the 353-file source manifest passed a fresh post-build readback.

The guarded successful-prefix reuse checked and retained the first 138 modules from `/home/ember/build/minidregg-capability-next-20260927` and its certified `/home/ember/build/minidregg-f450a57-evidence/build-r1` output. It compiled modules 139–353 and rebuilt their 215 C objects. The full 353-module Lean gate, native link, and artifact checks passed. `usage_exit=1` is the expected command-line usage probe. The copied [manifest.txt](manifest.txt) reports a reusable-artifact manifest SHA of `240f0480fd241bb1e23c88b96655b3de5757153e91fcacf951b64f5193f0a68e`; the **manifest file's own** SHA is `e020dfb36dc164ca9a74cfb46dce022eb45751d41c13e5cced08c43b4bc5fd4f`.

The linked Linux x86-64 ELF is `/home/ember/build/minidregg-9cd8c93-evidence/minidregg-host-9cd8c93-r1` on Persvati, SHA-256 `0728c9161e6a60bbbc257eb6e41bd505683358027c94c221776b8de13a558ce9`. A readback-identical, mode `0500` copy is staged without execution at `/tank/dregg-build/minidregg-9cd8c93-host/bin/minidregg-host-9cd8c93-r1` on hbox. No service was installed or launched.

Build invocation, from `/home/ember/build/minidregg-9cd8c93-native-20260927` on Persvati, under user unit `minidregg-9cd8c93-host-r1.service` (invocation `edfc86bbf7b04c239436e41043600e9c`):

```sh
MINIDREGG_NATIVE_JOBS=2 MINIDREGG_LEAN_THREADS=2 \
MINIDREGG_CYCLE_DIR=/home/ember/build/minidregg-9cd8c93-evidence/cycle \
bash scripts/build-native-host.sh \
  --reuse-success-prefix-from \
  /home/ember/build/minidregg-capability-next-20260927 \
  /home/ember/build/minidregg-f450a57-evidence/build-r1 \
  --output /home/ember/build/minidregg-9cd8c93-evidence/build-r1 \
  --binary /home/ember/build/minidregg-9cd8c93-evidence/minidregg-host-9cd8c93-r1
```

The unit exited successfully under `MemoryMax=32GiB`, `CPUQuota=200%`; the serialized Lean compiler used two threads and native C used at most two jobs. [build.log](build.log) records every module verdict. Fresh readbacks passed for 10 output artifacts, 353 source files, and 10,211 reusable artifacts. The retained lists and readback logs are copied here; [SHA256SUMS](SHA256SUMS) checks this portable evidence directory. Paths in artifact manifests refer to the preserved build snapshots, not to files copied into this repository. The source manifest can be checked against a private extraction of the exact commit. No runtime integration or new tests were run for this artifact closeout.

The manifest's `git_head=791a6d2c...` is inherited snapshot metadata. The source provenance is the exact `9cd8c93` archive and closure comparison, not the inherited `.git` directory.
