# Recovery native build, 2026-09-28

The Linux Mini client is qualified from the exact committed `0007925` resource-client archive, and the matching Host is qualified from the exact committed `e22d16b` archive. Both binaries are staged independently; this build lane did not install either into an operator service or change a live Store.

| Item | Pin |
| --- | --- |
| Mini archive | SHA-256 `b8644623d2c542e6715b0828273ad742448c48488c8a1b4008dbf59a70965117` |
| Mini complete source-file manifest | SHA-256 `e329d789433bcfb2f030719f2a127ecb943a85c5c1b9eac5be70522f288a3f1d` |
| Mini ELF | `/home/ember/build/minidregg-recovery-20260928/mini-0007925/bin/mini-0007925`, SHA-256 `3e9cb1ca488995a0a591ea6db8f9b4b6b59d9629782daf6babb294620c74513d` |
| Mini manifest | `/home/ember/build/minidregg-recovery-20260928/mini-0007925/manifest.txt`, SHA-256 `d7abb77ad638415e1ad63fa46fe848bb7dc1adf6ee6f38dfeabdcc09580ebcc5` |
| Mini build log | `/home/ember/build/minidregg-recovery-20260928/mini-0007925/build.log`, SHA-256 `c9223617f9d5a75b63a59d7ea661ba07d58d6c6e13e56b337fccd6196f9c6ab1` |

`cargo build --release --locked --manifest-path native/resource-client/Cargo.toml --bin mini` passed in an independent source/target directory with one Cargo job. The copied 190 MiB target cache was writable and independent of the prior qualified `bae39a8` target. Complete archive source and final ELF hashes were checked again after the build. The ELF is x86-64 Linux and staged mode `0500`. This was a release build, not a fresh test-suite result; focused source tests and Clippy belonged to the committing lanes.

The Host source archive is exact commit `e22d16b`, SHA-256 `2876336e0189fbbf23fe2c9a455e3b095129eb536fd3c04165a9239a3add9c6a`; its complete tracked-source manifest is SHA-256 `7bbacfdf7774ddfdc01d493db4377ad3e9e10006a1b5abfa6fb075e3e5ac9780`. The archive was overlaid only into the independent `/home/ember/build/minidregg-event28-diagnostic-next-20260927` snapshot, preserving `.lake`, `.git`, and the snapshot marker. Every tracked archive source byte was read back before compilation. The snapshot's inherited `.git` metadata is warm-cache metadata, not source provenance.

| Host item | Pin |
| --- | --- |
| ELF | `/home/ember/build/minidregg-recovery-20260928/native-e22d16b/minidregg-host-e22d16b-r3`, SHA-256 `723940446d3e0256bd446b07ca8d67ea9d67295d8c7cc78e08bb2487ffbe3db2` |
| Native manifest | `/home/ember/build/minidregg-recovery-20260928/native-e22d16b/build-r3/manifest.txt`, SHA-256 `862e17fcf0a462bdad6b830cd3a46e13801af1a2339a1ee9e41f1ef552d24afb` |
| Imported-source SHA manifest | `build-r3/source-sha256.txt`, SHA-256 `409d425ada8323ff8bde8213bacecae06868fbc87d05600bf01de7295a0f6054` |
| Artifact SHA manifest | `build-r3/artifact-sha256.txt`, SHA-256 `768d7fc094bd15e2e9adfa2204baab1900417e5dbe57c8f1d743830a5f7c0846` |
| Artifact readback log | `build-r3/artifact-readback.log`, SHA-256 `127da967452e1a0af6f773d91cb419b181abb963632faef31a6d0d7cbb0ceede` |
| Driver log | `/home/ember/build/minidregg-recovery-20260928/native-e22d16b/run-r3.log`, SHA-256 `692d11c76e3556d24e37082f2e6ec3b509a8bd120bf307a420abfb392afe6801` |

The Persvati **user** unit `minidregg-recovery-e22d16b-host-r3.service` ended successfully at 23:49:37 UTC (1,069 seconds). The guarded builder qualified a 363-module Lean closure, reusing only the 182 earlier source/artifact modules from immutable qualified `2721253` and checking all 2,933 package objects. It compiled a 181-module suffix, including ten declared inserted modules, then linked 3,296 response objects. The manifest reports 159 unchanged later sources. The linked x86-64 ELF was independently hashed and staged mode `0500`; imported-source and artifact SHA lists both passed a separate readback. The builder's `git_head=791a6d2c...` field reflects copied warm `.git` metadata and must not be used as the source cut. The archive and tracked-source SHA pins above establish `e22d16b` identity.

The first `81b740b` attempt used the qualified `2721253` baseline and passed the guarded reuse check for 182 earlier source/artifact modules, 10 declared later changes, 10 inserted modules, 160 unchanged later sources, and 2,933 package objects. It failed at module 321, `Host.ApplicationLifecycleClaimInspection`: the new SPK import made bare `codecV2.decode` ambiguous. The exact error is retained in `/home/ember/build/minidregg-recovery-20260928/native-81b740b/build-r1/lean/0321-Host_ApplicationLifecycleClaimInspection.log`. No `81b740b` ELF was qualified. The one-line explicit projection name in `e22d16b` passed an independent direct Lean check.

The corrected `e22d16b` r2 attempt refused before validation because its wrapper named nonexistent qualified-baseline output `build-r2`; its log remains `/home/ember/build/minidregg-recovery-20260928/native-e22d16b/run-r2.log`. The r3 wrapper used the actual immutable `2721253` `build-r1` baseline. The failed `81b740b` run had no resume checkpoints or successful manifest, so no part of it was claimed as a qualified reusable baseline. R3 recompiled the suffix from module 183 under the existing source/artifact guard and passed the formerly failing inspection module at index 321.

The `2721253` baseline tree, ELF, and manifest remain immutable. The separate failed `81b740b` output and its diagnostic logs are retained. No cache cleanup is authorized while any fixture or later source check still consumes those OLeans; after a successor ELF and its evidence qualify, only a specifically identified inactive build cache may be reclaimed after owner/process checks. No operator service or live Store was changed by this build lane.
