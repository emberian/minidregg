# Native provider witness gate — 2026-09-26

This is a **direct Mini native gate**, not an upstream Hermes or provider-network run. A fresh deployment on persvati used a parent grain (7001), tool grain (7002), scalar publication resource (7003), and distinct provider grain (7004, subject 9). The parent policy was authored with `workerSubjects:["8","9"]` and a pinned generation. The run exited successfully after these signed checks:

- A provider reserve of 51 against a remaining purse of 50 was refused at admission. Signed parent and provider roots stayed unchanged.
- A joint provider reserve of 3 with a parent no-op witness was confirmed. The provider moved to generation 1, status 3, remaining 47, reserved 3; the parent remained generation 1, status 3, remaining 97, reserved 3 with the same root.
- The parent hard disconnect was confirmed at generation 2, status 5, reserved 3. Retrying a prepared provider witness pinned to generation 1 was refused at admission, and the provider root stayed unchanged.

The selected public intents, outcomes, and signed query views are in `receipts/`. The two refusal records encode phase `admission` and detail `request refused` as hex. The source run was `/tmp/mga-provider-direct-evidence-20260926` on persvati; this checked-in selection excludes keys, store files, call bytes, and credential material. It is evidence of these native transitions and refusals only.

## Exact run image

| Component | SHA-256 |
| --- | --- |
| Linux Mini host (`minidregg-host-combined`) | `31a00492594a9abbde4541fef687f4d6a2fd2cac06c1645e604178a3e7f18179` |
| Frozen bootstrap `acceptance.sh` | `d62730b19f65fb52599561adfa074c69bab6acd6a240d70c95a0d8f3b03a3fcc` |
| Frozen `provider-direct.sh` | `6012d4f79d3b9354bd43ac55ced647edc7f57230ddbc4c04fb3e43841a509f5f` |
| `mini` | `3960d33f2eb79116147179de8783d34d0ebd0dc22b238112e818bd248cb8cd91` |
| SQLite Store helper | `ad03aede839259c1884383fc97f141a3fe106ba2f2cbae0df6f7916676fe193f` |
| Signature verifier helper | `c84004123ae6f02654cb6749e4105e351199618aaefce5755a2a0bb10bd0892b` |

The host build manifest is `/home/ember/build/minidregg-overnight-20260926/evidence/build-linux-combined/manifest.txt` on persvati: Lean 4.30, source modules 165/165, native artifacts 4/4, usage check passed. The frozen run manifest is `/tmp/mga-provider-direct-source/run-manifest.sha256` on persvati. The shared bootstrap later gained optional provider setup and Linux unit ownership checks; `acceptance-28d8-to-a77.diff` records that separate source delta and is not the direct run image.
