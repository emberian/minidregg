# Copied-Store Mini own-R submit profile (2026-09-26)

This is a read-only performance investigation of the live workroom journey.
All profiling submissions ran against new private SQLite Stores reconstructed
from the retained genesis and the exact birth, delegate, and tag10 signed
calls. The three reconstructed setup outcomes matched their originals
byte-for-byte before profiling the tag9 call. No profiler or extra Host used
the live A Store or fn cursor.

The retained tag9 `call.bin` was 1,051,229 bytes, SHA-256
`27c5cf71d9940271fa50313d533d63f7c688fe6656ec8dbb9b8ffd5c0b4c5600`.
Every profiled submission returned the same confirmed `outcome.bin` as the
original, SHA-256
`46e366e595500503da0336be3c8626034a43c4d27e2bf3186e0b4f4996752e9c`.
The source-qualified Mac Host was
`/tmp/minidregg-overnight-20260926/minidregg-host-provider-ownr-stable`,
SHA-256 `c37a35073b9d19ac342d91ba0a071b3a732f51b0f5f0991fc995ec64573edcff`.
The persistent client was committed `a2a6fa5`, immutable binary SHA-256
`909d4886448d18072012a28871554b8dd88c59f0c965e422f26dff99c2afeed1`.

| Run | Wall time | Profiled phase | Evidence |
| --- | ---: | --- | --- |
| Direct one-shot, copy 1 | 89 s | t≈2–12 s: cold `openExisting` replay | Private `mini-ownr-profile-20260926-client/ownr-submit.sample.txt` |
| Direct one-shot, copy 2 | 97 s | t≈23–33 s: fresh admission; t≈51–61 s: post-CAS confirmation replay | Private `mini-ownr-profile-late-20260926-client/ownr-submit.{mid,late}.sample.txt` |
| Persistent `mini serve` + socket retry, copy 3 | 51.92 s | Warm op2 request and typed inspection; service startup excluded | Private `mini-ownr-profile-warm-20260926-client/retry.time.log` |

The Mac `sample` reports 7,753 active Lean worker-thread samples in the early
window; 7,512 are under `NativeHost.openExisting` and semantic replay of the
three-event prefix. In the middle window, 5,153 of 7,905 active samples are
under fresh `DeclaredResourceController.admit`; 1,432 are in
`step → projectCommonSlots`, including 695 in `requestFor → cSHAKE`.
In the late window, all 8,122 active samples are under
`NativeHost.confirmed → openExisting → NativeHostReplay.verifyLoaded` after the
CAS. These are inclusive stack sample counts from selected 10-second windows,
not percentages of the full invocation. Reported physical footprint rose
from 862.9 MiB early to 1.6 GiB mid and 2.4 GiB late. The low-priority
process and sampling can affect wall time; the warm and direct runs are not a
controlled latency benchmark.

Source tracing explains the scaling candidate without changing semantics:
`ResourceTransaction.requestFor` separately encodes and domain-frames the
whole command for `argsDigest` and `effectsDigest`, then encodes it again for
cost. `DeclaredResourceController.projectCommonSlots` expands each encoded
command byte into a named policy slot, while `projectWithCommon` also expands
resource bytes for local and joint incidences. The sampled fresh admission
stacks contain both command hashing and policy projection. A source-owned
shared-byte refactor of `requestFor`, proved equal for every command/target,
is a narrow first optimization. Reducing policy slots requires a separate
evaluation-equivalence proof for arbitrary policies; full-image CAS and exact
post-CAS readback remain required.

The private profile directories contain Store/config and retained call
material and are deliberately not copied into this keyless evidence tree.
