# Exact policy projection reuse after the B3 native join

The successful B3 fixture in [FN-E2-B3-NATIVE-2026-09-24.md](FN-E2-B3-NATIVE-2026-09-24.md)
used Mini source `1eb84a9`. Its separate-process prepared, signed and signed-slot
replay stages took 31.191, 38.661 and 35.049 seconds. Those are material
application costs. No original prepared/signed sidecar or fn Store was changed
for the following profiling and optimization.

On the same two-accepted-event Mini image, an instrumentation-only compiled
host measured 27.538 seconds in `NativeHost.openExisting` of a 28.78-second
plan invocation, and 27.563 seconds of a 28.90-second signed-slot reuse.
The historical replay performed full native receiver admission. Entry 0
derived in about 2.4 seconds; entry 1, a joint invocation, derived in about
22.2 seconds. Its one target and authority `authorizeLeg` each took about
9.7 seconds. A 12-second CPU sample of the uninstrumented original binary
located a large portion of this work under
`PolicyStepContext.ofPreparedTupleExact` and its old/new projections,
including repeated `requestFor` cSHAKE calculation. A wrapper around the
actual native Ed25519 helper observed 11 calls taking about 4–5 ms each;
the external signature verifier was not the main source of this delay.
The sampling report is `/tmp/mini-b3-cpu-sample.txt` (SHA-256
`904b5d606da2561b4ba930bf6377193ef284a106d1433019136868e1780ac0de`).

Commit `6f2faa17d3a4a00965db5521da43aba052118510` derives the policy
projection's invariant request and command slots once from the exact
prepared tuple/incidence, then shares them across its old and new logical
states. `projectWithCommon_exact` proves the cached projection equals the
original for every logical state; `step_prepared_exact` connects the actual
receiving `step` to the original prepared-tuple context. Full prefix replay,
native signature checking, policy admission and canonical record comparison
remain on the path. No caller supplies an independent request identity or
policy result.

The candidate's 158 source modules matched the isolated Mini branch exactly
and were compiled with Lean 4.30.0 (arm64 macOS, commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`) through the same native
toolchain and link closure as the B3 baseline. The clean baseline executable
SHA-256 is `11f451f7c14d55efcb16ee16f99bfffc20f551a7ebf173d5090966e1434f68f9`;
the clean candidate executable SHA-256 is
`568bbbeaaf71eab3bd9d35e55d0f62e2282b211aed48db900fbc7f294da5181a`.
Three interleaved read-only `describe` pairs ran against
`/tmp/mini-fn-e2-native-20260923/live-deployment/pinned-config.json` using
`/usr/bin/time -p <binary> <config> describe`, in order B1,C1,C2,B2,B3,C3:

| Executable | Real seconds, three samples | Median | Range |
| --- | --- | ---: | ---: |
| B3 baseline | 29.86, 29.53, 29.72 | 29.72 | 29.53–29.86 |
| Cached projection | 26.65, 26.23, 27.14 | 26.65 | 26.23–27.14 |

All six `describe` outputs had SHA-256
`300eb8adbaad66d7901a0d0832dde316682e173a1fc15caa0c2a48eb778c3bbd`.
The raw elapsed/user/system samples and run order are in
[`E-20260924-mini-b3-projection-perf.json`](evidence/runs/E-20260924-mini-b3-projection-perf.json).
This is a 3.07-second median reduction on this one two-event read-only
fixture, not a general speedup or a throughput bound. Even after this change,
reopening still took a 26.65-second median; a future optimization must
preserve fresh native admission of every durable prefix.

The changed `Kernel/DeclaredResourceController.lean` and its 25-module
dependent native closure compiled. `scripts/probe-declared-resource.lean`
passed with actual native signatures, exact page/authority tuple, durable
replay and refusals for tampering, an unrelated signer, stale root, overbroad
edit and object-to-program edit; its retained log SHA-256 is
`81f96548a62adcffba64da31dabcb7f7fb21f024b78e8e38a01788df12cd6fd1`.
A separate physically replayable scratch image changed the first retained
original ingress to `[255]`. The clean candidate `describe` refused with
`semantic history refused at entry 0: unsupported or noncanonical signed
historical ingress`, exited 1 with no stdout, and left the scratch image's
readback SHA-256
`074a826db38a21c1b4eebe8db08849ac5d1947a53023a43887d5782b89ecdb4d`
unchanged. Baseline/candidate B3 stage replays also returned identical v2
prepared, v1 readback, signed readback, authored source and detached signature
bytes; the immutable v1 slot still returned `uncertain`/exit 3. The candidate
has not repeated the full fn sign/post/cold-reopen handoff or qualified a new
fn image; those claims belong only to the exact original B3 binaries above.

The scratch bytes can be reproduced with the retained
[`forge_history.lean`](../scripts/fn-b3/forge_history.lean) against the
candidate's compiled modules:

```sh
MINI_B3_FORGE_CONFIG=/tmp/mini-fn-e2-native-20260923/live-deployment/pinned-config.json \
MINI_B3_FORGE_OUTPUT=/tmp/mini-b3-forged-history.bin \
lake env lean scripts/fn-b3/forge_history.lean
```

The script itself checked physical restorable state and reproduced the scratch
image SHA above. The test installed it with the opaque SQLite transport's
`publish` into `/tmp/mini-b3-forged-store`, selected only that root in a copy
of the operator config, then invoked `<candidate> <scratch-config> describe`.
The retained exit/stdout/stderr files are in [`docs/evidence/runs/`](evidence/runs/)
as `E-20260924-mini-b3-forged-describe.*`.
