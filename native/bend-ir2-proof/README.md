# Experimental Mini IR2 proof harness

This is an offline conformance and privacy-regression harness, not a world proof-admission endpoint. It consumes actual Lean-emitted local-row IR2 through Bread's existing parser, prover and verifier. Whole-controller/source correspondence and full proof-system soundness/zero knowledge remain open.

Provision with `python3 provision.py /absolute/path/to/isolated/breadstuffs`. The isolated source retains exact Bread metadata and pinned `vendor/plonky3-fri-82cfad73` and `vendor/plonky3-challenger-82cfad73` patches. Provisioning neither edits nor builds Bread. Use a leased capped remote lane and the resolved lock; no whole workspace build.

The sibling `bend-proof-entropy` crate supplies OS-seeded cryptographic streams with shared clone state and post-fork refusal. Its three scoped tests passed. This fixes RNG suitability and duplicate clone streams, not STARK masking.

`Host/BendTraceIR2Emit.lean` emits one descriptor and two witnesses with identical public inputs but different private bits. Named kernel checks establish each witness satisfies the actual emitted relation. The typed wire printer preserves the nested field order required by Bread's current parser; generic `Lean.Json.compress` sorts keys and is not this ABI.

Actual raw-backend privacy refutation passed on 2026-10-03: both one-row witnesses produce verified proofs, but the public extension opening permits exact trace recovery. The retained `legacy_config` and raw regression preserve that failure without weakening a live verifier. Set `BEND_IR2_FIXTURE` to the emitted directory and run only the named release nextest targets in a bounded lane. Generated proofs, witnesses and detailed transcript logs remain outside published source.

The current capacity constructor derives a trace-opening budget: the actual default main AIR requests two extension openings, each with four base coordinates, plus nineteen base-row FRI queries. The 27-coordinate budget rounds up to 32 independently randomized trace rows. It rejects unsafe capacities and shifted LDE overflow. Actual minimum32 and normal256 proofs for both witnesses, public-input tamper rejection, and finite observation-map rank/coupling regressions passed. This count alone is not a proof of hiding: full evaluation-map coverage, quotient masking and FRI transcript decoupling remain obligations.

Experimental v3 adds a profile-owned challenger wrapper. It samples the actual degree-four extension until powers 1,a,a²,a³ have full rank, using paired deterministic rejection and a bounded fail-closed limit. Base-field and PoW operations delegate unchanged. The profile/version, exact parameters and public capacity are absorbed before proof messages. This changes the protocol; it must not reinterpret old proofs. The old profile remains test-only. The paired draw-order, capacity, cross-profile and actual proof regressions passed. Conditioned-challenge soundness bounds and full zero knowledge are not claimed.

CLI: `prove descriptor.json public.csv trace.csv proof.bin`, or `verify descriptor.json public.csv proof.bin`. It accepts only the declared local-row grammar. Existing reexecution admission remains in force. Public proof inputs must eventually come from the independently authorized projection and real constrained commitments; neither source metadata nor an opaque proof buffer establishes computation.

The experimental v4 profile seals raw challenge sampling to BabyBear and the exact registered degree-four extension. Direct extension sampling uses the same bounded conditioner as `sample_algebra_element`; other raw algebra samplers are absent. The version remains part of the transcript prefix. The new direct-draw parity test and paired minimum/normal-capacity proof regression pass; this is not a full-transcript ZK qualification.

### Reproducing the experimental backend

`Cargo.toml` is now portable and `Cargo.lock` is the exact tested lock (SHA256
43c1a9e1484ddd9645a5215a85aaad10cc5d651efe97532a2aa7245c2dd9d926).
The external Bread source slice is still an explicit prerequisite. It is NOT
interchangeable with an arbitrary current Bread checkout: `dependencies.lock.json`
pins every Rust/manifest source file in the tested three-crate slice and the two
vendor patches. Its root manifest narrows only workspace membership; package,
dependency, lint and profile declarations remain the tested ones.

Run `python3 provision.py /path/to/exact/source` to verify all pins and create the
owned `../bend-proof-deps/bread` symlink used by the portable manifest. Existing
unrelated files/symlinks are never replaced. The script neither rewrites the
manifest nor launches a build. Run Cargo with `--locked` on an allocated build
host. A source distribution for this exact external slice is still required for
a fresh user who has only this repository; the manifest/lock repair does not
claim that missing distribution already exists.

The v4 conditioned extension challenge distribution remains experimental. The
finite rank, draw-order and same-public/different-private tests do not prove the
whole Fiat–Shamir protocol sound or its full transcript zero knowledge.

### Actual admitted controller proof

`Verify/BendUnrolledDirectEmit.lean` constructs an admitted `Lab "yes"` through
`Assurance.BendObliviousMinimal.prepare`, unrolls the complete twelve-control
machine graph for two raw ticks, and checks that the decoded result is the
independently expected label with zero source reductions. Its descriptor uses
`BendTraceDirect.lower`, the proven interpretation of the existing AIR syntax.
`BendUnrolledDirect.accepted_run` proves arbitrary satisfying field rows force
every actual raw graph step; it does not assume an honest witness generator.
The initial 44 bits and final handled/state 45 bits are all public in this fixture.

On an allocated host with the qualified Lean closure, generate a fresh directory:

```
lean --run Verify/BendUnrolledDirectEmit.lean /path/to/public-fixture
BEND_UNROLLED_FIXTURE=/path/to/public-fixture \
BEND_UNROLLED_PROOF_OUTPUT=/path/to/private-proof-output \
cargo nextest run --release --locked --offline \
  -E 'test(source_admitted_full_controller_proof_binds_input_handled_and_output)'
```

The actual test passed on 2026-10-03: prove/verify, then rejection of changed input,
handled status and final state. The direct AIR used 26,521 columns and took 7.182s,
versus 202,289 columns and 52.008s for the equivalent generic flattened descriptor
on the same bounded host. The latter first exposed a real recursive emitter stack
overflow; `EmitSystemFast` repairs it with proved exact descriptor equality.
These are measured instances, not performance bounds or cryptographic theorems.

The public fixture establishes executable source/controller/prover conformance.
General source coverage, raw controller simulation, actual parser/PCS soundness,
full Fiat–Shamir soundness, full-transcript hiding and native world proof admission
remain separate obligations. No claimed `BindingCommitment` injectivity or deployed
2^-55 composition bound is imported. `BendCommitmentReduction` instead constructs
an actual domain-separated cSHAKE collision from different canonical input openings
with the same public commitment; a concrete collision-resistance bound is still needed.
