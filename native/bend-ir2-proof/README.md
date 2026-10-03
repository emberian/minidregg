# Experimental Mini IR2 proof harness

This is an offline conformance and privacy-regression harness, not a world proof-admission endpoint. It consumes actual Lean-emitted local-row IR2 through Bread's existing parser, prover and verifier. Whole-controller/source correspondence and full proof-system soundness/zero knowledge remain open.

Provision with `python3 provision.py /absolute/path/to/isolated/breadstuffs`. The isolated source retains exact Bread metadata and pinned `vendor/plonky3-fri-82cfad73` and `vendor/plonky3-challenger-82cfad73` patches. Provisioning neither edits nor builds Bread. Use a leased capped remote lane and the resolved lock; no whole workspace build.

The sibling `bend-proof-entropy` crate supplies OS-seeded cryptographic streams with shared clone state and post-fork refusal. Its three scoped tests passed. This fixes RNG suitability and duplicate clone streams, not STARK masking.

`Host/BendTraceIR2Emit.lean` emits one descriptor and two witnesses with identical public inputs but different private bits. Named kernel checks establish each witness satisfies the actual emitted relation. The typed wire printer preserves the nested field order required by Bread's current parser; generic `Lean.Json.compress` sorts keys and is not this ABI.

Actual raw-backend privacy refutation passed on 2026-10-03: both one-row witnesses produce verified proofs, but the public extension opening permits exact trace recovery. The retained `legacy_config` and raw regression preserve that failure without weakening a live verifier. Set `BEND_IR2_FIXTURE` to the emitted directory and run only the named release nextest targets in a bounded lane. Generated proofs, witnesses and detailed transcript logs remain outside published source.

The current capacity constructor derives a trace-opening budget: the actual default main AIR requests two extension openings, each with four base coordinates, plus nineteen base-row FRI queries. The 27-coordinate budget rounds up to 32 independently randomized trace rows. It rejects unsafe capacities and shifted LDE overflow. Actual minimum32 and normal256 proofs for both witnesses, public-input tamper rejection, and finite observation-map rank/coupling regressions passed. This count alone is not a proof of hiding: full evaluation-map coverage, quotient masking and FRI transcript decoupling remain obligations.

Experimental v3 adds a profile-owned challenger wrapper. It samples the actual degree-four extension until powers 1,a,a²,a³ have full rank, using paired deterministic rejection and a bounded fail-closed limit. Base-field and PoW operations delegate unchanged. The profile/version, exact parameters and public capacity are absorbed before proof messages. This changes the protocol; it must not reinterpret old proofs. The old profile remains test-only. At publication the v3 checks are pending; conditioned-challenge soundness bounds and full zero knowledge are not claimed.

CLI: `prove descriptor.json public.csv trace.csv proof.bin`, or `verify descriptor.json public.csv proof.bin`. It accepts only the declared local-row grammar. Existing reexecution admission remains in force. Public proof inputs must eventually come from the independently authorized projection and real constrained commitments; neither source metadata nor an opaque proof buffer establishes computation.
