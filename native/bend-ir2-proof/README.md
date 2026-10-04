# Experimental Objective Bend proof backend

Objective Bend is the sole language targeted by the active route. This offline harness consumes Lean-emitted local-row IR2 using the pinned Bread parser, prover and verifier. It is not a world proof-admission endpoint, and neither native cryptographic soundness nor full-transcript zero knowledge is established.

The active semantic entry is `Assurance/ObjectiveBendZkClaims.lean`. `ObjectiveBendCommittedSource.arithmetic_observes_source` connects an arbitrary satisfying field assignment to both shared execution/commitment graphs, the unrolled physical run, actual lazy-machine macrosteps, and independent Objective source evaluation. Physical ticks may be administrative; they are not falsely counted as source reductions. The concrete packed controller and result codec must instantiate its refinement and readback premises, and current native admission must independently derive the source and input identities. Those producers are substantive outstanding work.

`Compiler/ObjectiveProofContext.lean` supplies the canonical commitment context and a collision reduction without importing the removed language's invocation types. `BendCommitmentFrame`, `BendCommittedNetwork`, the Boolean DAG, unroller, arithmetic lowering, cSHAKE circuit and PCS harness remain reusable; their historical `Bend` names do not select another language. The successful prepare constructor is proved to return its actual generated graph, whose payload inputs alias the selected execution wires. This prevents unrelated result labels or an independently assignable payload copy from substituting for the constrained computation.

## Native protocol and privacy boundary

The CLI is `prove descriptor.json public.csv trace.csv proof.bin`, or `verify descriptor.json public.csv proof.bin`. It accepts only the checked local-row grammar. The current explicit V5 transcript profile binds independently supplied descriptor bytes through a domain-separated cSHAKE256 digest and exact length, absorbing every digest byte without lossy field folding. This binding relies on computational collision resistance; no globally injective compressing hash is assumed. Source authenticity, authority and disclosure are not conferred by an artifact digest.

V5 preserves bounded paired degree-four challenge conditioning, exact public parameters and capacity binding. The actual changed-artifact test rejects recomputed transcript binding even when altered whitespace parses into the same AIR. Historical V4/raw constructors are retained only for protocol and privacy regressions. They are not a second supported source language.

The entropy crate provides OS-seeded cryptographic streams with shared clone state and post-fork refusal. This does not itself prove hiding. The retained raw one-row regression produces two same-public verified proofs and demonstrates recovery of the private trace from a public extension opening. The capacity constructor refuses unsafe trace shapes using the actual two degree-four extension openings plus nineteen base-row queries, requiring at least 27 masking coordinates and rounding to 32 rows. This trace budget alone is not a complete hiding theorem.

General Lean results now establish fixed-observation polynomial coupling, actual dependent quotient-mask cancellation, the verifier's selector normalization, and descent to bounded prime-field mask polynomials. A native regression calls the actual quotient PCS/DFT and verifier recomposition. Full adaptive quotient/FRI/Merkle transcript hiding, native algebra correspondence, Fiat–Shamir/QROM soundness and instantiated composition bounds remain open. No 128-bit/PQ claim is supported.

## Reproduction

Provision with `python3 provision.py /path/to/exact/tested/breadstuffs`. `dependencies.lock.json` pins the external three-crate source slice and two vendor patches. Provisioning checks every pin, refuses replacement of unrelated paths, and neither edits nor builds Bread. That exact external source distribution is still required; an arbitrary current Bread checkout is not interchangeable.

Use a leased, capped, warm build host. `Cargo.lock` SHA256 is `d79fd70dd24c13098c191dccb5b3d61f1e0c339c1d485f271e0fa5d601edd364`; Plonky3 is pinned to `82cfad73cd734d37a0d51953094f970c531817ec`. Avoid whole-workspace builds. Useful focused targets are:

```
cargo nextest run --release --locked --offline --test quotient_masking \
  -E 'test(native_quotient_masks_preserve_verifier_recomposition)'

BEND_IR2_FIXTURE=/path/to/checked-generic-fixture \
cargo nextest run --release --locked --offline --test artifact_binding \
  -E 'test(exact_artifact_profile_rejects_semantically_equal_changed_bytes)'
```

`Host/BendTraceIR2Emit.lean` produces the generic arithmetic/privacy fixture. Its typed printer preserves the nested field order required by the actual parser. `Verify/BendCommittedIR2Emit.lean` exercises shared execution-output/canonical-frame/hash wires without asserting a language source execution. Generated salt, witnesses and proof transcripts remain private.

The old source-controller fixtures and their test drivers are retired from the active route. Their V5 results remain historical evidence in Git and the dated R32/R33 qualification records; they must not be presented as Objective Bend execution. A new native Objective controller proof awaits the concrete lazy ROM/controller refinement. Existing reexecution admission remains in force.
