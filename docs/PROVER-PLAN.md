# The prover: current reference surface and next joins

Status: 2026-08-08. This document supersedes the original WGPU-first construction plan. The seven
old rungs have largely landed in CPU reference form, and the GPU fold is now deliberately optional.

## What exists

The `prover/` crate is **unverified compute downstream of the verified emit seam**. It consumes a
`ConstraintDescriptor` produced by `Compiler/Emit.lean`; it does not author an AIR. Lean proves
`emit_faithful`. Rust has no semantics in this project; native tests are only engineering evidence
for unverified compute, whose outputs Lean-owned control must recheck.

The crate contains:

- JSON descriptor parsing and validation;
- deterministic trace generation and a mirror of `descriptorHolds`;
- a Poseidon2-shaped demo permutation and Merkle commitments;
- multilinear sumcheck and the descriptor gate-defect reduction;
- BabyBear⁴ arithmetic, multiplicative FRI folding, commitments, query openings, and final checks;
- a Fiat–Shamir transcript with Lean-authored conformance vectors;
- `reference_prove` / `reference_verify`, one-call composition under one transcript;
- a succinct Ext6 factored-gate verifier using one committed trace root and one aggregated
  trace-functional opening;
- a separate executable mirror of Loom's linear accumulator algebra; and
- explicit Fan--Paar binary-tower arithmetic through `GF(2^64)`, fast additive NTT, and byte-native
  hash/Merkle compute. The former handwritten sampled-FRI/OOD/evaluation-history admission stack was
  deleted after its claimed degree bound was found unenforced.

The reference protocol performs:

```text
descriptor + assignment
    -> satisfying trace
    -> trace root
    -> transcript-derived gate batching and sumcheck
    -> deterministic RS encoding of the trace
    -> transcript-derived FRI folds and queries
    -> final-word and opening checks
```

The verifier takes public inputs, replays every challenge, recomputes the trace root, reconstructs
the full RS word, checks that word's initial FRI commitment, and verifies the gate and FRI phases.

## What that does not mean

`ReferenceProof` contains the whole trace. Verification is linear in the trace and full RS word.
The path is therefore:

- **non-succinct**;
- **non-zero-knowledge**;
- a demo/reference implementation rather than a production prover; and
- unverified Rust, even where its behavior is conformance-matched to Lean objects.

The reference permutation parameters are intentionally small demo/conformance parameters.
`[PROVER-poseidon-params]` / `[AIR-poseidon-params]` still names selection and analysis of a real
parameter set. `[PROVER-digest-width]` is now closed at the runtime representation layer: every
Merkle root and authentication sibling is a nine-limb canonical BabyBear `Digest`, and transcripts
absorb a fixed-width, domain-separated encoding. The carrier has more than 248 bits of range, but
range is not collision resistance. `Compiler.WideDigestAir` now pins the matching fixed-width
encoding through emit. `[COMMIT-CR]`, production permutation/capacity analysis, raw-byte canonical
decoding, and wire-sharing composition with the recursive sponge/full verifier remain load-bearing.

The historical one-call implementation still uses multiplicative BabyBear⁴ rather than the binary
suite. Native GF(2) arithmetic, transform, and byte-native hash/Merkle kernels remain, but no sampled
binary FRI/OOD verifier is currently admissible. Lean-emitted rate-aware control must replace the
deleted handwritten stack before a binary light-client proof returns.

## Accumulator boundary

`prover/src/accumulator.rs` implements the post-reduction linear algebra:

- batch constraints with powers of one challenge;
- fold aligned claim targets;
- fold witness words coordinatewise; and
- iterate those operations over a chain.

The separate `prover/src/committed_accumulator.rs` is the first honest reference join: it binds a
wide root to a fully opened word, authenticates every position, checks multiplicative RS membership
by inverse DFT, and rechecks committed fold closure. This resolution is deliberately exhaustive,
shipping the whole word and every authentication path. Succinct queried openings/FRI,
extension-field challenges, formal FS/RBR refinement, RBR extraction, and the gate-to-linear-channel
bridge remain. The reference wrapper does derive its base-field fold challenge after absorbing both
complete claims and roots under a dedicated domain; it is not yet part of `ReferenceProof`.

## WGPU is an optional experiment

The `wgpu-fold` Cargo feature contains a BabyBear⁴ WGSL fold adopted into this crate and tested for
bit-for-bit agreement with the CPU fold. It is useful performance and conformance evidence, but:

- default builds do not depend on WGPU;
- `reference_prove` and `reference_verify` are CPU-only;
- only the fold is accelerated, not the surrounding PCS/protocol; and
- no future protocol is required to preserve this kernel or its data layout.

The project can rewrite or delete this path when additive FRI, a different field, or a better
prover architecture warrants it.

## Security labels

Do not attach the formal 137-bit candidate to this runtime. `ErrorBudget120` uses one
`BabyBear^6` cardinality for every challenge term and adds a 20-bit PoW price. The reference gate
sumcheck uses base BabyBear, FRI uses BabyBear⁴, and the transcript has no nonce rule. `PowGrinding`
proves the independent ideal-coordinate counting core, not that the demo sponge realizes those
coordinates in one shared ROM execution.

The older 55-bit BabyBear⁴ formula is also a theorem about named component interfaces and a threat
model, not a claim that demo hash parameters make the current executable a 55-bit production
system.

## Next implementation joins

The highest-value next steps are protocol joins, not GPU preservation:

1. **Succinct gate-to-LDT linkage:** replace the clear trace with committed wire/selector openings
   and a sound terminal claim. **Landed at sampled resolution:** the verifier receives no trace or
   defect table. Remaining: proximity/subfield/CR/ROM composition, refinement, and final LDT join.
2. **Additive refinement:** connect the running binary suite to the proved characteristic-two
   adaptive/coherent theorem and its cryptographic assumptions.
3. **Accumulator protocol:** generalize the fixed evaluation-channel append to receipt-native
   functionals, then connect it to the staged RBR extractor and final compression.
4. **Deployed ZK:** instantiate hiding committed-word-knowledge proofs and discharge the staged
   roots-before-query game's shared-ROM fresh/hit/sampling ports.
5. **One light-client proof:** the gate/binary conjunction now exists. Replace its separate component
   schedules with the shared-ROM RBR/extractor/final-compression protocol before performance
   promotion.
6. **Concrete cryptography:** select real permutation parameters, connect the landed wide runtime
   digest to the verifier AIR, define optional PoW nonce semantics, then prove the shared-ROM and
   commitment-security bridges.
7. **Field-consistent budget:** price the exact fields and challenge coordinates the implementation
   uses, including base-field sumcheck if retained.

## Performance gates

The intended performance target is not “beat every Plonky3 configuration.” It is receipt-native,
binary/word-heavy proof-carrying history: cheap incremental folds, low memory traffic, horizontal
scaling, and one final compression. The additive backend should not be promoted to the main path
until reproducible benchmarks show:

1. fewer constraints and bytes moved on a native receipt/hash workload;
2. append cost and peak memory that remain well behaved with history depth;
3. useful multicore and multi-machine scaling;
4. competitive final proof size and light-client verification after compression; and
5. results measured at the exact proved rate/security regime, not an optimistic conjectural one.

Measurements, commands, hardware, and interpretation live in
[`docs/PERFORMANCE.md`](PERFORMANCE.md). The first entry is the full-trace reference baseline, not a
claim of competitiveness.

## Tests

```sh
cd prover
cargo test

# Optional hardware path. Tests skip if no compatible adapter is present.
cargo test --features wgpu-fold
cargo run --release --features wgpu-fold --bin fri_fold_bench
```

The tests are designed to have teeth—mutated public inputs, trace roots, sumcheck messages, FRI
roots, openings, and final words reject—but they remain executable evidence, not machine-checked
Rust correctness.
