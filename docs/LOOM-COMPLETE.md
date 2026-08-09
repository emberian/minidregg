# Loom: what is complete, at which boundary

Status: 2026-08-08.

This document used to call Loom “complete” in a way that collapsed several proof resolutions into
one. The repository has since advanced substantially—and found important false targets—but the
honest claim is narrower:

> Loom contains machine-checked protocol, compiler, proximity, accumulation, and game-theoretic
> chains at explicit abstract interfaces. It does not give Rust a semantics, and therefore contains
> no theorem relating native execution to Lean beyond Lean-side checks of native outputs. It also does not yet contain a proved connection from the
> running Rust reference prover to one succinct, zero-knowledge, deployment-parameterized theorem.

That distinction is the organizing principle below.

## Machine-checked core

### Accumulation and chain extraction

- `Loom/Accumulator.lean` defines the constrained Reed–Solomon claim, same-word batching, and
  cross-word affine folding. Honest closure and the one-bad-challenge algebra have firing
  small-field examples.
- `Loom/AccExtractChain.lean`, `Loom/LightClient*.lean`, and the v0 assurance modules prove chain
  extraction, fixed/adaptive soundness, and Fiat–Shamir/grinding statements at their declared
  oracle and commitment interfaces.
- These are protocol theorems, not evidence that `prover/src/accumulator.rs` implements the whole
  protocol. The Rust module mirrors only the post-reduction linear channel.

### Sumcheck and derived arithmetization

- `Loom/Sumcheck.lean` and `Loom/MultilinearExtension.lean` prove the algebraic sumcheck layer.
- `Compiler/Air.lean` derives a circuit interpretation and proves it agrees with execution.
- `Compiler/AirFlatten.lean` lowers into degree-≤2 gates, and the assurance sumcheck modules retire
  the full linear-plus-quadratic gate system.
- `Compiler/Emit.lean` produces first-order descriptor data and proves `emit_faithful`:
  `descriptorHolds` means the emitted Lean gate system holds.

This closes semantic drift inside the compiler. It does not formalize Rust or prove that every
external proof accepted for a descriptor implies `descriptorHolds`.

### Reed–Solomon proximity and the rate regimes

- The unique-decoding core and the unconditional band
  `0 < δ < (1 - ρ) / 3` are proved locally.
- `Loom/HalfThresholdRegime.lean` proves the characteristic-independent algebra behind threshold
  halving: if two distinct affine folds are `δ/2`-close, the source pair has `δ` correlated
  agreement, hence at most one challenge can be bad.
- `Loom/HalfThresholdFri.lean` identifies the ordinary multiplicative FRI fold with that affine
  family and proves the `δ -> δ/2` transition.
- `Loom/HalfThresholdFriTower.lean` composes one halving round with a fixed `δ/2` tail. At rate
  `1/2`, the concrete starting radius `3/10` is above the Johnson radius and the tail radius
  `3/20` lies in the unconditional one-third-UD band.

The tower is a challenge-counting theorem over whole words. It does not yet price query misses or
model adversarially recommitted intermediate words, Merkle openings, or a single Fiat–Shamir
execution.

### Johnson: published mathematics, local import outstanding

`Loom/JohnsonRegime.lean` proves the classical Johnson list-size bound, shows the Johnson interval
strictly extends unique decoding for every nontrivial rate, and proves the exact sampling bridge.

The status of mutual correlated agreement changed after WHIR:

- WHIR's 2024 Conjecture 4.12 remains a named **local hypothesis** so the existing reductions retain
  their historical shape.
- The needed RS/polynomial-generator results through Johnson were subsequently published in
  [2025/2051](https://eprint.iacr.org/2025/2051) and
  [2025/2110](https://eprint.iacr.org/2025/2110), with related proximity consequences in
  [2025/2055](https://eprint.iacr.org/2025/2055). Their proofs are not yet formalized here.
- Capacity-level proximity-gap variants are false; see
  [2025/2046](https://eprint.iacr.org/2025/2046). Loom therefore makes no blanket capacity claim.
- Above Johnson, Loom now has the local threshold-halving route motivated by
  [2026/858](https://eprint.iacr.org/2026/858). The distinct action–orbit route is
  [2026/861](https://eprint.iacr.org/2026/861).

### GF(2) tower and additive proximity

- `Theory/BinaryTower*.lean` constructs actual finite fields of cardinality `2^(2^k)`, proper
  embeddings, Fan–Paar generators, the trace induction, and the proved fast multiplication
  recurrence.
- `Theory/AdditiveNTT*.lean` proves the additive domains, vanishing-polynomial fold structure,
  novel-basis transform, and additive fold algebra.
- `Loom/AdditiveProximity.lean` identifies the additive image domain with an ordinary
  Reed–Solomon domain, transports proximity-generator results, and proves an unconditional
  positive macroscopic additive-FRI band.

`prover/src/binary_tower.rs` now supplies an explicit Fan--Paar coordinate runtime through
`GF(2^64)`, including field operations and one additive fold pair, with exhaustive small-field
teeth. It is still arithmetic rather than an additive-FRI runtime: the fast novel-basis transform,
commitments, query protocol, transcript integration, and Lean-emitted control around unverified
Rust compute remain.

### Zero knowledge: theorem resolution matters

The native Loom games contain proved masking, completeness, extraction, and zero-knowledge
results, including `loom_zk_argument` at its stated formal-game resolution. Sub-UD recovery is
also proved at word/family resolution; the old premise that columns alone determine the increment
below unique decoding is machine-refuted.

Deployment-facing composition is not finished. `Loom/OracleLogLinkedTarget.lean` demonstrates why
the distinction matters:

- the former unrestricted `OracleLogReduction` extractor target is vacuous because an extractor
  can return the already-designated witness without reading the oracle log;
- the replacement pins the extractor definitionally to the shifted log and states the missing
  opening-injectivity, code-membership, distance, and radius hypotheses;
- a fresh-aggregate-challenge uniqueness kernel is proved; and
- `Loom/OracleLogLinkedAssembly.lean` closes the corrected target: fresh-link and hit-slot horns,
  the finite cover, the `(t+k)` union bound, the exact shifted-log extractor reduction, and an F₅
  premise-firing example.

This is the repaired linked OracleLog theorem at explicit UD/root/opening hypotheses. Older Def.
4.2 state-design and sub-UD deployment boundaries remain separate. Accordingly, “native
formal-game ZK theorem” is accurate; “the running prover is a succinct NIZK argument of knowledge”
is not.

### Assurance budgets

- `Assurance/ErrorBudget.lean` proves the displayed BabyBear⁴ budget expression is at most `2^-55`
  and greater than `2^-56`, under its explicit threat model and component interfaces.
- `Assurance/ErrorBudget120.lean` proves a BabyBear⁶ challenge-coordinate plus 20-bit-PoW
  expression lies in `(2^-138, 2^-137]`, and proves both levers are load-bearing at that point.
- `Assurance/PowGrinding.lean` proves the finite ideal-coordinate core: exact `2^-bits` nonce
  density, product factorization, and a leave-one-out adaptive `work * epsilon / 2^bits` bound.

The 137-bit result is an exact theorem about that idealized formula, not a current runtime claim.
The single `fieldCard = BabyBear^6` parameter prices all challenge terms, including sumcheck. The
Rust reference sumcheck is presently over base BabyBear, its FRI challenges are BabyBear⁴, and it
emits no PoW nonce. A mixed-field theorem plus the shared-ROM/domain-separation/runtime bridge is
required before assigning that label to an implementation.

## Running compute

There is now a prover and verifier implementation, contrary to the old version of this document.
`prover/src/protocol.rs` composes descriptor validation, trace generation, a trace commitment,
gate sumcheck, trace-derived RS encoding, and FRI under one replayed transcript. The integration
tests exercise the Lean-emitted demo descriptor and reject mutations.

Its boundary is deliberate:

- `ReferenceProof` carries the full witness trace;
- verification recomputes the trace commitment and entire RS word;
- the hash uses demo/conformance parameters, not a selected deployment set;
- runtime roots, authentication paths, and transcript encodings are nine canonical BabyBear
  limbs, closing `[PROVER-digest-width]` as a representation issue; this does not establish
  `[COMMIT-CR]` or production permutation/capacity security. `Compiler.WideDigestAir` pins the
  corresponding eleven-field encoding through emit, while raw-byte decoding and composition with
  the recursive sponge/full verifier remain;
- the path is multiplicative BabyBear, not the additive tower;
- the Rust/WGSL is unverified compute.

So it is a useful end-to-end **reference path**, but it is non-succinct and non-ZK.

The optional WGPU implementation accelerates only the BabyBear⁴ fold and is conformance-tested
against the CPU version. It is outside the protocol core and imposes no compatibility constraint
on the next prover architecture.

## What is not complete

The principal remaining joins are:

1. global adaptive earliest-deviation/query coupling for the landed committed half-threshold FRI
   rounds, followed by concrete Merkle/CR and FS Reduction composition;
2. formalize the `HaboeckTheorem2` algebraic core behind the landed exact Johnson MCA interface;
3. connect the landed fast additive NTT to commitments, queries, transcript, multi-round FRI, and
   its Lean refinement;
4. replace the landed exhaustive commitment/code-linked accumulator reference with succinct
   queried openings, transcript-derived challenges, and its RBR extractor;
5. add verifier-level root-word attribution, then compose sampling-to-closeness into the landed
   sub-UD linked-log transport and build the hiding-window Def. 4.2/runtime instance;
6. succinct openings connecting the emitted nonlinear gate claim to the low-degree claim;
7. concrete hash parameters and a one-execution ROM/PoW composition; and
8. a concrete commitment hash, the wide-digest verifier-AIR bridge, and one field-consistent
   security budget matching the runtime actually executed.

The defensible one-breath claim is therefore:

> minidregg has a large machine-checked proof-system and compiler core, new unconditional
> post-Johnson and additive-proximity mathematics, and a running transparent reference prover.
> Its remaining frontier is not “get the old GPU path into production”; it is to connect those
> pieces into a succinct, ZK, field-consistent implementation without weakening their exact
> theorem boundaries.
