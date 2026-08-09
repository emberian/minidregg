# minidregg

**A Lean-first laboratory for proof systems, derived arithmetization, and proof-native
computation.**

minidregg develops three things together:

1. **Loom**, a machine-checked proof-system model built around Reed–Solomon proximity,
   accumulation, sumcheck, Fiat–Shamir, and zero-knowledge/extraction games;
2. a **derived AIR compiler and emit seam** whose first-order descriptor is proved to mean the
   same thing as the Lean gate system; and
3. an **unverified Rust reference implementation** that can take an emitted descriptor through
   trace generation, commitment, gate sumcheck, and multiplicative FRI in one transcript.

The stable clean-sheet architecture and ordered construction plan live in
[`PROJECT.md`](PROJECT.md); [`GOAL.md`](GOAL.md) is the evidence/status ledger.

This is a frontier research stack, not a production prover. In particular, preserving or reaching
a particular “production GPU path” is **not** a project goal. Acceleration is an implementation
choice downstream of the protocol. The existing WGPU fold is retained as an optional conformance
experiment and can be replaced wholesale as the protocol evolves.

## Status at a glance

| Surface | What has landed | Exact boundary |
|---|---|---|
| **Derived arithmetization** | `Compiler/Air` proves the executor and circuit readings agree; flattening produces degree-≤2 gates; `Compiler/Emit` produces a serializable descriptor with `emit_faithful`. `Theory/Bignum` owns fixed-width little-endian limbs, and `Compiler/AirBignum` emits range-checked carry addition with exact integer soundness and overflow rejection. | This proves what emitted constraints mean, including the landed bignum addition gadget. Rust/WGSL has no semantics here: it is unverified compute whose outputs must be rechecked by Lean-owned control. Multiplication and broader application-language lowering remain separate work. |
| **Multiplicative RS proximity** | Ordinary unique-decoding results, an unconditional one-third-UD band, and `HalfThreshold*`: one round halves the radius outside at most one field challenge, followed by a proved UD tail. The committed transcript, adaptive earliest-deviation argument, and coherent runtime-shaped query paths are assembled at `m·b/|F| + (1−τ)^q`; the rate-1/2 `δ=3/10 → 3/20<1/6` specialization is machine-checked. | Concrete Merkle collision resistance and the single-ROM Fiat–Shamir reduction remain cryptographic/composition floors. The coherent theorem is multiplicative; it is not silently reused for characteristic-two additive folding. |
| **Johnson/list regime** | `JohnsonRegime` proves the list-size inequality and exact sampling amplification. `JohnsonMcaBridge` imports the exact theorem interface and constants from Haböck 2025/2110, corrects the paper/Loom degree convention to `ρ_H=(d−1)/n`, and proves that one `m=max(3,d)` instance covers Loom's rounded Johnson target. | The hard BCIKS/GS/Hensel algebraic proof is still the explicit proposition `HaboeckTheorem2`, not a local theorem or axiom. Thus the Johnson MCA seam is exact and conditional, not yet machine-proved end to end. There is **no blanket capacity claim**: capacity-level variants have counterexamples. |
| **GF(2) tower and additive FRI** | `Theory/BinaryTower*` proves the tower/fold algebra; `Loom/AdditiveProximity`, `AdditiveFriTower`, and `AdditiveFriQuery` now close the literal characteristic-two quotient tower, adaptive earliest-deviation cover, authenticated coherent paths, and the UD bound `m·2^(ell−1)/|F| + (1−τ)^q`. Rust has Fan–Paar `GF(2^64)`, a shift-aware `O(n log n)` transform, cSHAKE commitments/transcript, sampled multi-round FRI, an OOD quotient PCS, and arbitrary trace-linear retirement. | Those Rust paths are unverified compute/conformance oracles, not refinements. Generated Lean authority, basis/order correspondence, CR/shared-XOF composition, and the outer accumulator remain. |
| **Indexed lookup** | `LogupIndexLink` proves decoded Boolean address columns give literal unit-vector incidence and exactly the LogUp* pushforward. The Rust Tower256 LogUp prototype checks each committed index column and binds the ordered roots into one bundle. | Its handwritten verifier/receipt adapter is not authoritative and must be replaced by Lean emission. The zerocheck/PCS also inherits additive proximity and CR/ROM assumptions; this is indexed evaluation, not yet mutable RAM. |
| **Accumulation** | Loom proves claim folding, exact/UD soundness, arbitrary-depth extraction, and depth composition. `SemanticReceiptRelation` proves that the clean-sheet pre/post/touched quadratic word is exactly a `ReceiptDelta`; Lean proves header-cell packing and the bound `AccClaim` fold. Rust has executable history prototypes. | The handwritten Rust receipt/admission/history objects are mirrors and are being replaced by Lean-emitted artifacts. This is not yet the final WARP/FACS protocol; hiding/ZK composition and the unbounded outer accumulator/decider remain. |
| **Zero knowledge and extraction** | Native formal games, constrained masking, corrected OracleLog assembly, and sub-UD recovery are checked. `OracleLogLinkedTwoPhase*` freezes checked root preimages before a domain-separated query, binds the response to that query, transports accepted transcripts into sub-UD log extraction without `d≤t`, and assembles exact full-domain and allowed-coordinate sampling prices. | The staged reduction still exposes explicit shared-ROM fresh/hit/sampling ports. A concrete hiding deployment needs ZK proofs of committed-word knowledge rather than transparent all-word openings, plus CR/ZK errors; Rust is not ZK. |
| **Assurance arithmetic** | `ErrorBudget120` prices a unified BabyBear⁶ candidate in `(2^-138,2^-137]`; `MixedFieldBudget` proves the old base/Ext4 split is only 16 bits and Ext6+Ext4 only 75. `GateFactoredExt6` proves exact seven-operand provenance, degree-2 rounds, trace functionals, and η aggregation. | The Rust succinct verifier is an unverified prototype, not a refinement. Coherent proximity, base-subfield sampling, CR/shared-ROM, generated verifier wiring, recursion, and PoW composition remain before calling 137 bits deployed. |

## What runs today

The default Rust path is CPU-only and has a one-call API:

```text
Lean-emitted descriptor
    -> deterministic trace
    -> trace commitment
    -> Fiat–Shamir gate sumcheck
    -> trace-derived Reed–Solomon word
    -> Fiat–Shamir FRI commitments and queries
    -> reference verification
```

The verifier derives its challenges from one transcript and checks the first FRI commitment
against the Reed–Solomon encoding of the supplied trace. This closes a useful executable loop, but
the proof literally contains the entire witness trace and verification recomputes the whole trace
encoding. It is therefore **non-succinct, non-zero-knowledge, and not a production prover**. The
current hash permutation still uses a small conformance/demo parameter set, but the former
scalar-root wound is closed at the runtime representation layer: roots and authentication paths are
nine canonical BabyBear limbs, absorbed with a fixed-width, domain-separated transcript encoding.
That carrier has sufficient cardinality for a 248-bit range; it does **not** make the demo hash a
248-bit collision-resistant commitment. `Compiler/WideDigestAir` now pins the exact eleven-field
encoding through the emitted constraint system. Raw byte decoding, its wire-sharing composition
with the recursive sponge/full verifier, concrete permutation/capacity analysis, and `[COMMIT-CR]`
remain.

The next-generation reference surfaces are now executable as separate joined APIs:

```text
binary history:  evaluation claim (additive OOD PCS)
              -> sampled GF(2^64) append fold
              -> one fixed-size output claim

succinct gates:  emitted descriptor + public inputs + one trace root
              -> Ext6 gamma + degree-2 factored-selector sumcheck
              -> seven terminal trace functionals + fresh eta
              -> one aggregated committed-trace opening
              -> sampled multiplicative MLE terminal verification
```

The new gate verifier receives neither trace nor residual table. Lean proves that seven sparse
selector operands have exactly the emitted descriptor's gamma-batched cube sum, that their outer
sumcheck has individual degree two, and that their terminal values are public affine trace
functionals. Rust binds those seven equations, the entire public prefix, and padding zeros with one
fresh eta, then opens the aggregate against the same trace root fixed before gamma. Sampled
round-zero checks reject non-base Ext6 witnesses. Coherent proximity, subfield sampling, CR/ROM,
and executable refinement remain explicit rather than being mistaken for code-level completion.

`nextgen_light_client` packages the binary evaluation-history proof and the succinct gate proof
into one verifier object. A versioned, length-framed u16/BabyBear encoding binds both complete input
evaluation statements and the append-derived output claim as the private gate trace's public prefix;
valid proofs for different metadata cannot be spliced. This is a depth-independent conjunction,
not recursive compression: the binary append, output OOD, and Ext6 gate transcript schedules remain
domain-separated components whose shared-ROM composition is explicit.

`proof_carrying_history` takes the stronger arbitrary-functional append, verifies the same succinct
gate conjunction, and deterministically reconstructs its `semantic_receipt` envelope. The GF(2)
root is the actual append accumulator; Ext6 is the gate proof backend rather than a fictitious
cross-characteristic fold lane. A focused two-node chain rejects predecessor-proof, turn-metadata,
and transcript-suite substitution. The remaining step is a real unbounded hiding/knowledge-sound
outer accumulator over this now-concrete common relation.

On the formal side, `Assurance/SemanticReceiptRelation` gives that phrase exact content: touched
bits are Boolean; `(1−touched)·(post−pre)=0` enforces the frame; the zero set is iff a genuine
`ReceiptDelta`; and two valid fixed-shape words enter and fold through Loom's actual `AccClaim`.
`Assurance/SemanticTurnReceipt` now makes admission precede that projection: a commit carries
authorization for the exact request, exact effect/delta semantics, permitted disclosures, and
bound roots; reject has no post-state. `SemanticReceiptRuntimeCodec` proves the
`binding ++ 3*k+slot` layout, injectivity of the fixed 32-byte packing, and bound-claim fold.
`Compiler/SemanticTurnReceiptDescriptor` compiles that existing relation through the existing AIR
and emit path and produces the first-order deployment artifact. The handwritten Rust typed-turn
verifier and lookup receipt adapter were deleted. Complete header-preimage/auth/effect/disclosure
emission and the WARP IOR/decider/extractor remain.

`semantic_receipt_relation` is the matching exhaustive Rust reference. It checks the same
quadratics, canonically lifts the header-bound BabyBear semantic word into Ext6, commits the exact
word with the binary cSHAKE Merkle suite, and constructs the coordinate accumulator claim. Both
roots are transcript-bound before one atomic Ext6 challenge drives the committed cross-word fold.
This closes the executable field-consistency join, while deliberately leaving code membership,
sampled proximity, shared-ROM composition, the full typed-envelope codec refinement, and WARP
extraction open.

The optional `wgpu-fold` feature contains a BabyBear⁴ WGSL fold that is bit-for-bit conformance
tested against the CPU fold on supported hardware. It is not a dependency of proving or
verification and is not the architectural center of the project.

Conformance is not verification: the Rust tests compare executable behavior with Lean-authored
vectors and theorem-defined formulas, but there is no formal semantics of Rust or WGSL in the
trusted argument.

## The next-generation pillars

The active direction is to make the strongest pieces meet at one honest end-to-end boundary:

- **Rates:** use the unconditional half-threshold route now, formalize the algebraic core behind the
  landed exact Haböck interface (or keep it visibly conditional), and tie every above-Johnson claim
  to exact hypotheses rather than extrapolating to capacity.
- **Proximity:** compose the landed characteristic-two adaptive/coherent theorem with the concrete
  binary commitment/XOF execution and replace handwritten protocol control with Lean emission.
- **Tower arithmetic:** finish formal additive tower distance preservation; keep optimized Rust only
  as unverified compute behind generated interfaces;
  the sampled prover, cSHAKE transcript, OOD PCS, and fast transform now exist.
- **Accumulation:** lower the now-landed proof-verified arbitrary-functional history node into the
  common WARP/FACS relation, then replace its explicit proof chain with the intended unbounded
  hiding/RBR extractor and final-compression composition.
- **Gate provenance:** refine the landed succinct factored-selector/trace-opening protocol to Lean,
  close its coherent-proximity and base-subfield sampling composition, and join it to final FRI.
- **Deployed ZK:** instantiate the staged roots-before-query game with hiding committed-word-
  knowledge proofs and discharge its explicit shared-ROM fresh/hit/sampling ports; never revive the
  vacuous existential or refuted hidden-state targets.
- **Security:** compose the selected cSHAKE/Ext6 transcript, commitment CR, PoW if wanted, and
  recursive verifier in one execution before attaching the idealized 137-bit label to runtime.

## Design point and performance thesis

minidregg is not trying to become a second general-purpose Plonky3. Its intended design point is a
**transparent, post-quantum, receipt-native proof-carrying history system**: binary/word-oriented
computation, cheap incremental accumulation, straightline extraction at arbitrary history depth,
and final succinct compression only where a light client needs it.

The plausible performance wins are therefore workload- and layer-specific:

| Comparison | Where minidregg could win | Where it should currently expect to lose |
|---|---|---|
| **Plonky3** | Native receipt constraints, binary/word-heavy traces, and an additive-FRI path with fewer constraints and less memory traffic; appended history links that fold claims instead of recursively proving a verifier. | Generic prime-field AIR throughput, mature SIMD/parallel kernels, ecosystem, and every end-to-end benchmark today. |
| **Mina Pickles/Kimchi** | Transparent/PQ assumptions, parallel hash-based proving, and amortized per-link work without a curve-cycle verifier circuit at every link. | Mature recursive composition, compact deployed proofs, verifier latency, and application tooling until final compression is real. |
| **Binius64 / Flock** | Receipt-native accumulation, mechanized depth composition, and integration with the proof-native kernel. | Raw Boolean/hash throughput unless the additive backend adopts comparable word-level arithmetization, packed fields, and whole-pipeline optimization. |

The GF(2) tower earns its place only by delivering those concrete effects: XOR as addition,
64-bit word-level constraints instead of bit-by-bit expansion, recursive Fan–Paar arithmetic,
power-of-two additive domains, packed SIMD, and a cache-efficient additive NTT. Binius64 provides
direct evidence that this architecture can beat Plonky3 on some binary workloads, while the newer
Flock results show that the frontier already demands protocol-level specialization rather than a
fast field kernel alone.

Before claiming a performance advantage, the project must publish reproducible gates for:

1. constraints and bytes moved per native receipt/hash workload;
2. appended-link prover time and peak memory as history depth grows;
3. single-machine and distributed scaling efficiency;
4. final proof size and light-client verification time after compression; and
5. all of the above at the exact proved rate and security parameters.

The checked-in [performance ledger](docs/PERFORMANCE.md) starts with the deliberately slow
full-trace reference baseline so each replacement has a fixed workload and output schema to beat.

## Trust and claim discipline

Lean proves mathematical statements at their declared interfaces. Some interfaces are idealized
or conditional: random-oracle behavior, concrete commitment/hash security, imported proximity
results, and connections between abstract games and a deployed transcript. The source keeps those
boundaries named, with small-field firing examples and false neighboring statements where useful.

The compiler result is similarly precise: for an emitted descriptor, `descriptorHolds` is
equivalent to the Lean gate system. It does not by itself prove that an arbitrary external prover
checks the descriptor soundly. That final implication inherits the proof-system and cryptographic
bridges above.

## Primary literature

- [WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification (2024/1586)](https://eprint.iacr.org/2024/1586)
- [Linear-Time Accumulation Schemes / WARP (2025/753)](https://eprint.iacr.org/2025/753)
- [Proximity Gaps for Reed–Solomon Codes / BCIKS (2020/654)](https://eprint.iacr.org/2020/654)
- [All Polynomial Generators Preserve Distance with Mutual Correlated Agreement (2025/2051)](https://eprint.iacr.org/2025/2051)
- [On Proximity Gaps for Reed–Solomon Codes (2025/2055)](https://eprint.iacr.org/2025/2055)
- [A note on mutual correlated agreement for Reed–Solomon codes (2025/2110)](https://eprint.iacr.org/2025/2110)
- [On Reed–Solomon Proximity Gaps Conjectures — capacity counterexamples (2025/2046)](https://eprint.iacr.org/2025/2046)
- [FRI Soundness Above the Johnson Bound via Threshold Halving (2026/858)](https://eprint.iacr.org/2026/858)
- [Action–Orbit FRI Soundness Above the Johnson Radius (2026/861)](https://eprint.iacr.org/2026/861)
- [Succinct Arguments over Towers of Binary Fields / Binius (2023/1784)](https://eprint.iacr.org/2023/1784)
- [Binius64 architecture and reproducible benchmarks](https://www.binius.xyz/benchmarks/)
- [Flock: Fast Proving for Batch Boolean Computations (2026)](https://arxiv.org/abs/2607.27491)

OpenAI's 2026 [binary and spherical code bounds](https://openai.com/index/ten-advances-in-mathematics/)
are also relevant as research calibration: they were generated by an internal version of
**Astra** (the “Sol” reference is API-rate costing), and give stronger asymptotic upper bounds.
They are not a direct Loom ingredient: a tower-field symbol expanded in a binary basis can have
bit weight anywhere from 1 to the extension degree, so symbol distance, list recovery, and FRI
proximity do not transfer without a proved inner encoding. Their present value here is as a ceiling
for future concatenated binary-code designs and as proof-certificate inspiration, not as a protocol
soundness claim.

## Repository map

| Directory | Role |
|---|---|
| `Theory/` | Candidate-independent codes, finite fields, GF(2) towers, and additive transforms. |
| `Loom/` | Sumcheck, RS proximity/FRI, accumulation, Fiat–Shamir, extraction, and ZK games. |
| `Compiler/` | AIR DSL, flattening, gadgets, emit/serialization, and verifier components. |
| `Assurance/` | Cross-layer statements, manifests, and explicit security budgets. |
| `Kernel/`, `Effects/`, `Pred/` | The proof-native application/computation substrate. |
| `prover/` | Unverified Rust reference compute plus the opt-in WGPU fold experiment. |

## Build and test

```sh
lake build Minidregg
lake env lean Loom/HalfThresholdFriTower.lean

cd prover
cargo test
cargo test --features wgpu-fold
cargo run --release --features wgpu-fold --bin fri_fold_bench
```

GPU tests skip cleanly when no compatible adapter is available.

## Reading order

1. [`GOAL.md`](GOAL.md) — the live theorem/residual ledger.
2. [`docs/LOOM-COMPLETE.md`](docs/LOOM-COMPLETE.md) — what “complete” means at each proof resolution.
3. [`Assurance/LoomV0Manifest.lean`](Assurance/LoomV0Manifest.lean) — the machine-checked v0 index.
4. [`docs/PROVER-PLAN.md`](docs/PROVER-PLAN.md) — the current reference-prover surface and its next bridges.
5. [`ATLAS.md`](ATLAS.md) — architecture and design history.
