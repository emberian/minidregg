# minidregg

**A Lean-first laboratory for proof systems, derived arithmetization, and proof-native
computation.**

minidregg develops three things together:

1. **Loom**, a machine-checked proof-system model built around Reed–Solomon proximity,
   accumulation, sumcheck, Fiat–Shamir, and zero-knowledge/extraction games;
2. a **derived AIR compiler and emit seam** whose first-order descriptor is proved to mean the
   same thing as the Lean gate system; and
3. **Lean-owned semantic manifests and controllers** around a shrinking set of unverified native
   arithmetic, transform, and hash kernels.

Lean is the sole source of semantic meaning, protocol control, and acceptance. Rust is either
mechanically generated data-only DTO/dispatch glue or opaque untrusted computation behind a
Lean-owned interface. The project has no Rust operational semantics, so native code is never a
refinement and never decides whether a receipt is accepted.

The stable clean-sheet architecture and ordered construction plan live in
[`PROJECT.md`](PROJECT.md); [`GOAL.md`](GOAL.md) is the evidence/status ledger.

## Why Loom?

Loom is the proof-theoretic composition and assurance layer for a heterogeneous semantic computer,
not a universal field, VM, or demand to invent every prover component ourselves. Boolean words,
ordinary fields, residue-ring FHE, MPC shares, lookup/RAM, privacy, and history should keep their
native proof dialects. Loom owns the joints they otherwise leave informal: roots-before-challenges
control, explicit rate/error regimes, checked common-opening representation relations, native
failure non-authority, exact clause evidence, and proof-carrying-history attribution.

That choice is deliberately falsifiable. If one formalizable stack supplies the same heterogeneous,
straight-line-knowledge, ZK, and history guarantees with less machinery—or if the shared controller
does not remove duplicated joins and benchmark competitively—we should replace Loom. See
[`D-0004`](docs/decisions/D-0004-why-loom.md) for the decision, evidence milestones, and kill
criteria.

This is a frontier research stack, not a production prover. Preserving a historical native or GPU
path is **not** a project goal. Acceleration is an implementation choice downstream of a
Lean-owned protocol. The old BabyBear⁴/FRI/WGPU experiment has been deleted rather than retained as
a second, handwritten protocol profile.

## Status at a glance

| Surface | What has landed | Exact boundary |
|---|---|---|
| **Derived arithmetization** | `Compiler/Air` proves the executor and circuit readings agree; flattening produces degree-≤2 gates; `Compiler/Emit` produces a serializable descriptor with `emit_faithful`. `Theory/Bignum` owns fixed-width little-endian limbs, and `Compiler/AirBignum` emits range-checked carry addition with exact integer soundness and overflow rejection. | This proves what emitted constraints mean, including the landed bignum addition gadget. Rust/WGSL has no semantics here: it is unverified compute whose outputs must be rechecked by Lean-owned control. Multiplication and broader application-language lowering remain separate work. |
| **Multiplicative RS proximity** | Ordinary unique-decoding results, an unconditional one-third-UD band, and `HalfThreshold*`: one round halves the radius outside at most one field challenge, followed by a proved UD tail. The committed transcript, adaptive earliest-deviation argument, and coherent runtime-shaped query paths are assembled at `m·b/|F| + (1−τ)^q`; the rate-1/2 `δ=3/10 → 3/20<1/6` specialization is machine-checked. | Concrete Merkle collision resistance and the single-ROM Fiat–Shamir reduction remain cryptographic/composition floors. The coherent theorem is multiplicative; it is not silently reused for characteristic-two additive folding. |
| **Johnson/list regime** | `JohnsonRegime` proves the list-size inequality and exact sampling amplification. `JohnsonMcaBridge` imports the exact theorem interface and constants from Haböck 2025/2110, corrects the paper/Loom degree convention to `ρ_H=(d−1)/n`, and proves that one `m=max(3,d)` instance covers Loom's rounded Johnson target. | The hard BCIKS/GS/Hensel algebraic proof is still the explicit proposition `HaboeckTheorem2`, not a local theorem or axiom. Thus the Johnson MCA seam is exact and conditional, not yet machine-proved end to end. There is **no blanket capacity claim**: capacity-level variants have counterexamples. |
| **GF(2) tower and additive FRI** | `Theory/BinaryTower*` proves the tower/fold algebra; `Loom/AdditiveProximity`, `AdditiveFriTower`, and `AdditiveFriQuery` close the literal characteristic-two quotient tower, adaptive earliest-deviation cover, authenticated coherent paths, and the UD bound `m·2^(ell−1)/|F| + (1−τ)^q`. `Compiler/AdditiveFriReceiptClause` binds the manifest declaration, reversed/high-first basis order, affine domain and rate schedule, roots-before-challenges, coherent queries, terminal, and exactly that ideal predicate/bound. | Concrete commitment binding/CR, cSHAKE-ROM transport, validation of native arithmetic buffers, an instantiated online controller, and the outer accumulator remain explicit. The generic clause is not an admitted base-V1 runtime clause. Rust retains opaque compute, but tower/LCH/field representations and the selected hash algorithm are not yet generated or checked from Lean pins. |
| **Indexed lookup** | `LogupIndexLink` proves decoded Boolean address columns give literal unit-vector incidence and exactly the LogUp* pushforward. `Compiler/Logup256ReceiptClause.indexedTableReceiptClause` derives the exact indexed evaluation from a committed semantic trace behind explicit Tower256 arithmetic, PCS-opening, transcript-order, CR, and ROM premises. Native Tower256 retains arithmetic kernels only. | V1 now declares distinct `gf2Tower256Carrier` profile `205`, degree `256`, and codec `21`; clause `404` selects it in a locally extended manifest. The clause remains absent from base-V1 clauses, and the pin proves no Rust representation correspondence. External premises, proximity/composition, online control, and mutable state remain. |
| **Accumulation** | Loom proves claim folding, exact/UD soundness, arbitrary-depth extraction, and depth composition. `SemanticHistoryAccumulator` requires exact controller-resolved clause evidence and preserves one folded `AccClaim`; `SemanticHistoryStraightlinePcs` supplies its prefix-root extraction interface. `SemanticHistoryWARPAdditiveJoin` now commits each exact link word before its challenge, commits the literal post-challenge fold, projects the opened stream to the unshifted BCS word schedule, and identifies the terminal fold root with `SemanticAdditiveFriCheckpoint`'s level-zero root. | The history head remains proof-relevant and retains its entries. Invoking the full `AccRbrBcs` reduction still needs the exact reindexing of the genesis/link `AccClaim`s, plus its PCS/MCA/ROM/commitment premises; the additive and knowledge ledgers are not yet united in one game. This is not yet a concrete WARP/FACS deployment, sampled decider, hiding schedule, or succinct history object. |
| **Zero knowledge and extraction** | Lean formal games, constrained masking, corrected OracleLog assembly, and sub-UD recovery are checked. `OracleLogLinkedTwoPhase*` freezes checked root preimages before a domain-separated query, binds the response to that query, transports accepted transcripts into sub-UD log extraction without `d≤t`, and assembles exact full-domain and allowed-coordinate sampling prices. | The staged reduction still exposes explicit shared-ROM fresh/hit/sampling ports. A concrete hiding deployment needs ZK proofs of committed-word knowledge rather than transparent all-word openings, plus CR/ZK errors; Rust is not ZK. |
| **Assurance arithmetic** | `ErrorBudget120` prices a unified BabyBear⁶ candidate in `(2^-138,2^-137]`; `MixedFieldBudget` proves the old base/Ext4 split is only 16 bits and Ext6+Ext4 only 75. Lean proves `X^6−31` irreducible, and `GateFactoredExt6` proves exact seven-operand provenance, degree-2 rounds, trace functionals, and η aggregation. | Base V1 admits no proof dialects at all. Ext6 still needs its own concrete Lean controller, coherent proximity, base-subfield provenance/sampling, commitment/transcript/opening control, final LDT, CR/shared-ROM, recursion, and PoW composition before calling 137 bits deployed. |
| **BFV/residue-ring clause** | `Compiler/BfvReceiptClause` binds one committed witness and the ordered 384-row modulus-major equation family. `Assurance/BfvNativeBufferAdmission` emits one combined scalar/accumulator descriptor per row, treats native failure as blocking, checks every returned buffer and row link in Lean, constructs the 384-row token/private receipt event, and derives each exact signed `Int` equation under an inhabited local manifest/controller binding. | The local proof-suite pin is still deliberately unassigned, so this closes arithmetic buffer admission and receipt projection—not privacy, knowledge soundness, commitment binding, or an end-to-end FHE proof system. |
| **Semantic kernel and control** | `CanonicalTransition` derives one canonical materialized post and typed delta from validated patches. `AcceptedCellEffect` makes ZK/MPC/FHE completion a request-authorized cell effect, sealed by default, rather than receipt decoration. `DeclaredHyperedge` executes a flat finite family of one-target incidences over one pre-state/shared apex, checks joint authorization and exact aggregate balance, composes one canonical post, projects an actual `Kernel.Hyperedge`, and rejects nonzero aggregate deltas. This is the new call-forest replacement carrier. Generated manifests/controllers still expose only data and opaque fallible work to Rust. | Durable CAS/nullifier insertion remains an external handler boundary. The full receipt/history projection of a committed hyperedge, one canonical authorization-state projection, production dialect controllers, and emitted authenticated-column control remain. Legacy single-incidence and compatibility modules still exist; landing the new carrier does not itself migrate a UI/runtime or prove external atomic storage. Manifest pins are registry facts, not cryptographic verification. |

## What runs today

There is deliberately no authoritative Rust one-call prover/verifier API now. The former
full-trace `reference_prove` / `reference_verify` composition and its benchmark were deleted because
they authored transcript and acceptance semantics in Rust. `prover/src` now contains only
unverified field/tower arithmetic, linear/MLE/lookup kernels, transforms, and parameterized
cSHAKE data operations. The protocol wrappers for gate
sumcheck, MLE openings, LogUp, Fiat--Shamir, receipts, and proof history have been deleted. Lean owns
the relations, manifests, plans, codecs, and emitted descriptors.

“Kernel” does not yet mean “free of handwritten conventions.” The remaining LogUp arithmetic takes
scatter positions, probe points, and challenges from its caller. `hash_kernels` fixes only the
named cSHAKE256 algorithm while complete framing and output width are caller data; `mle_kernels` fixes
index/domain transforms; and the tower/Ext6 modules fix representation conventions. These are
untrusted candidate compute and generation/deletion debt. They acquire no semantic authority from
resembling a Lean formula and cannot be admitted until Lean-owned control pins or rechecks the
exact conventions.

The generated [`prover/generated/semantic_artifact_v1.rs`](prover/generated/semantic_artifact_v1.rs)
is a separate DTO seam: it contains canonical artifact constants, four data structures, and
`run_arithmetic`/`run_hash`/`run_transform` dispatch only. It does not validate the JSON or native
reply and does not construct a statement, transcript, verdict, or receipt. It is now compiled as
`prover::semantic_artifact_v1`, but no dispatch implementation yet connects its generated work
requests to native kernels.

The lookup carrier mismatch is now corrected at the artifact-data level: V1's Lean bundle, JSON,
and generated Rust payload include profile `205` at degree `256` with codec `21`, and the local
lookup clause selects it instead of degree-64 `gf2Carrier`. Clause `404` is still extension-only,
and profile identity alone does not validate native `Tower256` limb/basis representation.
The base generated artifact contains no dialect IDs. `Compiler.DialectClauseDispatch` separately
requires a controller entry for every admitted manifest clause, resolves its exact carrier/codecs/
bridges, treats native transport failure as blocked, and lets only the resolved Lean checker produce
the outcome. `Compiler.MinidreggV1ArithmeticWork` is the concrete non-vacuity tooth: its local
manifest adds arithmetic clause `406`, its honest `0+0=0` buffer reaches the generic Lean
certificate, and an opaque native error can only block. `Compiler.SemanticController` is the first Lean-executable authority model at the fixed
frame-nucleus descriptor boundary: for every arbitrary
native oracle, its only successful outcome carries exact-request authorization, the bound semantic
receipt relation, and descriptor acceptance. The native reply has no acceptance bit.

The former sampled binary-history/OOD API is deliberately absent. Its verifier checked local fold
consistency but never used the advertised coefficient bound, so it was not a low-degree test and
could make a false OOD claim pass with a pointwise quotient. Reintroduction requires a Lean-emitted,
genuinely rate-aware additive-FRI controller and a re-derived OOD theorem.

The proved Ext6 gate algebra is:

```text
emitted descriptor
    -> gamma-batched residual relation
    -> seven factored operand tables
    -> degree-2 sumcheck terminal
    -> eta-batched linear functional
```

Lean proves that seven sparse
selector operands have exactly the emitted descriptor's gamma-batched cube sum, that their outer
sumcheck has individual degree two, and that their terminal values are public affine trace
functionals. A commitment/opening, roots-before-challenge controller, coherent proximity and
subfield proof, CR/ROM composition, and final LDT remain. The former native verifier composition
was deleted rather than being mistaken for code-level completion.

The old `nextgen_light_client` conjunction was deleted with the unsound binary admission branch.
Only Ext6 arithmetic kernels survive on the native side; no Ext6 proof or verifier composition is
currently exported. A Lean-owned controller and one real outer accumulator remain.

On the formal side, `Assurance/SemanticReceiptRelation` gives that phrase exact content: touched
bits are Boolean; `(1−touched)·(post−pre)=0` enforces the frame; the zero set is iff a genuine
`ReceiptDelta`; and two valid fixed-shape words enter and fold through Loom's actual `AccClaim`.
`Assurance/SemanticTurnReceipt` now makes admission precede that projection: a commit carries
authorization for the exact request, exact effect/delta semantics, permitted disclosures, and
bound roots; reject has no post-state. `SemanticReceiptRuntimeCodec` proves the
`binding ++ 3*k+slot` layout, injectivity of the fixed 32-byte packing, and bound-claim fold.
`Compiler/SemanticTurnReceiptDescriptor` compiles that existing relation through the existing AIR
and emit path and produces the first-order deployment artifact. The handwritten Rust typed-turn
verifier and lookup receipt adapter were deleted. `SemanticHistoryAccumulator` now closes the
proof-relevant semantic append and exact full-opening decider/extraction layer; complete
header-preimage/auth/effect/disclosure emission and the succinct WARP IOR/PCS remain.
`SemanticHistoryStraightlinePcs` advances the latter only to an exact external interface: it binds
prefix-scheduled roots and literal fold words to the same carrier/index, then extracts the semantic
head from one accepted transcript outside a caller-priced failure event. It does not instantiate
the PCS, reduction, transcript ROM/CR argument, sampled decider, or hiding schedule.

The newer executable transaction seam is `Theory.DeclaredTurn`: it derives the effect digest and
pre-state root from one request seed, a typed `EffectDeclaration.Declaration`, and canonical
pre-state; checks authorization first; and recomputes the post-root. Its account-move projection is
`Compiler.DeclaredEffectArtifact`, not the older generic `Effects.EffectSpec` projection.
`Theory.ReactiveCellTransition` joins reactive decisions to validated patches and exposes durable
physical commit only through `HandlerPremise`. `Assurance.DeclaredTurnReceipt` now supplies the
bounded join from declared execution into `SemanticTurnReceipt` and `SemanticHistoryAccumulator`:
its `executeCore` has no receipt/witness argument, and `canonical_core_exact` plus
`historyClaim_core_exact` pin the accumulated core. The remaining manifest/header/code-membership,
reactive, dialect-clause, and emitted-controller obligations are still explicit.
`Assurance.PrivateComputationReceiptClause` closes one disclosure edge without inventing a proof
system: `ReceiptEvent.ofCompletion` preserves the existing authorization, representation-identity,
computation, and release evidence; `recordCompletion` attaches it to a committed turn; and
`rejected_not_released` plus `empty_disclosures_not_released` fail closed. Its portal evidence and
manifest pins remain abstract boundaries.

`Theory.TurnTransition` unifies ordinary declared and resumed reactive execution without erasing
their dependent types: `control` delegates to the two existing Lean controllers, refusal and block
materialize to the pre-cell, and `TransitionFacts` exposes canonical roots, exact footprint,
`ReceiptDelta`, and frame law. It does not admit history or perform physical commit.

The former Rust receipt-relation and proof-history wrappers were deleted. Their replacement is not a
new mirror: it is a Lean-owned manifest/controller whose only native interface is bounded compute
calls and replies, followed by Lean-side checks and construction of the sole verified receipt token.

Conformance is not verification: the Rust tests compare executable behavior with Lean-authored
vectors and theorem-defined formulas, but there is no formal semantics of Rust or WGSL in the
trusted argument.

## The next-generation pillars

The active direction is to make the strongest pieces meet at one honest end-to-end boundary:

- **Rates:** use the unconditional half-threshold route now, formalize the algebraic core behind the
  landed exact Haböck interface (or keep it visibly conditional), and tie every above-Johnson claim
  to exact hypotheses rather than extrapolating to capacity.
- **Proximity:** instantiate `AdditiveFriReceiptClause` with concrete commitment/XOF execution and
  Lean-emitted online control; its current predicate and bound are exact but idealized.
- **Tower arithmetic:** keep the proved additive tower and optimized native arithmetic/transform
  kernels, then emit the rate-aware FRI/OOD controller from Lean before any binary receipt is
  admissible again.
- **Accumulation:** instantiate a real WARP/FACS PCS, transcript reduction, and sampled decider
  behind the landed `SemanticHistoryStraightlinePcs` interface. Its prefix-typed roots,
  one-transcript extractor, exact erasure join, and error-ledger shape are real; the PCS, ROM/CR
  reduction, and hiding schedule are external. The retained-entry/full-opening history is still not
  succinct.
- **Lookup and gate clauses:** admit the locally pinned LogUp clause into a generated controller
  only after discharging its explicit Tower256/PCS/CR/ROM boundaries; replace the opaque Ext6 V1
  pin with a concrete clause around the landed factored-selector algebra, then close coherent
  proximity, base-subfield provenance, and final FRI.
- **Deployed ZK:** instantiate the staged roots-before-query game with hiding committed-word-
  knowledge proofs and discharge its explicit shared-ROM fresh/hit/sampling ports; never revive the
  vacuous existential or refuted hidden-state targets.
- **Security:** let Lean select and schedule the parameterized cSHAKE/Ext6 transcript, then compose
  commitment CR, PoW if wanted, and a recursive verifier in one execution before attaching the
  idealized 137-bit label to runtime.

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

No Rust behavior participates in that semantic argument. Generated Rust glue is a first-order DTO
and opaque-dispatch projection of a Lean artifact; handwritten Rust is only untrusted computation.
Conformance tests can find bugs but cannot establish refinement, protocol meaning, or acceptance.

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
| `prover/` | Opaque, untrusted, caller-parameterized arithmetic/transform/hash kernels. |

## Build and test

```sh
lake build Minidregg
lake env lean Loom/HalfThresholdFriTower.lean

cd prover
cargo test
```

## Reading order

1. [`GOAL.md`](GOAL.md) — the live theorem/residual ledger.
2. [`docs/LOOM-COMPLETE.md`](docs/LOOM-COMPLETE.md) — what “complete” means at each proof resolution.
3. [`Assurance/LoomV0Manifest.lean`](Assurance/LoomV0Manifest.lean) — the machine-checked v0 index.
4. [`docs/PROVER-PLAN.md`](docs/PROVER-PLAN.md) — the current native-kernel boundary and ordered Lean-control joins.
5. [`ATLAS.md`](ATLAS.md) — architecture and design history.
