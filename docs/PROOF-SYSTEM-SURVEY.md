# PROOF-SYSTEM-SURVEY — the backend decision (ATLAS §8, decision 2)

*Synthesized 2026-08-07 from a three-lane literature survey (hash-based systems ·
folding/accumulation · formalization landscape), all sources live-fetched Aug 2026,
formalization repos cloned and sorry-counted. Eprint numbers throughout.*

## 0. Executive recommendation

**A small-field, sumcheck-centric, hash-based stack, priced only at proven bounds:**

- **Arithmetization front:** Spartan/CCS-shaped (sumcheck over the effect
  descriptors) — sumcheck is the most-mechanized protocol in existence and its
  soundness is the exact proof shape mechanization likes (round induction +
  Schwartz–Zippel = the round-by-round invariant).
- **Multilinear PCS, staged:** *(staging revised after the construction-level
  reads — see LOOM-RECOMPOSITION §5/§6)* **WHIR-shaped constrained-claims at
  unique-decoding parameters first** — unconditional end-to-end (CA ⇒ mutual CA
  is free in UD) *with* RBR knowledge soundness, so the straightline law holds
  from v0 — widening to the Johnson bound (unconditional for RS since 2025/2051
  + 2025/2110) purely by re-tagging δ/t/ledger. Basefold is demoted to
  prior-art: its extractor is predicate-forking (2^d reruns) and its soundness
  plain-not-RBR — ineligible under the straightline law; its fold=bind
  invariant survives as the design idea.
- **Aggregation (the product):** straightline-extractable hash-based accumulation
  in the **Arc** 2024/1731 / **WARP** 2025/753 shape, **implemented and mechanized
  by us as the aggregation layer from the start** — straightline ROM extraction
  makes **unbounded-depth PCD a theorem**, which no rewinding-based scheme honestly
  offers at our use case. The gate to deploying it is our own machine-checked
  soundness (straightline RBR knowledge soundness; erasure-correction extraction),
  not anyone's audit. In-circuit recursive verification survives only as the final
  compression step where a light client wants one small proof, never as the
  per-link aggregation mechanism.
- **Transcript layer:** Poseidon2-class sponge as the ROM; Fiat–Shamir/BCS done
  **once over the whole compiled protocol** with round-by-round soundness as the
  non-negotiable invariant (2025/118's practical FS attacks are on protocols that
  skipped exactly this). *(Corrected after the full read of 2024/1724: the
  Rotem–Tessaro transforms are concretely infeasible at sumcheck round counts —
  their cost is governed by the special-soundness tree size N = (d+1)^{log n}.
  Where RBR knowledge soundness holds, FS-of-RBR already gives straightline
  extraction from one transcript; R–T stays on the shelf for hypothetical
  constant-round non-RBR components, where its Merkle-instantiated variant
  uniquely offers polynomial-loss QROM soundness. See LOOM-RECOMPOSITION §2.)*
- **No curves anywhere. No DLOG, no pairings, no trusted setup, no AGM, no curve
  cycle, no 255-bit fields.** PQ-plausible throughout.

## 1. The November 2025 event (why the timing is on our side)

- **2025/2046** (Crites–Stewart) **disproved the capacity-regime conjecture family**
  for RS proximity gaps — BCIKS correlated agreement up to capacity, WHIR's mutual
  correlated agreement up to capacity, and the DEEP-FRI list-decoding conjecture all
  fall in their strongest published forms. Breadstuffs' floor quoted "130 bits
  conjectured / 73 proven" — the conjectured side of that pair is now *falsified
  as stated*, not merely unaudited. Vindication of the pessimistic-number law.
- **2025/2051** (Bordage–Chiesa–Guan–Manzur) + **2025/2110** (Haböck) made the
  **Johnson regime unconditional** for STIR/WHIR (all polynomial generators satisfy
  MCA up to Johnson). The honest regime got *stronger* the same week the optimistic
  regime died. **2026/1367** (SoK) now states our exact thesis as the field's:
  the proven-vs-conjectured axis is the load-bearing, least-reported dimension.
- Caution: post-upheaval eprints claiming to beat Johnson (2026/858, 2026/861,
  2025/1712) are unvetted; 2025/1712 is in direct tension with the disproof. Build
  on none of them.

**Law for minidregg: we deploy at the parameters we can prove, and the proven number
is the only number that appears anywhere.** (~2–4× prover cost vs the dead
conjectures — the anti-laundering premium, worn visibly.)

## 2. The depth wound and the straightline escape

Every rewinding-extraction scheme — **including Pickles/IPA and the whole
Nova/HyperNova/ProtoStar line** — has knowledge soundness proven only at
constant/log recursion depth. Polynomial depth (= whole-history aggregation, our
product) is rescued only by the Extended AGM (uninhabited idealization — the exact
laundering shape ATLAS forbids) or the osROM (honest but strictly stronger than
ROM) [2024/232, 2025/1413, 2025/1663]. A Nova-style scheme *forgeable at poly
depth* while satisfying the standard definition has been constructed [2024/232].

The 2024–26 hash-based accumulation line (**Arc**, **WARP**; ancestor 2024/474)
extracts **straightline in the ROM** — no rewinding, so depth composes additively
and **unbounded-depth PCD is a theorem**. WARP: linear-time prover, log-time
verifier, any linear code, extraction via *erasure correction* (no list-decoding
machinery in the knowledge proof — markedly mechanization-friendly). Recursive
circuit = Merkle openings + field ops; decider = one final proximity check.

Pickles remains the **reference semantics and know-how quarry** (step/wrap,
deferred values, the sg accumulator — we know it deeply), not the mechanization
target: its floor needs forking-lemma tree extraction (zero Lean precedent),
DLOG (not PQ), a forced curve cycle, and carries the depth gap at our use case.

## 3. The formalization landscape (ground-truthed by cloning)

**Nobody anywhere has a fully mechanized soundness proof of a complete succinct
argument** (IOP + commitment + BCS + FS). The field's scaffolds are large and open;
its finished results are small, parameterized, and honest.

**Ownership stance (ember, 2026-08-07): the whole tower is ours.** No Lean
dependencies beyond mathlib — no vendored VCV-io, no ArkLib. External projects are
*prior art to study*, never load-bearing. This is cheaper than it sounds: we need
one instantiation, not a framework, and straightline extraction **eliminates the
forking/rewinding machinery entirely** — the hardest thing the external carriers
offer is machinery we never invoke. Our ROM carrier is a lazy-sampling handler +
query bounds + reprogramming for the RBR→FS step: a few-K-line build. Breadstuffs'
in-house record (fixed-parameter FRI soundness, LogUp, chip tables, the hygiene
discipline) is the evidence we hold this class of material ourselves — and do
better, because ours will carry the ATLAS vacuity gates the external scaffolds lack.

| artifact | status (cloned/counted 2026-08-07) | role for us |
|---|---|---|
| **ArkLib** (Verified-zkEVM, Lean 4) | 100,119 LOC, **293 sorries**; IOR architecture (RBR security, lenses, BCS, duplex-sponge FS) defined; headline theorems open (composition 19 sorries, BCS a stub) | **Prior art only.** Study the IOR decomposition; our composition spine is specialized to our one stack (their generality is where their sorries live) |
| **VCV-io** (Lean 4) | 146,057 LOC, 82 sorries; oracle computations as free monad; ROM as *inhabited lazy-sampling handler*; forking lemma without rewindability axioms; FS for sigma protocols | **Prior art only.** The ROM-as-inhabited-handler pattern is the idea worth taking; we build our own minimal carrier (no forking needed — straightline) |
| **simple-rbr-fri** (zksecurity, Hirai) | **4,068 LOC, 0 sorries, 0 axioms**; full FRI RBR soundness + completeness, MCA as named pluggable hypothesis; built solo in ~6 weeks | **Prior art + calibration.** Proof-shape crib; the named-hypothesis pattern is exactly ATLAS's carrier-with-realizer-slot law; 4K lines/6 weeks proves the scale is weeks, not years |
| δ\*/rs-mca; ArkLib BCIKS20 track; LeastAuthority WHIR blueprint | active | The MCA mechanization frontier — our Johnson upgrade path is being built by others |
| S-two AIR soundness (StarkWare, Lean) | shipped, at scale | Precedent that **deployed-AIR ⟸ semantics** scales; their crypto layer stays unverified — ours won't |
| SP1 chip proofs (EF audit: 51/62 complete, real bugs found) | cautionary | Per-chip green ≠ system-verified; the audit-the-claims law again |

**Where minidregg would be first in the world:** (1) soundness composed onto the
*deployed* AIR (breadstuffs' descriptor→AIR pipeline + chip-table + LogUp assets are
stronger starting material than StarkWare had); (2) the **mechanized recursion
obligation** — verifier-as-circuit agreement has no precedent anywhere; breadstuffs'
per-effect circuit⟺executor agreement is the right primitive, aimed at the verifier
itself.

## 4. The honest floor, stated as typed obligations (ATLAS laws 1–4 applied)

Exactly **two named interface hypotheses**, each a carrier with a realizer slot,
never an `axiom`:

1. **Proximity/MCA hypothesis** — pluggable bound, `(1+ρ)/2` unique-decoding regime
   *inhabited today* by elementary proof (breadstuffs' fixed-parameter FRI result
   slots in as an inhabitation witness, not obsolete); Johnson-bound realizer lands
   when the community MCA mechanization (δ\*, ArkLib-BCIKS) completes, or we
   mechanize Haböck 2024/1571 ourselves.
2. **ROM realization** — the oracle is an *inhabited handler* (our own
   lazy-sampling carrier; the pattern is standard); the sole permanently-unproven
   leap is "the deployed Poseidon2 sponge realizes it," stated as the named
   idealization it is. Where Merkle binding can
   ride explicit collision-resistance instead, it does — CR of a compressing hash
   is inhabited and non-vacuous (never an "injectivity" premise false by counting).

Everything else — sumcheck, folding, RBR, BCS/FS reduction, accumulation,
field-faithfulness at the deployed prime — is a theorem. Deployed field chosen once
(BabyBear/KoalaBear/Goldilocks-class; extension field for sampling per Arc's
explicit checkable inequality) and parameterizes the whole development; toys are
type-distinct.

## 5. Tracked alternative

**Neo/SuperNeo lattice folding** (2025/294, 2026/242): Module-SIS at
estimator-checkable parameters (real, inhabited, PQ), Goldilocks-native, no curves,
pay-per-bit commitments, single small-extension sumcheck. Held back by: three months
old, rewinding-style reductions-of-knowledge (depth caveat pending), norm-slack
bookkeeping that must all appear in the theorem statement. Re-evaluate in 6–12
months; the sumcheck front we build is shared with it.

## 6. Rejected, with reasons on the label

- **Pickles/IPA, Nova/HyperNova, ProtoStar/ProtoGalaxy as foundation** — depth gap
  at the product's use case + forking extraction with no mechanization precedent +
  curve cycles/big fields (Pickles stays the semantics quarry).
- **Plonky3-FRI at breadstuffs parameters** — the conjectured regime it priced is
  now falsified; at proven parameters it is strictly dominated by STIR/WHIR.
- **Circle STARKs** — great engineering, deployed self-describedly in a conjectured
  regime, and would double our coding-theory formalization with zero ecosystem help.
- **Binius/Binius64** — no succinct verifier today; unstable target.
- **KZG/Plonk anything** — trusted setup + extractability only in the AGM
  (uninhabited); the EasyCrypt effort's own trajectory shows the wall.
- **DeepFold** — its differentiator was capacity pricing; dead.
- **Ligero/Brakedown as the system** — √n verifier kills recursion (but their
  elementary proofs make a fine first mechanization exercise).

## 7. Decided / remaining

**Decided (ember, 2026-08-07):** the whole tower is ours — no VCV-io, no ArkLib,
prior art only; and accumulation is not gated on external audit — we implement the
accumulator and mechanize its soundness ourselves, and that proof is the gate.

**Remaining:**
1. **Field**: BabyBear (breadstuffs continuity, Plonky3 ecosystem) vs KoalaBear
   (SP1-Hypercube momentum) vs Goldilocks (Neo-compat) — with the Arc/WARP
   field-size inequality satisfied by extension choice either way.
2. **Poseidon2 vs a SHA3-class sponge** for the ROM instantiation leap (circuit
   cost vs cryptanalytic maturity).

## 8. Addendum — the 2026 deep-cut sweep (direct Kagi pass, 2026-08-07)

A second, novelty-targeted search pass beyond the citation graph the three lanes
walked. Verdict: **the recommendation stands and got stronger**; four items join
the plan, several join the watchlist.

**Reinforcing:**
- **2026/782** (Krachun–Kazanin–**Haböck**, Apr 2026) — a *second, independent*
  counterexample to RS proximity gaps near capacity (an affine line at
  θ = 1−ρ−η, η = Θ(1/log n), not θ-close yet containing exponentially many close
  points, over multiplicative subgroups of prime fields). The capacity regime is
  now dead from two unrelated directions (with 2025/2046). Johnson-only pricing
  further vindicated.
- **2025/2041** (Thaler, "Sum-check Is All You Need," Nov 2025–Mar 2026) — the
  field's own opinionated survey lands on our arithmetization choice; its five
  prover mechanisms (batch evaluation, read/write memory checking, virtual
  polynomials, sparse sumchecks, small-value preservation) are the Compiler/
  lane's optimization roadmap. Plus **2026/587** (sumcheck-prover speedups).

**Adopted into the plan:**
- **2024/1724** (Rotem–Tessaro) — straight-line knowledge extraction for
  *multi-round* protocols (sumcheck/folding shapes), ROM **and QROM without
  super-polynomial loss. Now cited in §0 as the transcript-layer extraction
  architecture. (Missed by the lanes: 2024 number, revised 2025.)
- **2026/289** (Zheng–Gao–Liu, ZK-PCD from accumulation) — masking vectors +
  ZK-sumcheck; separates the compliance predicate from accumulation verification
  so no zkNARK is needed. This is the **disclosure dial at the aggregation
  layer**: when receipts must not leak through the aggregate, this is the
  reference technique.

**Watchlist:**
- **2026/538** (Paslis–Ràfols–Zacharakis, holography accumulation) — *stateless*
  recursive proving (accumulates witness-independent public evaluation checks;
  decider collapses to one polynomial evaluation), attacking Arc/WARP's large
  prover-state cost. If our node's accumulator state becomes an operational
  burden, this is the refinement to evaluate.
- **Zinc/Zinc+** (2025/316, 2026/855, Nethermind et al.) — transparent hash-based
  SNARKs over polynomial **rings** (ℚ[X], ℤ[X], F_q[X]) via IPRS codes; matters
  if we ever want native ring/lattice/bitwise arithmetic in-circuit (e.g. PQ
  signature verification inside the light client). Not core substrate.
- **DeepBrake / BrakeWHIR** (2026/1561, Jul 2026) — row-wise RS commitments with
  a consolidated proximity+evaluation check (no sumcheck reduction at opening);
  BrakeWHIR: 2.6× faster verification, 1.9× smaller proofs. PCS-layer
  optimization for the WHIR phase.
- **ProtogaLattice** (2026/1317, Balbás–Nitulescu–Plançon, Jun 2026) — constant-
  round lattice folding, ~4 RO calls/iteration (vs sumcheck-heavy LatticeFold+/
  Neo verifier circuits); the lattice watch-item (§5) keeps maturing. Also
  2026/359 (partial range checks), 2026/1127 (FHE bootstrapping via folding).
- **WHIR-DAS** (camofu/whir-das) — WHIR + the FoDAS compiler for transparent PQ
  **data availability sampling** (Lean-Ethereum data layer); early boilerplate,
  but it is the availability story our storage/light-client layer will want.

**To audit, not adopt — a methodology exercise in our own house style:**
- **iotexproject/rs-proximity-gaps** — a claimed **zero-sorry, zero-axiom Lean 4
  formalization** of "FRI soundness above the Johnson bound via threshold
  halving" (2026/858/861), targeting the intermediate zone between Johnson and
  capacity (the Proximity Prize zone — untouched by both capacity
  counterexamples). If the mechanized *statement* says what the paper claims
  (vacuity audit: premise inhabitation, deployed-regime scope, no smuggled
  hypotheses), this would be a machine-checked third rung on our parameter
  ladder — worth one focused audit session precisely because "0 sorries" is
  where our discipline says the reading *starts*, not ends.
