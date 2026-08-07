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
- **Multilinear PCS, staged:** **Basefold (RS instantiation) at unique-decoding
  parameters first** — the only candidate where *every lemma machine-checked, floor =
  ROM + explicit CR only* is a near-term reality (~10–30K Lean lines beyond infra;
  elementary correlated agreement; ~2–3× queries as the price) — **then WHIR at the
  Johnson bound** as the mechanization of Johnson-regime correlated agreement matures
  (same sumcheck skeleton; 63 KiB / 360 μs verify @2^22 — the cheapest recursion step
  in the family; the entire Lean ecosystem is converging on it).
- **Aggregation (the product):** recursion via in-circuit verification of the WHIR/
  Basefold verifier as the deployed pattern now, with the aggregate format kept
  **abstract** so a straightline-extractable hash-based accumulator (**Arc**
  2024/1731 / **WARP** 2025/753) slots in once audited — because straightline ROM
  extraction makes **unbounded-depth PCD a theorem**, which no rewinding-based
  scheme honestly offers at our use case.
- **Transcript layer:** Poseidon2-class sponge as the ROM; Fiat–Shamir/BCS done
  **once over the whole compiled protocol** with round-by-round soundness as the
  non-negotiable invariant (2025/118's practical FS attacks are on protocols that
  skipped exactly this).
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
its finished results are small, parameterized, and honest:

| artifact | status (cloned/counted 2026-08-07) | role for us |
|---|---|---|
| **ArkLib** (Verified-zkEVM, Lean 4) | 100,119 LOC, **293 sorries**; IOR architecture (RBR security, lenses, BCS, duplex-sponge FS) defined; headline theorems open (composition 19 sorries, BCS a stub) | **Adopt the architecture**, not the theorems; consider a specialized composition spine for our one stack; track daily |
| **VCV-io** (Lean 4) | 146,057 LOC, 82 sorries; oracle computations as free monad; ROM as *inhabited lazy-sampling handler*; forking lemma without rewindability axioms; FS for sigma protocols | **Vendor.** The ROM/game-hopping carrier; irreplaceable |
| **simple-rbr-fri** (zksecurity, Hirai) | **4,068 LOC, 0 sorries, 0 axioms**; full FRI RBR soundness + completeness, MCA as named pluggable hypothesis; built solo in ~6 weeks | **Port outright.** The completion-discipline template — `FRI_MCA_Hypothesis` is exactly ATLAS's carrier-with-realizer-slot pattern |
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
2. **ROM realization** — the oracle is an *inhabited handler* (VCV-io lazy
   sampling); the sole permanently-unproven leap is "the deployed Poseidon2 sponge
   realizes it," stated as the named idealization it is. Where Merkle binding can
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

## 7. Open questions for ember

1. **Field**: BabyBear (breadstuffs continuity, Plonky3 ecosystem) vs KoalaBear
   (SP1-Hypercube momentum) vs Goldilocks (Neo-compat) — with the Arc/WARP
   field-size inequality satisfied by extension choice either way.
2. **ArkLib posture**: silent consumers, or upstream contributors (their BCS/
   composition holes are exactly what we must build anyway — contributing buys
   review; forking buys velocity)?
3. **Accumulation phase-in**: how long do we run recursive-verification-only before
   trusting Arc/WARP-shape accumulation (audits? our own mechanization of WARP's
   straightline extractor)?
4. **Poseidon2 vs a SHA3-class sponge** for the ROM instantiation leap (circuit
   cost vs cryptanalytic maturity).
