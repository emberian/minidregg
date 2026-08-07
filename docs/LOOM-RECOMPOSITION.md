# LOOM — recomposing the frontier into minidregg's own proof system

*Design pass 2026-08-07, following PROOF-SYSTEM-SURVEY.md and its §8 addendum.
Working name **Loom**: it weaves strands (the blocklace's own word) of receipts into
one fabric a light client checks once. Name provisional — ember's call.*

**Stance.** This document recomposes the best published mathematics into a system
none of the papers describe. Every recomposition step below is either (a) a theorem
in a cited paper, (b) a composition we must prove ourselves — marked **[OB-n]** and
entered in the obligation ledger — or (c) a design choice with no mathematical
content. Nothing here inherits authority from resemblance to published work; the
ledger is the deliverable.

## 1. The component shelf, as typed reductions

The frontier, viewed as an algebra of reductions between relations (the IOR lens —
the one thing ArkLib got architecturally right):

| component | reduction | source | extraction discipline |
|---|---|---|---|
| Sumcheck | R_hyperedge-body (CCS-shaped) → R_multilinear-eval | classic; 2025/2041 for prover craft | RBR; straightline via R–T [2024/1724] |
| Foldable-code PCS (Basefold-shape) | R_multilinear-eval → R_proximity(C) | 2023/1705 (+ 2024/1571 Johnson) | RBR; unique-decoding regime = erasure-decodable |
| Constrained-code IOPP (WHIR-shape) | R_constrained-eval → R_proximity(CRS) | 2024/1586 (+ 2025/2051, 2025/2110) | RBR, MCA @ Johnson unconditional |
| Accumulation (Arc/WARP-shape) | R_proximity × Acc → Acc | 2024/1731, 2025/753 | **straightline** via erasure correction; unbounded depth |
| ZK at the aggregate | compliance/accumulation separation + masked sumcheck | 2026/289 | inherits |
| FS/transcript | interactive → non-interactive, whole-protocol | BCS; RBR discipline; 2024/1724; 2025/118 as the cautionary | straightline in ROM (+QROM variant) |

The shelf has one striking property the papers don't exploit *jointly*: **every row
can be made straightline-extractable in one ROM**, and **every row can run over one
code family**. Those two unifications are Loom.

## 2. The recomposition — five moves

### Move 1 — One code, one proximity core, one extraction discipline
Fix a single foldable linear code family C (RS instantiation at v0), used by BOTH
the PCS (Basefold-shape folding) and the accumulator (WARP-shape, which accepts any
linear code). Run v0 entirely in the **unique-decoding regime**, where:
- correlated agreement is elementary (mechanizable in weeks, per the FRI precedent),
- **erasure/unique decoding is well-defined**, so WARP's straightline extractor and
  the PCS's extractor are *the same mathematical object* — one decoder, one lemma
  family, used at two layers. **[OB-1]**: the fold structure of C commutes with the
  accumulator's claim format (Basefold folding produces proximity claims about C at
  successively halved lengths; the accumulator must fold claims at *mixed* lengths
  or we normalize lengths first — the normalization-vs-mixed-folding choice is the
  central technical question of Loom v0).
The Johnson-regime upgrade (2025/2051 + 2025/2110 MCA) later widens parameters
without touching the architecture — the proximity hypothesis is a pluggable carrier
exactly as in the survey §4.

### Move 2 — Uniformly straightline: the whole-stack theorem
Each published piece is straightline *in isolation* (R–T for the sumcheck front;
WARP for accumulation; RBR+BCS for the transcript). **[OB-2]** — Loom's apex:
**whole-stack straightline knowledge soundness** — one theorem stating that the
composed extractor for (sumcheck ∘ fold ∘ accumulate ∘ FS) is straightline in one
ROM with additive error across depth. No paper states this composed theorem; it is
exactly the theorem whose absence created breadstuffs' `EngineSound` carrier. The
composition is *specialized to our one stack* (survey §3's stance), which is why it
is finishable where ArkLib's general Append machinery is not: our composition spine
has exactly four arrows.

### Move 3 — Receipt-native accumulation (the product-shaped novelty)
The papers accumulate proofs *about a general VM*. Loom's accumulated relation is
the kernel's own algebra: per turn (= one hyperedge, HYPEREDGE-DESIGN §4), the
accumulator folds the claim bundle
`⟨body-descriptor satisfied, Q binds post-state, seam: pre-root = prev.post-root⟩`
— i.e. **the light-client object IS the receipt chain**, not a SNARK of an
executor-simulator. Payoffs: (a) the compliance predicate is our fold-algebra IR,
whose interp/compile agreement is by initiality — the circuit the accumulator
carries is *derived*, closing the loop with ATLAS's compiler spine; (b) the
uniform-arity receipt (one Q shape for every ι) means ONE claim format at every
link — no per-shape accumulator variants, which is what kept breadstuffs' prover
partition alive. **[OB-3]**: the seam claim is linear-algebraic over C-encodings
(root equality as an encoded-column claim) — prove the encoding makes the seam a
*native* accumulated claim rather than a side condition.

### Move 4 — The disclosure dial reaches the aggregate
Adopt 2026/289's separation: the compliance predicate stays non-ZK (our receipts
are commitments already — hiding lives in the commitment layer per the kernel's
disclosure ladder), while the accumulator itself can be masked (ZK-sumcheck with
masking vectors) when a federation wants history-pattern privacy. **[OB-4]**: the
masking preserves straightline extraction (2026/289 proves ZK for their scheme;
ours must re-prove it against the WARP-shape extractor). Dial default: off at v0.

### Move 5 — Small fields, explicit inequalities, stateless watch
Witness data over the deployed base field (survey §7: BabyBear/KoalaBear/Goldilocks
open); sumcheck challenges and accumulator sampling over the extension satisfying
Arc's explicit field-size inequality — **a checked constant in the repo, not
prose**. Prover accumulator state is Arc/WARP's known operational cost; holography
accumulation (2026/538) is the watchlist refinement if node state becomes a
burden — its "public evaluation checks accumulate separately" decomposition is
compatible with Move 3's claim bundle. **[OB-5]** (deferred): stateless variant.

## 3. Why this is plausibly frontier, stated carefully

Nobody has the **conjunction**: unbounded-depth aggregation (straightline, proven
depth-independent) × fully mechanized soundness (every arrow Lean-checked, floor =
two inhabited carriers) × PQ-plausible transparency × receipt-native statements
(the aggregate attests a capability kernel's own algebra, not a VM wrapper) ×
deployed-parameter honesty (Johnson/unique-decoding only; both capacity
counterexamples cited on the label). Each conjunct exists somewhere; the
conjunction exists nowhere. Loom's novelty is the composition and its one apex
theorem [OB-2] — which is also precisely the theorem minidregg's assurance case
needs, so no effort is spent on generality we don't ship.

## 4. The obligation ledger (the honest core)

| id | obligation | risk | first move |
|---|---|---|---|
| OB-1 | fold ∘ accumulate compatibility (mixed-length claims vs normalization) | **the** technical risk; could force a length-normalization round | work the math on paper against WARP §constructions + Basefold folding; decide v0 shape |
| OB-2 | whole-stack straightline KS, 4-arrow composition, additive depth error | medium — each arrow published; composition ours | state the theorem in Lean first (statement-first discipline); prove arrows in order sumcheck→fold |
| OB-3 | seam claims native to the code (root equality as encoded claim) | medium-low | prototype the Q/seam encoding against C |
| OB-4 | ZK masking preserves straightline extraction | low (deferrable; dial off at v0) | after OB-2 |
| OB-5 | stateless accumulator variant | watchlist | after deployment cost data |
| OB-6 | unique-decoding correlated agreement, mechanized (v0 floor realizer) | low — elementary; calibrated by simple-rbr-fri | early, it unblocks the carrier's realizer slot |

Statement-first discipline throughout: every OB enters the Lean tree as a
`Prop`-statement with its ATLAS keystone fields (satisfiable/teeth/premise-
inhabitation) *before* proof work starts — so a vacuous formulation dies on day
one, not after a proof exists.

## 5. Next actions

1. Fetch and closely read WARP (2025/753) + Arc (2024/1731) + Basefold (2023/1705)
   full constructions; work OB-1 on paper. (The abstract-level compatibility above
   is design; OB-1 is where it meets the actual protocols.)
2. Scaffold the Lean project with `Theory/` + `Loom/` skeletons; state OB-2 and
   OB-6 as statement-first keystones.
3. Field + sponge decisions (survey §7) become blocking at OB-6's parameter
   instantiation — decide by then.
