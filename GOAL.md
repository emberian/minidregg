# GOAL — flesh out LOOM (the owned proof system) toward a defensible whole

**Priority (ember, 2026-08-07 eve): LOOM IS VITAL, above kernel work.** Keep **2–6 lanes
active on Loom at all times**, driving it toward maturity — enough that we understand the
whole system (its resources, its soundness floor, why it beats plonky3) well enough to
defend "we built our own proof system" to skeptical peers. Breadth AND depth, continuously.

**All subagents run `model:"fable"`.** Lanes are bounded to mathlib + local Loom/Assurance
files (NEVER large breadstuffs reads — that stalls the stream); construction facts go
INLINE in prompts from the deep-read reports.

## The Loom map (what a defensible whole needs)
- **Front:** sumcheck ✓ (round + adaptive union bound, PROVED).
- **Code layer:** Reed-Solomon ✓ (Cor 4.11 UD); MCA-at-UD ✓. NEXT: constrained RS code
  (CRS[F,L,m,ŵ,σ]) — the claim object; γ-power constraint batching (WHIR Constr 5.5).
- **Accumulator (THE HEART, nothing yet):** the WARP claim (rt,α,μ,β,η); the γ-fold
  (CRS×CRS→CRS closure); straightline erasure-extraction; unbounded-depth composition.
- **Depth:** OB-2 tower ✓ modulo OB-2a (game-slot bound — close it).
- **Transcript:** RBR vocabulary ✓ (Rbr.lean). NEXT: BCS/Fiat-Shamir (RBR→straightline NI).
- **ZK (contribution slot):** OB-4 — hiding for hash-based straightline accumulation.
- **Bridge:** OB-3 ✓ (receipt Q native to the accumulator, binding half; [OB3-d-fold]
  closes once the accumulator lands).

## Standing lanes (keep 2–6 live; relaunch as they land)
Weaving: ACC-sound (proximity), SumcheckReduction (front→code), OB-4 (ZK slot).

## Done-log (recent)
- 2026-08-07 eve ★★★ **v0 APEX — the light-client theorem, PROVED + audited** ★★★ (Loom/LightClient e7db26d). lightClient_attests: verifying the aggregate at every challenge schedule + SeamOk ⇒ every link of the history is attested. Anti-tamper: not_seamOk_of_broken (one broken seam refutes the whole chain); order-tooth (a reordered chain, List.Perm witness, fails — the seam pins ORDER not content). REFUTED (OB-2 discipline on itself): oneShot_lightClient_false — the naive single-schedule form is machine-checked FALSE (phantom_forged/phantom_caught: two unsat claims γ-cancel at a rigged schedule, the ∀-schedule quantifier proven load-bearing). ALL ATLAS triple.
  → **The derandomized v0 slice is GREEN + AUDITED**: kernel turn → receipt Q (OB-3) → accumulator fold → light-client attestation, soundness = depth composition (OB-2 PROVED). Remaining for the probabilistic upgrade: [ACC-sound] (proximity, weaving) + [LC-sound] (∀-schedule → one FS schedule, rides ACC-sound + Depth's Thm B.4).
- 2026-08-07 eve **OB-3 kill-checkpoint COMPLETE (binding + fold)** (audited): [OB3-d-fold] CLOSED — receiptClaim_folds proves two receipt claims fold via Loom's foldClaims to ONE accumulated claim (proof term IS foldClaims_satisfies fed the bridge — inheritance visible). The receipt Q is a native AccClaim; the chain is one accumulated object. Teeth: a ghost fold caught at every γ≠0. ATLAS triple. Only [OB3-c-prox] (rate<1) + [ACC-sound] proximity remain.
- 2026-08-07 eve ★★ **OB-2 COMPLETE — the whole-stack depth composition theorem, RIGOROUSLY AUDITED** ★★. [OB-2a] CLOSED (gameSlotBound_proved: GameSlotBound, fully proved not reduced — the lazy-rnd resolver runFrom/resolveIn + the exactly-uniform kernel card_resolve_runFrom + pushforward slicing). OB2_depth_composition_nonneg_proved inhabits the REAL obligation; the anti-weakening check passes (OB2_depth_composition_false still compiles beside it — the repair is honest, not a relabeled weakening). ATLAS triple. This is the theorem whose absence was breadstuffs' laundered EngineSound carrier. Downstream: FiatShamir's fsKeystone_proved now UNCONDITIONAL (straightline FS-of-RBR at loss-free (t+k)·ε_rbr). FiatShamir + OutOfDomain audited; batch pushed. Tree green 2052.
- 2026-08-07 eve **OutOfDomain ✓** (audited, ATLAS triple): WHIR OOD sampling — the uniqueness pin (card_oodAgree < d), the list-separation union bound CLOSED (no residual), ∃! pin, + bonus bridge (oodConstraint = a LinearConstraint → mem_constrainedRS_ood_iff, discharging ConstrainedCode's promise). Teeth attain d-1 at F5.
- 2026-08-07 eve **FiatShamir** committed (98eea64, self-reported clean, hand-audit pending): the transcript layer. Design finding — Rbr's SR game IS the lazy-sampled ROM game (queries=salted prefixes=SrMoves), so 3 machine-checked pieces not a stub: ROM as an INHABITED handler (Oracle.empty, no axiom), fsStraightline_iff_sr (BCS bridge), FsOfRbrSound ↔ OB2-depth. Its [OB-2a] residual is INHERITED from Depth — the sibling OB-2a lane builds the exact resolver that discharges it.
- 2026-08-07 eve **Accumulator — THE HEART** (audited): WARP AccClaim (rt,α,μ,β,η) + foldClaims; closure foldClaims_satisfies (CRS×CRS→CRS) [propext,Quot.sound]; a machine-checked bridge to ConstrainedCode (ofConstraints_satisfies_iff); teeth attain (t-1)ℓ/|F| (bad-set card=1 at F5). The chain is one accumulated object.
- 2026-08-07 eve **ConstrainedCode** (audited): WHIR Def 4.5 constrained RS code + gamma-power batching (forward proved + exact-word t-1 bound, tightness attained at F5); constrainedRS_append = the accumulator's merge closure.
- 2026-08-07 eve **OB-3 kill-checkpoint PASSES** (Assurance/ReceiptClaim, audited): Q's
  word = flatten(post); flatten_faithful binds it over the deployed finite field
  (range-restricted cast, non-vacuous); anti-ghost tooth computes over ZMod 5. No failure
  site bit. Receipt IS the accumulator's word.
- 2026-08-07 eve Sumcheck ✓ (adaptive union bound discharged), N2a ✓ (hyperedge=limit),
  Receipt ✓, kernel spine complete (Camera/State/Turn/TurnLimit/Receipt green).
- Earlier: OB-6 (MCA@UD +typo), Camera, N3 (fold_unique), Reed-Solomon, OB-2 (refuted+
  repaired mod OB-2a), Pred. Tree green 2045 jobs.
