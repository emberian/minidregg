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
Current wave: Accumulator, ConstrainedCode, OB-2a, FiatShamir.

## Done-log (recent)
- 2026-08-07 eve **OB-3 kill-checkpoint PASSES** (Assurance/ReceiptClaim, audited): Q's
  word = flatten(post); flatten_faithful binds it over the deployed finite field
  (range-restricted cast, non-vacuous); anti-ghost tooth computes over ZMod 5. No failure
  site bit. Receipt IS the accumulator's word.
- 2026-08-07 eve Sumcheck ✓ (adaptive union bound discharged), N2a ✓ (hyperedge=limit),
  Receipt ✓, kernel spine complete (Camera/State/Turn/TurnLimit/Receipt green).
- Earlier: OB-6 (MCA@UD +typo), Camera, N3 (fold_unique), Reed-Solomon, OB-2 (refuted+
  repaired mod OB-2a), Pred. Tree green 2045 jobs.
