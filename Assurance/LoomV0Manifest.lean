/-
# `Assurance/LoomV0Manifest.lean` — the machine-checked table of contents.

**Not new math.** Every declaration below is a `theorem manifest_<name> :
<exact type> := <landed theorem>` — a verbatim RE-EXPORT of a theorem that
already lives in `Loom/` or `Assurance/`. The type is copied from the real
declaration (verified against the compiler's own elaborated signature, not
retyped from memory) and the body cites the original by name. If a cited
theorem is renamed, deleted, or its type drifts incompatibly, this file
FAILS TO BUILD — that failure IS the point: a bit-rot guard over the whole
proved tower, and a single legible index of what "Loom v0" consists of, for
a peer to read top to bottom.

No `sorry`. No vacuous restatement (`: True := trivial` or the like) — every
entry below is checked against the real theorem's real type. REFUTATIONS
(`oneShot_lightClient_false`, `OB2_depth_composition_false`,
`smallField_bound_vacuous`) are indexed too: the discipline of naming what is
FALSE is as load-bearing as what is proved, and belongs in the same table.

Grouped by layer, in the order `GOAL.md`'s done-log narrates the tower:
Front → Code → Accumulator → Depth/transcript → Light client → Deployed →
Bridge/capstone. Each entry's docstring names the theorem's own residual (if
any is still open at THAT theorem's resolution) — a residual named at one
layer is very often closed at a layer above it; the full ledger is §8.
-/
import Assurance.LoomV0
import Assurance.ReceiptClaim
import Loom.SumcheckReduction
import Loom.SmallField
import Loom.OutOfDomain
import Loom.AccSoundRbr
import Loom.LightClientFS
import Loom.DeciderProximity
import Loom.Erasure

namespace Minidregg.Assurance

open Minidregg.Loom Minidregg.Kernel

/-! ## §1. Front — sumcheck retires the constraint channel -/

/-- **`sumcheck_soundness`** (`Loom/Sumcheck.lean`). The v-round sumcheck: a
false claim survives a uniformly sampled challenge vector with probability
at most `v·d/|F|`. Fully proved; no residual at this layer. -/
theorem manifest_sumcheck_soundness {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {v d : ℕ} {prover honest : ℕ → Polynomial F} {H S : F}
    (hProverDeg : ∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ (r : Fin v → F), ∀ i, i < v →
      (honest i).eval 0 + (honest i).eval 1 = scChain S honest (chalOf r) i) :
    uniformProb (Fin v → F) (AcceptsFalse prover honest H S)
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) :=
  sumcheck_soundness hProverDeg hHonestDeg hHonest

/-- **`adaptiveUnionBound_holds`** (`Loom/Sumcheck.lean`, OB-SC). The
fully-adaptive per-round union bound is DISCHARGED, not merely stated:
prefix-measurable per-round bad sets of size `≤ d` still union-bound to
`v·d/|F|`. No residual. -/
theorem manifest_adaptiveUnionBound_holds {F : Type} [Field F] [Fintype F]
    {v d : ℕ} : AdaptiveUnionBound F v d :=
  adaptiveUnionBound_holds

/-- **`sumcheck_retires_batch`** (`Loom/SumcheckReduction.lean`). The batched
γ-constraint list retires into ONE sumcheck claim, at the same `v·d/|F|`
price — the front absorbs the whole constraint channel. No residual. -/
theorem manifest_sumcheck_retires_batch {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {v d : ℕ} {prover honest : ℕ → Polynomial F}
    {f : ι → F} {cs : List (LinearConstraint ι F)} {γ : F}
    (hγ : ¬ Satisfies f (batchConstraint γ cs))
    (hProverDeg : ∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ (r : Fin v → F), ∀ i, i < v →
      (honest i).eval 0 + (honest i).eval 1
        = scChain (trueSum (batchConstraint γ cs) f) honest (chalOf r) i) :
    uniformProb (Fin v → F)
      (SumcheckAccepts prover honest (batchConstraint γ cs).target
        (trueSum (batchConstraint γ cs) f))
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) :=
  sumcheck_retires_batch hγ hProverDeg hHonestDeg hHonest

/-! ## §2. Code layer — Reed–Solomon, correlated agreement, constraints, OOD, LDT -/

/-- **`reedSolomonCode_hasMutualCorrelatedAgreement`** (`Loom/ReedSolomon.lean`,
WHIR Cor. 4.11, unique-decoding shape) — "the UD proximity". A proximity
generator for RS upgrades to MUTUAL correlated agreement at unique decoding.
Residual: `hPG : IsProximityGenerator` is carried as an explicit HYPOTHESIS
(WHIR Thm 4.8 / BCIKS 2020/654), never assumed as an instance or axiom. -/
theorem manifest_reedSolomonCode_hasMutualCorrelatedAgreement
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [DecidableEq F]
    {ℓ : ℕ} [Nonempty ι]
    (G : ProximityGenerator F ℓ) (dom : ι ↪ F) (d : ℕ) {B : ℝ} {err : ℝ → ℝ}
    (hPG : IsProximityGenerator G (reedSolomonCode dom d) B err)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ → δ₂ < 1 - B → err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ → δ < 1 - B → 0 ≤ err δ) :
    HasMutualCorrelatedAgreement G (reedSolomonCode dom d)
      (max (1 - (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2) B) err :=
  reedSolomonCode_hasMutualCorrelatedAgreement G dom d hPG herr_mono herr_nonneg

/-- **`hasMutualCorrelatedAgreement_of_isProximityGenerator`**
(`Loom/CorrelatedAgreement.lean`, [OB-6], WHIR Lemma 4.10) — "MCA-at-UD".
The generic mutual-correlated-agreement theorem at unique decoding: PROVED
unconditionally (the realization, not just the interface). No residual. -/
theorem manifest_hasMutualCorrelatedAgreement_of_isProximityGenerator
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [DecidableEq F]
    {ℓ : ℕ} [Nonempty ι]
    (G : ProximityGenerator F ℓ) (C : Submodule F (ι → F)) {B : ℝ}
    {err : ℝ → ℝ} {dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hPG : IsProximityGenerator G C B err)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ → δ₂ < 1 - B → err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ → δ < 1 - B → 0 ≤ err δ) :
    HasMutualCorrelatedAgreement G C (max (1 - dC / 2) B) err :=
  hasMutualCorrelatedAgreement_of_isProximityGenerator G C hdC hPG herr_mono herr_nonneg

/-- **`mem_constrainedRS_iff`** (`Loom/ConstrainedCode.lean`, WHIR Def 4.5).
`CRS[F,dom,d,cs]` membership is exactly RS-membership plus every listed
constraint. Definitional; no residual. -/
theorem manifest_mem_constrainedRS_iff {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    {dom : ι ↪ F} {d : ℕ} {cs : List (LinearConstraint ι F)} {f : ι → F} :
    f ∈ constrainedRS dom d cs ↔
      f ∈ reedSolomonCode dom d ∧ ∀ c ∈ cs, Satisfies f c :=
  mem_constrainedRS_iff

/-- **`card_batch_satisfying_le`** (`Loom/ConstrainedCode.lean`, WHIR Constr.
5.5, γ-power batching, exact-word kernel). A word violating some listed
constraint satisfies the γ-batch on at most `t−1` of `|F|` challenges.
Residual: the δ-proximity lift `[CRS-batch-sound]` (closed at the claim
level by `foldClaims_sound_proximity_UD` below). -/
theorem manifest_card_batch_satisfying_le {ι : Type*} [Fintype ι]
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {f : ι → F} {cs : List (LinearConstraint ι F)} (h : ∃ c ∈ cs, ¬ Satisfies f c) :
    (Finset.univ.filter fun γ : F =>
        Satisfies f (batchConstraint γ cs)).card ≤ cs.length - 1 :=
  card_batch_satisfying_le h

/-- **`existsUnique_of_good`** (`Loom/OutOfDomain.lean`) — "the uniqueness
pin". At a separating OOD point, a claimed OOD value is realized by exactly
ONE codeword of the list. `[OOD-pin]` CLOSED — no residual. -/
theorem manifest_existsUnique_of_good {ι : Type*} [Fintype ι]
    {F : Type*} [Field F] [DecidableEq F]
    (dom : ι ↪ F) {d ℓ : ℕ} {ws : Fin ℓ → ι → F} {z : F}
    (hgood : ¬ ∃ i j : Fin ℓ, i < j ∧ ws i ≠ ws j ∧
      oodEval dom d (ws i) z = oodEval dom d (ws j) z)
    {σ : F} (hex : ∃ i, oodEval dom d (ws i) z = σ) :
    ∃! w : ι → F, (∃ i, ws i = w) ∧ oodEval dom d w z = σ :=
  existsUnique_of_good dom hgood hex

/-- **`proximity_sound`** (`Loom/Proximity.lean`, the WHIR/FRI LDT). A δ-far
word passes the iterated fold-test on at most `m·b·|F|^(m−1)` of `|F|^m`
challenge tuples. Residual: `[PROX-fold-distance]` (`hfold`) — closed
unconditionally below quantization by the next entry, reduced to the
standing `hPG` macroscopically. -/
theorem manifest_proximity_sound {F : Type*} [Field F] {ι : ℕ → Type*}
    [∀ n, Fintype (ι n)] {m : ℕ} [Fintype F] [DecidableEq F]
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    {f : ι 0 → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (acceptSet T deg f).card ≤ m * (b * Fintype.card F ^ (m - 1)) :=
  proximity_sound T deg hδ hfold hfar

/-- **`foldDistancePreserving_of_lt_inv_card`** (`Loom/Proximity.lean`) — the
UNCONDITIONAL realizer of `[PROX-fold-distance]` below the quantization
radius (`b = 1`, zero hypotheses beyond `δ < 1/|κ|`). Closes the sub-
quantization regime of `[PROX-fold-distance]`; the macroscopic regime stays
open (rides `hPG`, see `proximity_sound`'s citation elsewhere). -/
theorem manifest_foldDistancePreserving_of_lt_inv_card
    {F : Type*} [Field F] {ι κ : Type*} {dom : ι ↪ F} {domSq : κ ↪ F}
    [DecidableEq F] [Fintype ι] [Fintype κ] [Nonempty κ]
    (D : FoldingData F dom domSq) (d : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδκ : δ < 1 / (Fintype.card κ : ℝ)) :
    FoldDistancePreserving D (2 * d) d δ 1 :=
  foldDistancePreserving_of_lt_inv_card D d hδ0 hδκ

/-! ## §3. Accumulator — the WARP γ-fold, THE HEART -/

/-- **`foldClaims_satisfies`** (`Loom/Accumulator.lean`) — the closure
theorem: `CRS-claim × CRS-claim → CRS-claim` under the γ-fold, satisfied by
`f + γ•g`. This is what makes a receipt chain ONE accumulated object.
No residual (pure algebra). -/
theorem manifest_foldClaims_satisfies {Root : Type*} {F : Type*} [Field F]
    {ι : Type*} {r : ℕ}
    {C : Submodule F (ι → F)}
    (foldRoot : Root → F → Root → Root)
    {A B : AccClaim Root F ι r} {f g : ι → F} (γ : F)
    (hshare : ∀ i, B.weights i = A.weights i)
    (hA : AccClaim.Satisfies C A f) (hB : AccClaim.Satisfies C B g) :
    AccClaim.Satisfies C (foldClaims foldRoot A B γ) (f + γ • g) :=
  foldClaims_satisfies foldRoot γ hshare hA hB

/-- **`accSound_batch_exact`** (`Loom/AccSound.lean`, [ACC-sound], exact-word,
claim level). A word violating a listed constraint satisfies the γ-batch
with probability `≤ (t−1)/|F|`. Exact-word only; the δ-proximity form is
`foldClaims_sound_proximity_UD` below. -/
theorem manifest_accSound_batch_exact {ι : Type*} [Fintype ι]
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    {fw : ι → F} {cs : List (LinearConstraint ι F)}
    (h : ∃ c ∈ cs, ¬ Satisfies fw c) :
    uniformProb F (fun γ => Satisfies fw (batchConstraint γ cs))
      ≤ ((cs.length : ℝ) - 1) / (Fintype.card F : ℝ) :=
  accSound_batch_exact h

/-- **`foldClaims_sound_proximity_UD`** (`Loom/AccSound.lean`) — **THE
[ACC-sound] HEADLINE**: at unique decoding, the folded word is δ-close to a
codeword satisfying the folded claim with probability at most
`err⋆(δ) + 1/|F|`. Mutual correlated agreement genuinely consumed. Closed
at UD; the downstream residual is binding this ALGEBRA to the prover's
COMMITMENT — `[ACC-extract-bind]`, closed by `committed_extract_bind` +
`committed_word_recovered` below. -/
theorem manifest_foldClaims_sound_proximity_UD
    {Root : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F] {r : ℕ} [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)} (foldRoot : Root → F → Root → Root)
    {A B : AccClaim Root F ι r} {f g : ι → F} {δ dC Bstar : ℝ}
    {errstar : ℝ → ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (hfar : ∀ u ∈ C, ∀ v ∈ C, relDist f u ≤ δ → relDist g v ≤ δ →
      ∃ i, ¬(A.weights i u = A.targets i ∧ A.weights i v = B.targets i)) :
    uniformProb F (fun γ => ∃ w, relDist (f + γ • g) w ≤ δ ∧
        AccClaim.Satisfies C (foldClaims foldRoot A B γ) w)
      ≤ errstar δ + 1 / (Fintype.card F : ℝ) :=
  foldClaims_sound_proximity_UD foldRoot hdC hMCA hδ0 hδB hδC hfar

/-- **`extractPair_sound`** (`Loom/AccExtract.lean`) — the two-point
straightline extractor: folds of ONE pair at two distinct challenges
determine the pair exactly. Pure field algebra; no residual. -/
theorem manifest_extractPair_sound {F : Type*} [Field F] {ι : Type*}
    {h h' f g : ι → F} {γ γ' : F} (hne : γ ≠ γ')
    (hh : h = f + γ • g) (hh' : h' = f + γ' • g) :
    extractPair h h' γ γ' = (f, g) :=
  extractPair_sound hne hh hh'

/-- **`accKnowledgeSound`** (`Loom/AccExtract.lean`, [ACC-extract] step
level). A prover verifying the fold at two distinct challenges yields
genuine witnesses of the INDIVIDUAL claims. Residual: binding the extracted
witnesses to the prover's COMMITMENT is `[ACC-extract-bind]` (closed below);
depth is `[ACC-extract-chain]` (closed next). -/
theorem manifest_accKnowledgeSound {Root : Type*} {F : Type*} [Field F]
    {ι : Type*} {r : ℕ}
    (foldRoot : Root → F → Root → Root)
    {C : Submodule F (ι → F)} {A B : AccClaim Root F ι r}
    {h h' : ι → F} {γ γ' : F} (hne : γ ≠ γ')
    (hshare : ∀ i, B.weights i = A.weights i)
    (hfold : AccClaim.Satisfies C (foldClaims foldRoot A B γ) h)
    (hfold' : AccClaim.Satisfies C (foldClaims foldRoot A B γ') h') :
    AccClaim.Satisfies C A (extractPair h h' γ γ').1 ∧
    AccClaim.Satisfies C B (extractPair h h' γ γ').2 ∧
    h = (extractPair h h' γ γ').1 + γ • (extractPair h h' γ γ').2 ∧
    h' = (extractPair h h' γ γ').1 + γ' • (extractPair h h' γ γ').2 :=
  accKnowledgeSound foldRoot hne hshare hfold hfold'

/-- **`extractChain_sound`** (`Loom/AccExtractChain.lean`, [ACC-extract-chain],
CLOSED at arbitrary depth). A prover verifying the aggregate at the base
schedule and every link-perturbed schedule yields a witness list
genuinely satisfying the WHOLE chain — no induction over depth needed. -/
theorem manifest_extractChain_sound {Root : Type*} {F : Type} [Field F]
    {ι : Type*} {r : ℕ}
    (foldRoot : Root → F → Root → Root)
    {C : Submodule F (ι → F)} {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) {γs γalt : ℕ → F}
    (hne : ∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ))
    {h₀ : ι → F} {hs : Fin ch.length → ι → F}
    (hbase : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) h₀)
    (hpert : ∀ k : Fin ch.length, AccClaim.Satisfies C
      (aggregate foldRoot (updSched γs γalt k) A₀ ch) (hs k)) :
    List.Forall₂ (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w)
      ch (extractChain γs γalt h₀ hs) :=
  extractChain_sound foldRoot halign hne hbase hpert

/-- **`lightClientKnowledgeSound`** (`Loom/AccExtractChain.lean`) — the
knowledge-sound light client: a seam-ok aligned chain the prover verifies
at the flat `n+1`-transcript family ATTESTS, with witnesses BUILT (not
merely asserted to exist). Residual: `[ACC-extract-bind]` (commitment
binding, closed below). -/
theorem manifest_lightClientKnowledgeSound {Root : Type*} {F : Type} [Field F]
    {ι : Type*} {r : ℕ}
    (foldRoot : Root → F → Root → Root)
    {C : Submodule F (ι → F)} {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) (hseam : SeamOk ch) {γs γalt : ℕ → F}
    (hne : ∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ))
    {h₀ : ι → F} {hs : Fin ch.length → ι → F}
    (hbase : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) h₀)
    (hpert : ∀ k : Fin ch.length, AccClaim.Satisfies C
      (aggregate foldRoot (updSched γs γalt k) A₀ ch) (hs k)) :
    attests C ch ∧
    List.Forall₂ (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w)
      ch (extractChain γs γalt h₀ hs) :=
  lightClientKnowledgeSound foldRoot halign hseam hne hbase hpert

/-- **`accSound_rbr`** (`Loom/AccSoundRbr.lean`, [ACC-sound-rbr]). The
γ-fold's soundness bound, in Rbr's round-error vocabulary — literally
`foldClaims_sound_proximity_UD` renamed, matching the shape
`RbrKnowledgeSoundness.extract_sound` demands. Residual:
`[ACC-sound-rbr-game]` — the shape match does not yet extend to a BUILT
`RbrKnowledgeSoundness` instance (single-round backward extraction alone
does not close; the realizer is `AccExtract`'s two-point extractor at
chain level, already indexed above). -/
theorem manifest_accSound_rbr {Root : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F] {r : ℕ} [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)} (foldRoot : Root → F → Root → Root)
    {A B : AccClaim Root F ι r} {f g : ι → F} {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (hfar : ∀ u ∈ C, ∀ v ∈ C, relDist f u ≤ δ → relDist g v ≤ δ →
      ∃ i, ¬(A.weights i u = A.targets i ∧ A.weights i v = B.targets i)) :
    uniformProb F (fun γ => ∃ w, relDist (f + γ • g) w ≤ δ ∧
        AccClaim.Satisfies C (foldClaims foldRoot A B γ) w)
      ≤ accRbrError F errstar δ :=
  accSound_rbr foldRoot hdC hMCA hδ0 hδB hδC hfar

/-! ## §4. Depth / transcript — OB-2 composition and Fiat–Shamir -/

/-- **`OB2_depth_composition_nonneg_proved`** (`Loom/Depth.lean`, [OB-2′]).
The REPAIRED loss-free depth-composition theorem (WARP 2025/753, Thm B.4),
fully discharged from `[OB-2a]`. No residual. -/
theorem manifest_OB2_depth_composition_nonneg_proved :
    OB2_depth_composition_nonneg :=
  OB2_depth_composition_nonneg_proved

/-- **`gameSlotBound_proved`** (`Loom/Depth.lean`, [OB-2a], CLOSED). The
game-slot bound: the lazy-`rnd` resolver's exactly-uniform kernel, fully
proved (not reduced to a further hypothesis). No residual — this closes
the last gap `OB2_depth_composition_nonneg_proved` depends on. -/
theorem manifest_gameSlotBound_proved : GameSlotBound :=
  gameSlotBound_proved

/-- **`OB2_depth_composition_false`** (`Loom/Depth.lean`) — **REFUTATION**:
the AUDITED, naively-stated `[OB-2]` depth-composition claim is
machine-checked FALSE (`Z = ∅`, `εrbr = -1`, `t = 0` — the sign of the
claimed bound breaks). The repaired obligation is
`OB2_depth_composition_nonneg`, proved above. Indexed here so the honesty
of "we refuted our own naive statement before repairing it" is legible,
not just claimed in prose. -/
theorem manifest_OB2_depth_composition_false : ¬ OB2_depth_composition :=
  OB2_depth_composition_false

/-- **`fsKeystone_proved`** (`Loom/FiatShamir.lean`). The FS-of-RBR
knowledge-soundness-preservation keystone, UNCONDITIONAL — rides
`gameSlotBound_proved`, nothing further assumed. Residual (deployment, not
this theorem's own gap): `[FS-ROM]` (uniform→hash-derived schedule
transport, closed at the fixed-chain level by `lightClientFS_sound` below)
and `[LC-fs-adaptive]` (grinding-adversary pricing). -/
theorem manifest_fsKeystone_proved : FsOfRbrKeystone :=
  fsKeystone_proved

/-! ## §5. Light client — the apex, its soundness, its non-interactive form -/

/-- **`lightClient_attests`** (`Loom/LightClient.lean`) — **THE v0 APEX**
(derandomized form): a chain verified at EVERY challenge schedule, plus a
decidable seam, attests the whole history. Deterministic; superseded
probabilistically by `lightClientSound` below (one draw, not every
schedule). -/
theorem manifest_lightClient_attests {Root : Type*} {F : Type*} [Field F]
    {ι : Type*} {r : ℕ}
    (foldRoot : Root → F → Root → Root)
    {C : Submodule F (ι → F)} {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch) (hA₀ : Verifies C A₀) (hseam : SeamOk ch)
    (hver : ∀ γs : ℕ → F, Verifies C (aggregate foldRoot γs A₀ ch)) :
    attests C ch :=
  lightClient_attests foldRoot halign hA₀ hseam hver

/-- **`oneShot_lightClient_false`** (`Loom/LightClient.lean`,
`LCExample`) — **REFUTATION**: verifying the aggregate at a SINGLE FIXED
schedule, even with a seam-ok chain and honest genesis, does NOT attest the
history (`phantomChain` forges it). This is why the one-shot form must be
probabilistic — `lightClientSound` below — never an algebraic theorem. -/
theorem manifest_oneShot_lightClient_false :
    ¬ (∀ (A₀ : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1)
        (ch : Chain (ZMod 5) (ZMod 5) (Fin 4) 1),
        Aligned A₀ ch →
          Verifies (reedSolomonCode Minidregg.Loom.RSExample.dom₅ 2) A₀ →
          SeamOk ch →
          Verifies (reedSolomonCode Minidregg.Loom.RSExample.dom₅ 2)
            (aggregate Minidregg.Loom.LCExample.linRoot (fun _ => 1) A₀ ch) →
          attests (reedSolomonCode Minidregg.Loom.RSExample.dom₅ 2) ch) :=
  Minidregg.Loom.LCExample.oneShot_lightClient_false

/-- **`lightClientSound`** (`Loom/LightClientSound.lean`) — **[LC-sound],
THE DEPLOYABLE HEADLINE**: a chain carrying a δ-far-false link survives
verification at ONE uniformly sampled schedule with probability at most
`n·(err⋆(δ) + 1/|F|)`. Residual: binding the honest fold's anchor words to
the prover's COMMITMENT is `[ACC-extract-bind]` (closed below); the
uniform→hash-derived schedule transport is `[FS-ROM]`/`[LC-sound-fs]`
(closed at the fixed-chain level by `lightClientFS_sound`). -/
theorem manifest_lightClientSound
    {Root : Type*} {ι : Type*} {F : Type} [Field F] {r : ℕ}
    [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (foldRoot : Root → F → Root → Root) [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r} {ws : List (ι → F)}
    {f₀ : ι → F} {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ) (hlen : ws.length = ch.length)
    (hfalse : ∃ p ∈ ch.zip ws, ∀ v ∈ C, relDist p.2 v ≤ δ →
        ¬ AccClaim.Satisfies C p.1.claim v) :
    uniformProb (Fin ch.length → F) (fun γv =>
        ∃ w, relDist (foldWords (padSched γv) f₀ ws) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) w)
      ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)) :=
  lightClientSound foldRoot halign hdC hMCA hδ0 hδB hδC herr0 hlen hfalse

/-- **`lightClientSound_exact`** (`Loom/LightClientSound.lean`). Exact-word
specialization: an unsatisfiable link survives one uniform draw with
probability `≤ 1/|F|`, SHARP (`[LC-sound-delta]` came out empty — no
residual). -/
theorem manifest_lightClientSound_exact
    {Root : Type*} {ι : Type*} {F : Type} [Field F] {r : ℕ}
    (foldRoot : Root → F → Root → Root) [Fintype F]
    {C : Submodule F (ι → F)} {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (halign : Aligned A₀ ch)
    (huns : ∃ l ∈ ch, ¬ ∃ f, AccClaim.Satisfies C l.claim f) :
    uniformProb (Fin ch.length → F) (fun γv =>
        Verifies C (aggregate foldRoot (padSched γv) A₀ ch))
      ≤ 1 / (Fintype.card F : ℝ) :=
  lightClientSound_exact foldRoot halign huns

/-- **`lightClientFS_sound`** (`Loom/LightClientFS.lean`) — **[LC-sound-fs],
THE DEPLOYABLE NON-INTERACTIVE HEADLINE**: `lightClientSound`'s bound,
UNCHANGED, with each link's challenge ROM-derived (σ-before-γ) instead of
sampled — the FS derivation is injective and fresh, so the transport is
lossless. Residual: `[LC-fs-adaptive]` (the grinding adversary re-rolling
the transcript hash `t` times; the chain here is fixed before the coins
sample). -/
theorem manifest_lightClientFS_sound
    {Root ι F : Type} [Field F] {r : ℕ} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (foldRoot : Root → F → Root → Root) [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r} {ws : List (ι → F)}
    {f₀ : ι → F} {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ) (hlen : ws.length = ch.length)
    (hfalse : ∃ p ∈ ch.zip ws, ∀ v ∈ C, relDist p.2 v ≤ δ →
        ¬ AccClaim.Satisfies C p.1.claim v)
    (d : Fin ch.length → F) :
    uniformProb (Fin ch.length → F) (fun c =>
        ∃ w, relDist (foldWords
            (padSched (fsSchedule (fsDerive A₀ ch c) A₀ ch d)) f₀ ws) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot
            (padSched (fsSchedule (fsDerive A₀ ch c) A₀ ch d)) A₀ ch) w)
      ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)) :=
  lightClientFS_sound foldRoot halign hdC hMCA hδ0 hδB hδC herr0 hlen hfalse d

/-- **`decider_sound`** (`Loom/Decider.lean`). The final one-time check: the
decider's verdict IS `AccClaim.Satisfies`, definitionally. Both soundness
and completeness in one `Iff.rfl`. No residual. -/
theorem manifest_decider_sound {Root : Type*} {F : Type*} [Field F]
    {ι : Type*} {r : ℕ}
    (C : Submodule F (ι → F)) (A : AccClaim Root F ι r) (f : ι → F) :
    decider C A f ↔ AccClaim.Satisfies C A f :=
  decider_sound C A f

/-- **`decider_depth_independent`** (`Loom/Decider.lean`, LOOM §6's one-time
compression). The decider's check on a depth-`n` fold is the SAME `r`
functionals, evaluated once, independent of chain length — succinctness,
structurally. Residual: `[DEC-succinct]`, an operation-COUNTING cost model
(this theorem is the structural fact the cost model would price, not the
count itself). -/
theorem manifest_decider_depth_independent {Root : Type*} {F : Type*} [Field F]
    {ι : Type*} {r : ℕ}
    (foldRoot : Root → F → Root → Root)
    (C : Submodule F (ι → F)) (A : AccClaim Root F ι r)
    (links : List (AccClaim Root F ι r × F)) (f : ι → F) :
    decider C (foldChain foldRoot A links) f
      ↔ f ∈ C ∧ ∀ i, A.weights i f = (foldChain foldRoot A links).targets i :=
  decider_depth_independent foldRoot C A links f

/-- **`deciderProx_sound`** (`Loom/DeciderProximity.lean`, [DEC-proximity]).
The DEPLOYED (rate < 1) decider rejects δ-far words: acceptance on at most
`m·b·|F|^(m−1)` challenge tuples, riding `proximity_sound` through the
containment `deciderProxAcceptSet ⊆ acceptSet`. Residual: the same
`[PROX-fold-distance]` as `proximity_sound`, plus `[DEC-prox-query]`
(spot-check/repetition accounting). -/
theorem manifest_deciderProx_sound {Root : Type*} {F : Type*} [Field F] {r : ℕ}
    {ι : ℕ → Type*} {m : ℕ} [Fintype F] [∀ n, Fintype (ι n)] [DecidableEq F]
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    (A : AccClaim Root F (ι 0) r) {f : ι 0 → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (deciderProxAcceptSet T deg A f).card ≤ m * (b * Fintype.card F ^ (m - 1)) :=
  deciderProx_sound T deg hδ hfold A hfar

/-! ## §6. Deployed — small fields, the commitment root, erasure, ZK -/

/-- **`sumcheck_lambda_secure`** (`Loom/SmallField.lean`, [OB-8]). The
deployment inequality: `v·d·2^λ ≤ |F|` buys `λ` bits, instantiated from
`sumcheck_soundness` (no re-derivation). Its tooth is
`smallField_bound_vacuous` next — no residual on this direction itself. -/
theorem manifest_sumcheck_lambda_secure {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {v d lam : ℕ} {prover honest : ℕ → Polynomial F} {H S : F}
    (hProverDeg : ∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ (r : Fin v → F), ∀ i, i < v →
      (honest i).eval 0 + (honest i).eval 1 = scChain S honest (chalOf r) i)
    (hbig : v * d * 2 ^ lam ≤ Fintype.card F) :
    uniformProb (Fin v → F) (AcceptsFalse prover honest H S) ≤ 1 / 2 ^ lam :=
  sumcheck_lambda_secure hProverDeg hHonestDeg hHonest hbig

/-- **`smallField_bound_vacuous`** (`Loom/SmallField.lean`, [OB-8]) —
**REFUTATION-SHAPED TOOTH**: at `|F| = 5`, `v·d = 100` the "soundness bound"
`v·d/|F| = 20 ≥ 1` holds for EVERY event — a bound any adversary satisfies
secures nothing. Demonstrates the extension degree is LOAD-BEARING for
`sumcheck_lambda_secure`, not decorative. -/
theorem manifest_smallField_bound_vacuous (E : (Fin 100 → ZMod 5) → Prop) :
    uniformProb (Fin 100 → ZMod 5) E
      ≤ (100 : ℝ) * ((1 : ℝ) / Fintype.card (ZMod 5)) :=
  smallField_bound_vacuous E

/-- **`committed_extract_bind`** (`Loom/Commitment.lean`) — **[ACC-extract-bind]
(a)(c), the binding + attribution seam**: a fully-opened word IS the
committed word, and satisfaction transfers to it. Residual (b): the
`t`-column erasure lift, closed for unique decoding by
`committed_word_recovered` below. -/
theorem manifest_committed_extract_bind {Root : Type*} {F : Type*} {ι : Type*}
    {Op : Type*} [Field F] {r : ℕ}
    (S : BindingCommitment Root F ι Op)
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {w e : ι → F}
    {oe : ι → Op} (hrt : A.rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen A.rt i (e i) (oe i))
    (hsat : AccClaim.Satisfies C A e) :
    e = w ∧ AccClaim.Satisfies C A w :=
  committed_extract_bind S hrt hopen hsat

/-- **`idealCommitment`** (`Loom/Commitment.lean`) — the honest floor's
INHABITATION witness: root = word, verify = symbol equality, binding a
two-line theorem. Re-exported as a `def` (it is the witness OBJECT, not a
`Prop`); confirmed AXIOM-FREE by `#print axioms` below (no `Classical.choice`,
no `propext`, no `Quot.sound` — it doesn't merely avoid `sorry`, it avoids
every logical axiom Lean tracks). Residual: `[COMMIT-CR]`, the deployed
Merkle/sponge realizer, priced only relative to collision-resistance. -/
noncomputable def manifest_idealCommitment (F ι : Type*) :
    BindingCommitment (ι → F) F ι Unit :=
  idealCommitment F ι

/-- **`committed_word_recovered`** (`Loom/Erasure.lean`) — closes
**[ACC-extract-bind](b)** for unique decoding: `t ≥ d` verified openings of
a genuine RS codeword erasure-recover the FULL word, and (composed with
`S.binding`) that word IS the committed one. With `committed_extract_bind`
above, `[ACC-extract-bind]` is CLOSED at the word level. Residual:
`[ERASURE-list]` (beyond unique decoding, list-decoding regime). -/
theorem manifest_committed_word_recovered {ι : Type*} {F : Type*} [Field F]
    {Root : Type*} {Op : Type*}
    (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t) {opened : Fin t → ι}
    (hopen : Function.Injective (dom ∘ opened)) {rt : Root} {w : ι → F}
    (hrt : rt = S.commit w) (hw : w ∈ reedSolomonCode dom d)
    {vals : Fin t → F} {op : Fin t → Op}
    (hverify : ∀ j, S.verifyOpen rt (opened j) (vals j) (op j)) :
    recoverFromColumns dom d opened vals = w :=
  committed_word_recovered S dom hdt hopen hrt hw hverify

/-- **`mask_bijOn`** (`Loom/ZK.lean`, [OB-4-hiding] core). The masking map
`g ↦ f + γ•g` is a bijection from the mask claim's satisfying set ONTO the
folded claim's — perfect hiding of the accumulator's secret witness.
Residual: `[OB-4-hiding-rbr]` (constrained-mask + joint simulation + the
full RBR game — the open research half). -/
theorem manifest_mask_bijOn {Root : Type*} {F : Type*} [Field F] {ι : Type*} {r : ℕ}
    (foldRoot : Root → F → Root → Root)
    {C : Submodule F (ι → F)} {A B : AccClaim Root F ι r}
    {f : ι → F} {γ : F} (hγ : γ ≠ 0)
    (hshare : ∀ i, B.weights i = A.weights i)
    (hf : AccClaim.Satisfies C A f) :
    Set.BijOn (mask f γ) (satWords C B)
      (satWords C (foldClaims foldRoot A B γ)) :=
  mask_bijOn foldRoot hγ hshare hf

/-- **`t_symbols_uniform`** (`Loom/ZKHiding.lean`) — the MDS `t`-wise
independence core: for `t ≤ d`, `t` opened RS symbols are jointly uniform
(full support + equal-weight fibers via codeword translation). The
load-bearing lemma for `[OB-4-hiding]`'s opening-leakage bound; `t ≤ d` is
SHARP (refuted at `t = d+1` elsewhere in the file). No residual on the
independence fact itself. -/
theorem manifest_t_symbols_uniform {F : Type*} [Field F] {ι : Type*} {t d : ℕ}
    (dom : ι ↪ F) (ht : t ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) :
    (∀ v : Fin t → F, (openFiber (reedSolomonCode dom d) q v).Nonempty) ∧
      ∀ v₁ v₂ : Fin t → F, ∃ c ∈ reedSolomonCode dom d,
        Set.BijOn (· + c) (openFiber (reedSolomonCode dom d) q v₁)
          (openFiber (reedSolomonCode dom d) q v₂) :=
  t_symbols_uniform dom ht hq

/-! ## §7. Bridge / capstone — the receipt IS an accumulated claim; the tower composes -/

/-- **`flatten_faithful`** (`Assurance/ReceiptClaim.lean`, OB-3, binding
half). Given range-restricted cast injectivity, the flattened field vector
determines the observed post-state — `û(α)=μ` genuinely binds the kernel
receipt Q. Proved over the DEPLOYED finite field (not char-zero). No
residual at the binding level. -/
theorem manifest_flatten_faithful {F : Type} [Field F] (w : Window) (k k' : KernelState)
    (castInj : ∀ z z' : ℤ, z ∈ obsRange w k → z' ∈ obsRange w k' →
      ((z : F) = (z' : F)) → z = z')
    (h : flatten (F := F) w k = flatten (F := F) w k') :
    uproj w k = uproj w k' :=
  flatten_faithful w k k' castInj h

/-- **`receiptClaim_folds`** (`Assurance/ReceiptClaim.lean`, [OB3-d-fold],
CLOSED at closure level). Two receipt claims over one window fold, via
Loom's `foldClaims`, to ONE accumulated claim satisfied by the folded word
— the receipt chain is one accumulated object. Rides the shared
`[ACC-sound]` bound (`foldClaims_sound_proximity_UD` above) for its
δ-proximity form; no residual at the closure level itself. -/
theorem manifest_receiptClaim_folds {F : Type} [Field F] {Root : Type}
    [DecidableEq F] {w : Window}
    {C : Submodule F (FlatIx w → F)}
    (foldRoot : Root → F → Root → Root)
    (rc₁ rc₂ : ReceiptClaim w F) (rt₁ rt₂ : Root) (γ : F)
    (h₁ : flatten (F := F) w rc₁.post ∈ C)
    (h₂ : flatten (F := F) w rc₂.post ∈ C) :
    AccClaim.Satisfies C
      (foldClaims foldRoot (rc₁.acc rt₁) (rc₂.acc rt₂) γ)
      (flatten (F := F) w rc₁.post + γ • flatten (F := F) w rc₂.post) :=
  receiptClaim_folds foldRoot rc₁ rc₂ rt₁ rt₂ γ h₁ h₂

/-- **`receiptClaim_proximity`** (`Assurance/ReceiptClaim.lean`,
[OB3-c-prox], CLOSED at exact-membership). At rate < 1, a receipt word
δ-far from the code prox-accepts on at most `m·b·|F|^(m−1)` challenge
tuples, riding `proximity_sound`. Regime split exactly as
`[PROX-fold-distance]`: sub-quantization UNCONDITIONAL, macroscopic rides
the standing `hPG`. -/
theorem manifest_receiptClaim_proximity {F : Type} [Field F] [DecidableEq F]
    {Root : Type} {w : Window} {tail : ℕ → Type} {m : ℕ}
    [Fintype F] [∀ n, Fintype (tail n)]
    (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    {f : FlatIx w → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (rc.proxAcceptSet rt T deg f).card ≤ m * (b * Fintype.card F ^ (m - 1)) :=
  receiptClaim_proximity rc rt T deg hδ hfold hfar

/-- **`loomV0_holds`** (`Assurance/LoomV0.lean`) — **THE v0 CAPSTONE**: the
whole tower as ONE theorem. Bundles, at a shared final accumulator,
soundness (`lightClientSound`), knowledge soundness
(`lightClientKnowledgeSound`), binding (`committed_extract_bind`), and
decision (`decider_sound`) — the proof term IS the four citations, no
re-derivation. Honestly scoped (see the residual ledger, §8): the
soundness slice's CLAIMED words and the knowledge/binding/decision
slices' VERIFYING transcript are independent parameters — the landed
theorems do not couple them; that coupling is `[ACC-extract-bind]`/
`[FS-ROM]` at deployment. -/
theorem manifest_loomV0_holds {Root : Type*} {F : Type} [Field F] {ι : Type*}
    {r : ℕ} {Op : Type*} [Fintype F] [Nonempty ι] [Fintype ι] [DecidableEq ι]
    [DecidableEq F]
    {foldRoot : Root → F → Root → Root} {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ} {ws : List (ι → F)} {f₀ : ι → F}
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ) (hlen : ws.length = ch.length)
    (hfalse : ∃ p ∈ ch.zip ws, ∀ v ∈ C, relDist p.2 v ≤ δ →
      ¬ AccClaim.Satisfies C p.1.claim v)
    {γs γalt : ℕ → F} (hseam : SeamOk ch)
    (hne : ∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ))
    {h₀ : ι → F} {hs : Fin ch.length → ι → F}
    (hbase : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) h₀)
    (hpert : ∀ k, AccClaim.Satisfies C
      (aggregate foldRoot (updSched γs γalt k) A₀ ch) (hs k))
    {S : BindingCommitment Root F ι Op} {w e : ι → F} {oe : ι → Op}
    (hrt : (aggregate foldRoot γs A₀ ch).rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen (aggregate foldRoot γs A₀ ch).rt i (e i) (oe i))
    (hsat : AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) e)
    (f : ι → F) :
    LoomV0Guarantee foldRoot C A₀ ch δ errstar ws f₀ γs γalt h₀ hs S w e f :=
  loomV0_holds halign hdC hMCA hδ0 hδB hδC herr0 hlen hfalse hseam hne hbase
    hpert hrt hopen hsat f

/-- **`loomV0_light_client`** (`Assurance/LoomV0.lean`) — the
defensibility ONE-LINER: checking a receipt history's aggregate at ONE
Fiat–Shamir schedule is sound, at price `n·(err⋆(δ)+1/|F|)`. This IS
`lightClientSound`, re-exported at the capstone's name for legibility — a
citation, not new math. -/
theorem manifest_loomV0_light_client {Root : Type*} {F : Type} [Field F]
    {ι : Type*} {r : ℕ} [Fintype F] [Nonempty ι] [Fintype ι] [DecidableEq ι]
    [DecidableEq F]
    {foldRoot : Root → F → Root → Root}
    {C : Submodule F (ι → F)} {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {ws : List (ι → F)} {f₀ : ι → F} {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ) (hlen : ws.length = ch.length)
    (hfalse : ∃ p ∈ ch.zip ws, ∀ v ∈ C, relDist p.2 v ≤ δ →
      ¬ AccClaim.Satisfies C p.1.claim v) :
    uniformProb (Fin ch.length → F) (fun γv =>
        ∃ u, relDist (foldWords (padSched γv) f₀ ws) u ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) u)
      ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)) :=
  loomV0_light_client halign hdC hMCA hδ0 hδB hδC herr0 hlen hfalse

/-! ## §8. The residual ledger — prose, honest, not stubs

Every tag below is a NAMED obligation with a realizer or an explicit open
half — never a `def : Prop := True`. Status as of this manifest (matches
`GOAL.md`'s done-log):

* **`[FS-ROM]`** — the deployed light client derives its schedule by
  Fiat–Shamir from the transcript hash; the ROM idealization transporting
  "uniform schedule" to "hash-derived, at the RBR price" is
  `Loom/FiatShamir.lean`'s compilation. CLOSED at the fixed-chain level by
  `lightClientFS_sound`; `lightClientSound` (composed into the capstone) is
  its pre-transport ancestor, cited at that resolution.
* **`[COMMIT-CR]`** — the deployed Merkle/sponge commitment scheme,
  realizing `BindingCommitment` with a short root, is a theorem only
  relative to collision-resistance of the compression function. The
  capstone's `binding` field fires against `idealCommitment` (axiom-free,
  inhabited); `loomV0_holds` is generic in the scheme `S`, so swapping in
  the deployed one composes for free once this lands.
* **`[ACC-extract-bind]`(b)** — NOW CLOSED: `committed_extract_bind`
  (all-positions resolution) + `committed_word_recovered` (the `t ≥ d`
  column erasure lift, unique decoding) together bind the extraction
  algebra's witnesses to the prover's COMMITMENT, not merely to
  algebraically consistent words. `[ERASURE-list]` (beyond unique
  decoding) is the remaining open half.
* **`[LC-fs-adaptive]`** — the `t`-query grinding strengthening (an
  adaptive prover re-rolling the transcript hash to bias the FS-derived
  schedule) is named in `Loom/LightClientFS.lean`, not closed there;
  `lightClientFS_sound` above is the FIXED-chain (non-adaptive) form.
* **`[OB-4-hiding-rbr]`** — `mask_bijOn`'s perfect-hiding core is proved;
  the constrained-mask + joint-simulation + full RBR hiding GAME is the
  open research half of the ZK contribution slot.
* **`[OB-8-tower]`** — `sumcheck_lambda_secure` prices λ-bit security per
  field/extension-degree dial; the WHOLE-TOWER small-field accounting
  (every layer's constant folded into one deployed-field number) is not
  assembled in one place yet.
* **`[ACC-sound-rbr-game]`** — `accSound_rbr` matches the BOUND shape
  `RbrKnowledgeSoundness.extract_sound` demands; a single-round backward
  extractor does not build a full `RbrKnowledgeSoundness` instance (the
  channel is linear, so the naive extractor has too large a kernel) — the
  chain-level two-point extractor (`AccExtract`/`AccExtractChain`, indexed
  above) is the real realizer, at the CHAIN resolution, not per-round.
* **`[ERASURE-list]`** — `committed_word_recovered` closes the erasure
  lift at UNIQUE DECODING (`t ≥ d` opened columns, MDS interpolation); the
  beyond-UD list-decoding regime is untouched.
* **`[DEC-prox-query]`** — `deciderProx_sound` counts ACCEPTING challenge
  TUPLES; translating that into a spot-check/repetition SCHEDULE (how many
  Merkle queries a deployed verifier actually issues) is not modeled.
* **NO PROVER; performance UNMEASURED.** Every theorem in this manifest is
  a VERIFIER guarantee over words, claims, and transcripts the tree
  already has in hand. There is no prover implementation, no cost/latency
  measurement, and no wall-clock claim anywhere in this file or the tower
  it indexes.

None of these residuals is closed by this file — a manifest re-exports,
it does not discharge. Their status is exactly what the cited theorems'
own docstrings already say; repeating it here keeps the index legible
without re-litigating it. -/

/-! ## §9. Axiom audit — the capstone's ATLAS-triple, machine-checked

No `sorry` anywhere in the cited tower (a `sorryAx` dependency below would
say so, loudly). The three axioms every nontrivial Mathlib-based proof
here inherits are Lean's own logical trio — `propext`, `Classical.choice`,
`Quot.sound` — never anything candidate-specific, never a proof-system
assumption smuggled in as an `axiom` declaration. `idealCommitment` (the
commitment floor's inhabitation witness) needs NONE of them. -/

#print axioms manifest_loomV0_holds
#print axioms manifest_loomV0_light_client
#print axioms manifest_committed_extract_bind
#print axioms manifest_idealCommitment
#print axioms manifest_oneShot_lightClient_false
#print axioms manifest_OB2_depth_composition_false

end Minidregg.Assurance
