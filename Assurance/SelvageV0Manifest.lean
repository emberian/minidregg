/-
# `Assurance/SelvageV0Manifest.lean` — the machine-checked table of contents.

**Not new math.** Every declaration below is a `theorem manifest_<name> :
<exact type> := <landed theorem>` — a verbatim RE-EXPORT of a theorem that
already lives in `Selvage/` or `Assurance/`. The type is copied from the real
declaration (verified against the compiler's own elaborated signature, not
retyped from memory) and the body cites the original by name. If a cited
theorem is renamed, deleted, or its type drifts incompatibly, this file
FAILS TO BUILD — that failure IS the point: a bit-rot guard over the whole
proved tower, and a single legible index of what "Selvage v0" consists of, for
a peer to read top to bottom.

No `sorry`. No vacuous restatement (`: True := trivial` or the like) — every
entry below is checked against the real theorem's real type. REFUTATIONS
(`oneShot_lightClient_false`, `OB2_depth_composition_false`,
`smallField_bound_vacuous`, `not_maskedOpeningHiding_zero`,
`masked_pair_ambiguous`, `create_unbacked_breaks`, `leaky_step_leaks`,
`phantomGrind_beats_fixed_bound`) are indexed too: the discipline of naming
what is FALSE is as load-bearing as what is proved, and belongs in the same
table.

Grouped by layer, in the order `GOAL.md`'s done-log narrates the tower:
Front → Code → Accumulator → Depth/transcript → Light client → Deployed →
Bridge/capstone (§§1–7, the first revision), then the layers that COMPLETED
v0 (`docs/LOOM-COMPLETE.md`): ZK argument of knowledge (§8) →
Arithmetization compiler (§9) → Note-spend gadgets (§10) → Kernel (§11) →
Deployment hardening (§12). Each entry's docstring names the theorem's own
residual (if any is still open at THAT theorem's resolution) — a residual
named at one layer is very often closed at a layer above it; the full
ledger is §13.
-/
import Assurance.SelvageV0
import Assurance.ReceiptClaim
import Selvage.SumcheckReduction
import Selvage.SmallField
import Selvage.OutOfDomain
import Selvage.AccSoundRbr
import Selvage.LightClientFS
import Selvage.DeciderProximity
import Selvage.Erasure
import Selvage.ZKHiding
import Selvage.ConstrainedMask
import Selvage.RbrZeroKnowledge
import Selvage.ZkArgument
import Selvage.ZkTriangular
import Selvage.ZkExtraction
import Selvage.ZkRbrGame
import Selvage.AccRbrInstance
import Selvage.MultilinearExtension
import Selvage.LightClientGrinding
import Compiler.NoteSpend
import Assurance.AirSumcheck
import Assurance.AirSumcheckQuadratic
import Assurance.PrivateReceipt
import Assurance.PrivateTurn
import Kernel.TurnBalancedLimit
import Kernel.Verbs
import Kernel.PrivateTurn

namespace Minidregg.Assurance

open Minidregg.Selvage Minidregg.Kernel

universe u v

/-! ## §1. Front — sumcheck retires the constraint channel -/

/-- **`sumcheck_soundness`** (`Selvage/Sumcheck.lean`). The v-round sumcheck: a
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

/-- **`adaptiveUnionBound_holds`** (`Selvage/Sumcheck.lean`, OB-SC). The
fully-adaptive per-round union bound is DISCHARGED, not merely stated:
prefix-measurable per-round bad sets of size `≤ d` still union-bound to
`v·d/|F|`. No residual. -/
theorem manifest_adaptiveUnionBound_holds {F : Type} [Field F] [Fintype F]
    {v d : ℕ} : AdaptiveUnionBound F v d :=
  adaptiveUnionBound_holds

/-- **`sumcheck_retires_batch`** (`Selvage/SumcheckReduction.lean`). The batched
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

/-- **`reedSolomonCode_hasMutualCorrelatedAgreement`** (`Selvage/ReedSolomon.lean`,
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
(`Selvage/CorrelatedAgreement.lean`, [OB-6], WHIR Lemma 4.10) — "MCA-at-UD".
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

/-- **`mem_constrainedRS_iff`** (`Selvage/ConstrainedCode.lean`, WHIR Def 4.5).
`CRS[F,dom,d,cs]` membership is exactly RS-membership plus every listed
constraint. Definitional; no residual. -/
theorem manifest_mem_constrainedRS_iff {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    {dom : ι ↪ F} {d : ℕ} {cs : List (LinearConstraint ι F)} {f : ι → F} :
    f ∈ constrainedRS dom d cs ↔
      f ∈ reedSolomonCode dom d ∧ ∀ c ∈ cs, Satisfies f c :=
  mem_constrainedRS_iff

/-- **`card_batch_satisfying_le`** (`Selvage/ConstrainedCode.lean`, WHIR Constr.
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

/-- **`existsUnique_of_good`** (`Selvage/OutOfDomain.lean`) — "the uniqueness
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

/-- **`proximity_sound`** (`Selvage/Proximity.lean`, the WHIR/FRI LDT). A δ-far
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

/-- **`foldDistancePreserving_of_lt_inv_card`** (`Selvage/Proximity.lean`) — the
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

/-- **`foldClaims_satisfies`** (`Selvage/Accumulator.lean`) — the closure
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

/-- **`accSound_batch_exact`** (`Selvage/AccSound.lean`, [ACC-sound], exact-word,
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

/-- **`foldClaims_sound_proximity_UD`** (`Selvage/AccSound.lean`) — **THE
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

/-- **`extractPair_sound`** (`Selvage/AccExtract.lean`) — the two-point
straightline extractor: folds of ONE pair at two distinct challenges
determine the pair exactly. Pure field algebra; no residual. -/
theorem manifest_extractPair_sound {F : Type*} [Field F] {ι : Type*}
    {h h' f g : ι → F} {γ γ' : F} (hne : γ ≠ γ')
    (hh : h = f + γ • g) (hh' : h' = f + γ' • g) :
    extractPair h h' γ γ' = (f, g) :=
  extractPair_sound hne hh hh'

/-- **`accKnowledgeSound`** (`Selvage/AccExtract.lean`, [ACC-extract] step
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

/-- **`extractChain_sound`** (`Selvage/AccExtractChain.lean`, [ACC-extract-chain],
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

/-- **`lightClientKnowledgeSound`** (`Selvage/AccExtractChain.lean`) — the
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

/-- **`accSound_rbr`** (`Selvage/AccSoundRbr.lean`, [ACC-sound-rbr]). The
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

/-- **`OB2_depth_composition_nonneg_proved`** (`Selvage/Depth.lean`, [OB-2′]).
The REPAIRED loss-free depth-composition theorem (WARP 2025/753, Thm B.4),
fully discharged from `[OB-2a]`. No residual. -/
theorem manifest_OB2_depth_composition_nonneg_proved :
    OB2_depth_composition_nonneg :=
  OB2_depth_composition_nonneg_proved

/-- **`gameSlotBound_proved`** (`Selvage/Depth.lean`, [OB-2a], CLOSED). The
game-slot bound: the lazy-`rnd` resolver's exactly-uniform kernel, fully
proved (not reduced to a further hypothesis). No residual — this closes
the last gap `OB2_depth_composition_nonneg_proved` depends on. -/
theorem manifest_gameSlotBound_proved : GameSlotBound :=
  gameSlotBound_proved

/-- **`OB2_depth_composition_false`** (`Selvage/Depth.lean`) — **REFUTATION**:
the AUDITED, naively-stated `[OB-2]` depth-composition claim is
machine-checked FALSE (`Z = ∅`, `εrbr = -1`, `t = 0` — the sign of the
claimed bound breaks). The repaired obligation is
`OB2_depth_composition_nonneg`, proved above. Indexed here so the honesty
of "we refuted our own naive statement before repairing it" is legible,
not just claimed in prose. -/
theorem manifest_OB2_depth_composition_false : ¬ OB2_depth_composition :=
  OB2_depth_composition_false

/-- **`fsKeystone_proved`** (`Selvage/FiatShamir.lean`). The FS-of-RBR
knowledge-soundness-preservation keystone, UNCONDITIONAL — rides
`gameSlotBound_proved`, nothing further assumed. Residual (deployment, not
this theorem's own gap): `[FS-ROM]` (uniform→hash-derived schedule
transport, closed at the fixed-chain level by `lightClientFS_sound` below)
and `[LC-fs-adaptive]` (grinding-adversary pricing). -/
theorem manifest_fsKeystone_proved : FsOfRbrKeystone :=
  fsKeystone_proved

/-! ## §5. Light client — the apex, its soundness, its non-interactive form -/

/-- **`lightClient_attests`** (`Selvage/LightClient.lean`) — **THE v0 APEX**
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

/-- **`oneShot_lightClient_false`** (`Selvage/LightClient.lean`,
`LCExample`) — **REFUTATION**: verifying the aggregate at a SINGLE FIXED
schedule, even with a seam-ok chain and honest genesis, does NOT attest the
history (`phantomChain` forges it). This is why the one-shot form must be
probabilistic — `lightClientSound` below — never an algebraic theorem. -/
theorem manifest_oneShot_lightClient_false :
    ¬ (∀ (A₀ : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1)
        (ch : Chain (ZMod 5) (ZMod 5) (Fin 4) 1),
        Aligned A₀ ch →
          Verifies (reedSolomonCode Minidregg.Selvage.RSExample.dom₅ 2) A₀ →
          SeamOk ch →
          Verifies (reedSolomonCode Minidregg.Selvage.RSExample.dom₅ 2)
            (aggregate Minidregg.Selvage.LCExample.linRoot (fun _ => 1) A₀ ch) →
          attests (reedSolomonCode Minidregg.Selvage.RSExample.dom₅ 2) ch) :=
  Minidregg.Selvage.LCExample.oneShot_lightClient_false

/-- **`lightClientSound`** (`Selvage/LightClientSound.lean`) — **[LC-sound],
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

/-- **`lightClientSound_exact`** (`Selvage/LightClientSound.lean`). Exact-word
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

/-- **`lightClientFS_sound`** (`Selvage/LightClientFS.lean`) — **[LC-sound-fs],
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

/-- **`decider_sound`** (`Selvage/Decider.lean`). The final one-time check: the
decider's verdict IS `AccClaim.Satisfies`, definitionally. Both soundness
and completeness in one `Iff.rfl`. No residual. -/
theorem manifest_decider_sound {Root : Type*} {F : Type*} [Field F]
    {ι : Type*} {r : ℕ}
    (C : Submodule F (ι → F)) (A : AccClaim Root F ι r) (f : ι → F) :
    decider C A f ↔ AccClaim.Satisfies C A f :=
  decider_sound C A f

/-- **`decider_depth_independent`** (`Selvage/Decider.lean`, LOOM §6's one-time
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

/-- **`deciderProx_sound`** (`Selvage/DeciderProximity.lean`, [DEC-proximity]).
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

/-- **`sumcheck_lambda_secure`** (`Selvage/SmallField.lean`, [OB-8]). The
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

/-- **`smallField_bound_vacuous`** (`Selvage/SmallField.lean`, [OB-8]) —
**REFUTATION-SHAPED TOOTH**: at `|F| = 5`, `v·d = 100` the "soundness bound"
`v·d/|F| = 20 ≥ 1` holds for EVERY event — a bound any adversary satisfies
secures nothing. Demonstrates the extension degree is LOAD-BEARING for
`sumcheck_lambda_secure`, not decorative. -/
theorem manifest_smallField_bound_vacuous (E : (Fin 100 → ZMod 5) → Prop) :
    uniformProb (Fin 100 → ZMod 5) E
      ≤ (100 : ℝ) * ((1 : ℝ) / Fintype.card (ZMod 5)) :=
  smallField_bound_vacuous E

/-- **`committed_extract_bind`** (`Selvage/Commitment.lean`) — **[ACC-extract-bind]
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

/-- **`idealCommitment`** (`Selvage/Commitment.lean`) — the honest floor's
INHABITATION witness: root = word, verify = symbol equality, binding a
two-line theorem. Re-exported as a `def` (it is the witness OBJECT, not a
`Prop`); confirmed AXIOM-FREE by `#print axioms` below (no `Classical.choice`,
no `propext`, no `Quot.sound` — it doesn't merely avoid `sorry`, it avoids
every logical axiom Lean tracks). Residual: `[COMMIT-CR]`, the deployed
Merkle/sponge realizer, priced only relative to collision-resistance. -/
noncomputable def manifest_idealCommitment (F ι : Type*) :
    BindingCommitment (ι → F) F ι Unit :=
  idealCommitment F ι

/-- **`committed_word_recovered`** (`Selvage/Erasure.lean`) — closes
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

/-- **`mask_bijOn`** (`Selvage/ZK.lean`, [OB-4-hiding] core). The masking map
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

/-- **`t_symbols_uniform`** (`Selvage/ZKHiding.lean`) — the MDS `t`-wise
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
Selvage's `foldClaims`, to ONE accumulated claim satisfied by the folded word
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

/-- **`loomV0_holds`** (`Assurance/SelvageV0.lean`) — **THE v0 CAPSTONE**: the
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
    SelvageV0Guarantee foldRoot C A₀ ch δ errstar ws f₀ γs γalt h₀ hs S w e f :=
  loomV0_holds halign hdC hMCA hδ0 hδB hδC herr0 hlen hfalse hseam hne hbase
    hpert hrt hopen hsat f

/-- **`loomV0_light_client`** (`Assurance/SelvageV0.lean`) — the
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

/-! ## §8. The ZK argument of knowledge — OB-4, the confirmed-absent-from-the-literature slot -/

/-- **`rs_maskedOpeningHiding`** (`Selvage/ZKHiding.lean`) — masked-opening
hiding for Reed–Solomon, PROVED: at any `t ≤ d` distinct query points and
nonzero challenge, the `t` opened symbols of `f + γ•r` (uniform mask
codeword `r`) are exactly simulatable without the witness. Both dials are
load-bearing (`t ≤ d` refuted at `t = d+1`; `γ ≠ 0` refuted next). -/
theorem manifest_rs_maskedOpeningHiding {F : Type*} [Field F] {ι : Type*} {t d : ℕ}
    (dom : ι ↪ F) (ht : t ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) {γ : F} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (reedSolomonCode dom d) q γ :=
  rs_maskedOpeningHiding dom ht hq hγ

/-- **`not_maskedOpeningHiding_zero`** (`Selvage/ZKHiding.lean`) —
**REFUTATION-SHAPED TOOTH**: at `γ = 0` there is NO hiding — the opened
support collapses to the witness's own symbols. The mask challenge is what
makes the witness private, not decoration. -/
theorem manifest_not_maskedOpeningHiding_zero {F : Type*} [Field F] {ι : Type*} {t : ℕ}
    (C : Submodule F (ι → F)) {q : Fin t → ι} (ht : 0 < t) :
    ¬ MaskedOpeningHiding C q (0 : F) :=
  not_maskedOpeningHiding_zero C ht

/-- **`constrainedMask_hiding`** (`Selvage/ConstrainedMask.lean`,
[OB-4-hiding-rbr] gap (1) CLOSED, `r = 1`). Hiding holds even when the mask
is CONFINED to the mask claim's homogeneous solution space — a mask that
respects the claim AND still hides — at the tightened bound `t + 1 ≤ d`.
Residual: the sub-UD seam this tightening opens is `[ZK-RBR-extract]`
lemma A (see `selvage_zk_argument`). -/
theorem manifest_constrainedMask_hiding {F : Type*} [Field F] {ι : Type*} {t d : ℕ}
    (dom : ι ↪ F) (pt : ι) (ht : t + 1 ≤ d)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) (hpt : ∀ j, q j ≠ pt)
    {γ : F} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (constrainedMaskSpace dom d pt) q γ :=
  constrainedMask_hiding dom pt ht hq hpt hγ

/-- **`zkArgument_of_hiding`** (`Selvage/ZkArgument.lean`) — the single-round
COEXISTENCE theorem: completeness (`foldClaims_satisfies`), knowledge
soundness (`accKnowledgeSound`), and zero-knowledge (`MaskedOpeningHiding`)
discharge the SAME structure's three fields on the SAME parameter tuple.
The quantifier-position separation (only `knowledge_sound` sees a second
challenge) is visible in the field types. No residual at this round. -/
theorem manifest_zkArgument_of_hiding {Root : Type*} {F : Type*} [Field F]
    {ι : Type*} {r t : ℕ}
    {C : Submodule F (ι → F)} (foldRoot : Root → F → Root → Root)
    {A B : AccClaim Root F ι r} {M : Submodule F (ι → F)} {q : Fin t → ι} {γ : F}
    (hMB : ∀ g ∈ M, AccClaim.Satisfies C B g) (hZK : MaskedOpeningHiding M q γ) :
    ZkArgument C foldRoot A B M q γ :=
  zkArgument_of_hiding foldRoot hMB hZK

/-- **`rbrZk_multiround`** (`Selvage/RbrZeroKnowledge.lean`) — the multi-round
coexistence: an aligned chain with linkwise-distinct challenge pairs and
per-round mask hiding carries a whole-chain ZK argument (`RbrZkArgument`) —
the chain-level two-point extractor and the composed round-by-round
simulator on one object. The simulator's type carries no counterfactual
schedule, no transcript, no witness. -/
theorem manifest_rbrZk_multiround {Root : Type*} {F : Type} [Field F]
    {ι : Type*} {r t : ℕ}
    {C : Submodule F (ι → F)} (foldRoot : Root → F → Root → Root)
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {M : Fin ch.length → Submodule F (ι → F)}
    {q : Fin ch.length → Fin t → ι} {γs γalt : ℕ → F}
    (halign : Aligned A₀ ch)
    (hne : ∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hZK : ∀ k : Fin ch.length, MaskedOpeningHiding (M k) (q k) (γs (k : ℕ))) :
    RbrZkArgument C foldRoot A₀ ch M q γs γalt :=
  rbrZk_multiround foldRoot halign hne hZK

/-- **`triangularHiding_of_rounds`** (`Selvage/ZkTriangular.lean`) — the
DEPLOYED recommitment schedule hides: per-round masked-opening hiding
composes through the triangular (each round opens the recommitted partial
fold) opening map — the backward induction through the ∀-witness quantifier
closes. No residual at the hiding level. -/
theorem manifest_triangularHiding_of_rounds {F : Type*} [Field F] {ι : Type*} {t n : ℕ}
    {M : Fin n → Submodule F (ι → F)} {q : Fin n → Fin t → ι} {γs : ℕ → F}
    (H : ∀ k : Fin n, MaskedOpeningHiding (M k) (q k) (γs (k : ℕ))) :
    TriangularHiding M q γs :=
  triangularHiding_of_rounds H

/-- **`extracted_openings_are_jointOpen`** (`Selvage/ZkExtraction.lean`) —
quantifier confinement, definitional face: the per-round openings of the
extracted masked words ARE `jointOpen` — the exact map whose image the ZK
simulator proves uniform and witness-free. The extractor's leakage surface
and the simulator's support are ONE object, by `rfl`. -/
theorem manifest_extracted_openings_are_jointOpen {F : Type} [Field F]
    {ι : Type*} {t n : ℕ}
    (q : Fin n → Fin t → ι) (ηs : ℕ → F) (ws gs : Fin n → ι → F) :
    (fun k => openSymbols (q k) (maskedWord ηs ws gs k))
      = jointOpen q ηs ws gs :=
  extracted_openings_are_jointOpen q ηs ws gs

/-- **`maskedChainExtraction_holds`** (`Selvage/ZkExtraction.lean`) — the
mask-augmented chain extraction: from the base, `n` link-perturbed, and `n`
MASK-perturbed transcripts, the extractor recovers EVERY round's
`(witness, mask)` pair exactly, at arbitrary depth. The type carries BOTH
counterfactual schedules — contrast the simulator, whose type carries
neither; that separation is the confinement `[ZK-RBR-*]` fought for. -/
theorem manifest_maskedChainExtraction_holds {F : Type} [Field F] {ι : Type*} {n : ℕ}
    {γs γalt ηs ηalt : ℕ → F}
    (hγ : ∀ k : Fin n, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hγ0 : ∀ k : Fin n, γs (k : ℕ) ≠ 0)
    (hη : ∀ k : Fin n, ηs (k : ℕ) ≠ ηalt (k : ℕ)) :
    MaskedChainExtraction (ι := ι) γs γalt ηs ηalt n :=
  maskedChainExtraction_holds hγ hγ0 hη

/-- **`masked_pair_ambiguous`** (`Selvage/ZkExtraction.lean`) —
**REFUTATION-SHAPED CONFINEMENT TOOTH**: the δ-schedule family can NEVER
peel the `(witness, mask)` pair — two distinct fully-valid decompositions
share EVERY transcript at EVERY link schedule. The mask counterfactuals the
extractor consumes are provably not a function of what the ZK distinguisher
sees; this impossibility IS hiding doing its job. -/
theorem manifest_masked_pair_ambiguous {Root : Type*} {F : Type} [Field F]
    {ι : Type*} {r : ℕ}
    {C : Submodule F (ι → F)} {ch : Chain Root F ι r} {ηs : ℕ → F}
    {ws gs : Fin ch.length → ι → F}
    (hws : ∀ k, AccClaim.Satisfies C (ch.get k).claim (ws k))
    (hgsC : ∀ k, gs k ∈ C)
    (hker : ∀ k i, (ch.get k).claim.weights i (gs k) = 0)
    {k₀ : Fin ch.length} (hnz : gs k₀ ≠ 0) :
    ∃ ws' gs' : Fin ch.length → ι → F,
      (ws', gs') ≠ (ws, gs) ∧
      (∀ k, AccClaim.Satisfies C (ch.get k).claim (ws' k)) ∧
      (∀ k, gs' k ∈ C ∧ ∀ i, (ch.get k).claim.weights i (gs' k) = 0) ∧
      maskedWord ηs ws' gs' = maskedWord ηs ws gs ∧
      ∀ (δ : ℕ → F) (f₀ : ι → F),
        flatFold δ f₀ (maskedWord ηs ws' gs')
          = flatFold δ f₀ (maskedWord ηs ws gs) :=
  masked_pair_ambiguous hws hgsC hker hnz

/-- **`zkRbrGame_holds`** (`Selvage/ZkRbrGame.lean`) — the ASSEMBLED game: an
aligned chain with genuinely two-point challenge dials and per-round mask
hiding carries the full ZK-argument RBR game — all nine fields (completeness,
adversarial chain extraction, exact masked inversion, the pair peel, the
straightline committed-column seam, the counterfactual-free simulator, both
round-error scales, FS composition) by CITATION only, nothing re-derived. -/
theorem manifest_zkRbrGame_holds {Root : Type*} {F : Type} [Field F]
    {ι : Type*} {t r : ℕ}
    [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {C : Submodule F (ι → F)}
    (foldRoot : Root → F → Root → Root) {A₀ : AccClaim Root F ι r}
    {ch : Chain Root F ι r} {M : Fin ch.length → Submodule F (ι → F)}
    {q : Fin ch.length → Fin t → ι} {γs γalt ηs ηalt : ℕ → F}
    (halign : Aligned A₀ ch)
    (hγ : ∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hγ0 : ∀ k : Fin ch.length, γs (k : ℕ) ≠ 0)
    (hη : ∀ k : Fin ch.length, ηs (k : ℕ) ≠ ηalt (k : ℕ))
    (hZK : ∀ k : Fin ch.length, MaskedOpeningHiding (M k) (q k) (ηs (k : ℕ))) :
    ZkRbrGame C foldRoot A₀ ch M q γs γalt ηs ηalt :=
  zkRbrGame_holds foldRoot halign hγ hγ0 hη hZK

/-- **`accFsSound_native`** (`Selvage/AccRbrInstance.lean`,
[ZK-RBR-game-resid] DISCHARGED at the IOR resolution). The Fiat–Shamir
compilation of the accumulator chain's OWN reduction — the literal
WARP-Def-4.2 `Reduction`/`RbrKnowledgeSoundness` pair, BUILT, not
caller-supplied — is straightline knowledge-sound at the
`(t + k)·accRbrError` grinding factor. Residual: `[ACC-rbr-bcs]` (the
BCS root-and-columns message alphabet; here the alphabet is full round
words). -/
theorem manifest_accFsSound_native {Root F : Type} [Field F] [Fintype F] [DecidableEq F]
    {m r : ℕ} (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) {dC Bstar : ℝ} (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hBstar : δs ≤ 1 - Bstar) (hdC2 : δs ≤ dC / 2)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ)
    (Z : Set (Stmt (accReduction C foldRoot ch hm hch δs hδpos hδone))) :
    FsStraightlineKnowledgeSoundness
      (accReduction C foldRoot ch hm hch δs hδpos hδone) Z
      (fun _s t δ => ((t : ℝ) + (ch.length : ℝ)) * accRbrError F errstar δ) :=
  accFsSound_native C foldRoot ch hm hch δs hδpos hδone errstar hdC hMCA
    hBstar hdC2 hstar Z

/-- **`selvage_zk_argument`** (`Selvage/ZkRbrGame.lean`) — **THE OB-4 HEADLINE**:
Selvage has a machine-checked straightline NON-INTERACTIVE ZERO-KNOWLEDGE
ARGUMENT OF KNOWLEDGE for the accumulated claim — every aligned chain with
two-point dials and hiding rounds carries the full game, and the FS carrier
holds UNCONDITIONALLY (`fsKeystone_proved`). Covered scope, in the same
sentence: modulo the floor (`[FS-ROM]`, `[COMMIT-CR]`, the standing `hPG`),
the sub-UD seam `[ZK-RBR-extract]` lemma A, and `[ACC-rbr-bcs]`. Proven
parameters only: `err⋆(δ) + 1/|F|` per round, `(t + k)·ε` after FS. -/
theorem manifest_selvage_zk_argument {Root : Type*} {F : Type} [Field F]
    {ι : Type*} {t r : ℕ}
    [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (∀ (C : Submodule F (ι → F)) (foldRoot : Root → F → Root → Root)
        (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
        (M : Fin ch.length → Submodule F (ι → F))
        (q : Fin ch.length → Fin t → ι) (γs γalt ηs ηalt : ℕ → F),
        Aligned A₀ ch →
        (∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ)) →
        (∀ k : Fin ch.length, γs (k : ℕ) ≠ 0) →
        (∀ k : Fin ch.length, ηs (k : ℕ) ≠ ηalt (k : ℕ)) →
        (∀ k : Fin ch.length, MaskedOpeningHiding (M k) (q k) (ηs (k : ℕ))) →
        ZkRbrGame C foldRoot A₀ ch M q γs γalt ηs ηalt) ∧
      FsOfRbrSound :=
  selvage_zk_argument

/-! ## §9. The arithmetization compiler — circuit ⟺ executor by initiality, retired by the proven sumcheck -/

/-- **`eval_agrees_exec`** (`Compiler/Air.lean`) — CIRCUIT ⟺ EXECUTOR, FREE
BY INITIALITY: the DSL's circuit fold and the independent hand-recursed
executor agree on EVERY expression, zero induction at the use site. N3
applied to arithmetization: drift is not avoided, it is IMPOSSIBLE.
Axiom-audited on `[propext, Quot.sound]` — no choice (see §14). -/
theorem manifest_eval_agrees_exec {F : Type u} [Field F] {Idx : Type u} (asg : Idx → F) :
    Compiler.evalExec asg = Compiler.eval asg (F := F) (Idx := Idx) :=
  Compiler.eval_agrees_exec asg

/-- **`boolGadget_correct`** (`Compiler/Air.lean`) — the first DERIVED
gadget: the booleanity assertion `x·(x−1)` accepts iff the wire is `0` or
`1` — semantics straight out of the initiality transfer, no bespoke
soundness argument. The pattern every later gadget follows. -/
theorem manifest_boolGadget_correct {F : Type u} [Field F] {Idx : Type u}
    (asg : Idx → F) (i : Idx) :
    Compiler.accepts asg (Compiler.boolGadget i) ↔ (asg i = 0 ∨ asg i = 1) :=
  Compiler.boolGadget_correct asg i

/-- **`flatten_constraint_iff`** (`Compiler/AirFlatten.lean`,
[AIR-flatten]). The flattened degree-≤2 gate system with the root pinned to
`0` is satisfiable iff the circuit accepts — sound by wire-forcing, complete
by the forced aux extension. The deployment-shaped gate system means exactly
what the expression means. -/
theorem manifest_flatten_constraint_iff {F : Type u} [Field F] {Idx : Type u}
    (asg : Idx → F) (t : Compiler.Term (Compiler.AirSig F Idx)) (n₀ : ℕ) :
    (∃ auxv : ℕ → F, Compiler.gatesHold asg auxv (Compiler.flatten t n₀).gates ∧
        (Compiler.flatten t n₀).out.read asg auxv = 0)
      ↔ Compiler.accepts asg t :=
  Compiler.flatten_constraint_iff asg t n₀

/-- **`multiAffine_ext`** (`Selvage/MultilinearExtension.lean`) — MLE
uniqueness: two multi-affine functions agreeing on the hypercube are EQUAL —
the MLE is THE multilinear interpolant, not just one of them. -/
theorem manifest_multiAffine_ext {F : Type*} [CommRing F] {m : ℕ} [Nontrivial F]
    {g₁ g₂ : (Fin m → F) → F}
    (h₁ : MultiAffine g₁) (h₂ : MultiAffine g₂)
    (hcube : ∀ b, g₁ (cubePt b) = g₂ (cubePt b)) : g₁ = g₂ :=
  multiAffine_ext h₁ h₂ hcube

/-- **`mle_retires_constraint`** (`Selvage/MultilinearExtension.lean`,
[SC-reshape] DISCHARGED). The turnkey decider sumcheck: a `LinearConstraint`
transported to the hypercube with the honest side BUILT (the MLE realizer,
constructed and consumed in one statement) — a violating word survives any
admissible prover with probability `≤ v/|F|`. Only adversary-side hypotheses
remain. -/
theorem manifest_mle_retires_constraint {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] {v : ℕ}
    (e : ι ≃ (Fin v → Bool)) {w : ι → F} {c : LinearConstraint ι F}
    (hviol : ¬ Satisfies w c)
    {prover : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable prover)
    (hProverDeg : ∀ (χ : ℕ → F) (i : ℕ), i < v →
      (prover χ i).degree < ((1 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin v → F)
      (fun r => SumcheckAccepts (prover (chalOf r))
        (mleHonest (fun b => constraintSummand c w (e.symm b)) (chalOf r))
        c.target (trueSum c w) r)
      ≤ (v : ℝ) * (1 / Fintype.card F) :=
  mle_retires_constraint e hviol hpm hProverDeg

/-- **`airSumcheck_sound`** (`Assurance/AirSumcheck.lean`, [AIR-sumcheck],
the linear face). A rejected assignment whose aux valuation leaves every MUL
gate intact violates SOME linear constraint of the encoded system — and
Selvage's PROVEN sumcheck retires that violation at `v·d/|F|`. Residual at this
entry: the quadratic channel, closed next. -/
theorem manifest_airSumcheck_sound {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {v d : ℕ} (asg : Idx → F) (t : Compiler.Term (Compiler.AirSig F Idx))
    (hrej : ¬ Compiler.accepts asg t) (auxv : ℕ → F)
    (hmul : ∀ g ∈ (Compiler.flatten t 0).gates,
      g.op = Compiler.GateOp.mul → g.holds asg auxv) :
    ∃ c ∈ flatLinearSystem t,
      ¬ Satisfies (wireWord (N := (Compiler.flatten t 0).next) asg auxv) c ∧
      ∀ (prover honest : ℕ → Polynomial F),
        (∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ)) →
        (∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ)) →
        (∀ (r : Fin v → F), ∀ i, i < v →
          (honest i).eval 0 + (honest i).eval 1
            = scChain (trueSum c (wireWord (N := (Compiler.flatten t 0).next) asg auxv))
                honest (chalOf r) i) →
        uniformProb (Fin v → F)
          (SumcheckAccepts prover honest c.target
            (trueSum c (wireWord (N := (Compiler.flatten t 0).next) asg auxv)))
          ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) :=
  airSumcheck_sound asg t hrej auxv hmul

/-- **`airGateSystem_sound`** (`Assurance/AirSumcheckQuadratic.lean`) —
**THE FULL-GATE HEADLINE**: a rejected assignment is caught under EVERY aux
valuation — either a linear constraint is violated and the proven adaptive
sumcheck retires it at `v·d/|F|`, or a MUL gate's quadratic claim is
violated and the proven sumcheck retires it at `m·2/|F|` with the honest
side BUILT. NO unretired channel: the derived arithmetization inherits the
proof system's soundness, completely. -/
theorem manifest_airGateSystem_sound {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {v d m : ℕ} (asg : Idx → F) (t : Compiler.Term (Compiler.AirSig F Idx))
    (hrej : ¬ Compiler.accepts asg t) (auxv : ℕ → F)
    (enc : Fin (mulGates (Compiler.flatten t 0).gates).length ↪ (Fin m → Bool)) :
    (∃ c ∈ flatLinearSystem t,
      ¬ Satisfies (wireWord (N := (Compiler.flatten t 0).next) asg auxv) c ∧
      ∀ (prover honest : (ℕ → F) → ℕ → Polynomial F),
        PrefixMeasurable prover → PrefixMeasurable honest →
        (∀ (χ : ℕ → F) (i : ℕ), i < v →
          (prover χ i).degree < ((d + 1 : ℕ) : WithBot ℕ)) →
        (∀ (χ : ℕ → F) (i : ℕ), i < v →
          (honest χ i).degree < ((d + 1 : ℕ) : WithBot ℕ)) →
        (∀ r : Fin v → F, ∀ i, i < v →
          (honest (chalOf r) i).eval 0 + (honest (chalOf r) i).eval 1
            = scChain (trueSum c (wireWord (N := (Compiler.flatten t 0).next) asg auxv))
                (honest (chalOf r)) (chalOf r) i) →
        uniformProb (Fin v → F)
          (fun r => SumcheckAccepts (prover (chalOf r)) (honest (chalOf r)) c.target
            (trueSum c (wireWord (N := (Compiler.flatten t 0).next) asg auxv)) r)
          ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F))
    ∨ (∃ k, ¬ Satisfies (defectWord (mulGates (Compiler.flatten t 0).gates) enc asg auxv)
          (mulConstraint (mulGates (Compiler.flatten t 0).gates) enc k) ∧
        QuadRetired (gateTableA (mulGates (Compiler.flatten t 0).gates) enc asg auxv)
          (gateTableB (mulGates (Compiler.flatten t 0).gates) enc asg auxv)
          (gateTableC (mulGates (Compiler.flatten t 0).gates) enc asg auxv)
          (mulConstraint (mulGates (Compiler.flatten t 0).gates) enc k)) :=
  airGateSystem_sound asg t hrej auxv enc

/-! ## §10. The note-spend gadgets — the SOUND shielded spend, all derived -/

/-- **`rangeGadget_correct`** (`Compiler/AirRange.lean`, [AIR-range]). The
range gadget (k booleanity assertions + the recomposition assertion, all DSL
terms) accepts iff every bit wire is boolean AND the value wire is their
weighted sum — derived from `boolGadget_correct`, no new induction. -/
theorem manifest_rangeGadget_correct {F : Type u} [Field F] {Idx : Type u} {k : ℕ}
    (asg : Idx → F) (xi : Idx) (bits : Fin k → Idx) :
    Compiler.systemAccepts asg (Compiler.rangeGadget xi bits) ↔
      ((∀ i, asg (bits i) = 0 ∨ asg (bits i) = 1) ∧
        asg xi = ∑ i : Fin k, asg (bits i) * (2 : F) ^ (i : ℕ)) :=
  Compiler.rangeGadget_correct asg xi bits

/-- **`hashConstraint_correct`** (`Compiler/AirHash.lean`, [AIR-poseidon]).
The hash constraint (a Poseidon-style permutation gadget, ALL rounds,
derived) accepts iff the nullifier wire carries EXACTLY the executor hash of
the note wires — sound AND complete. That the hash is hard to invert or
collide is `[COMMIT-CR]`, the named floor, never a theorem here. -/
theorem manifest_hashConstraint_correct {F : Type u} [Field F] {Idx : Type u} {w : ℕ}
    [NeZero w] (asg : Idx → F) (spec : Compiler.PermSpec F w)
    (nullifier : Idx) (note : Fin w → Idx) :
    Compiler.systemAccepts asg (Compiler.hashConstraint spec nullifier note) ↔
      asg nullifier = Compiler.hashExec spec fun i => asg (note i) :=
  Compiler.hashConstraint_correct asg spec nullifier note

/-- **`membership_meaning`** (`Compiler/AirMembership.lean`,
[AIR-membership]). The depth-`k` Merkle membership gadget, closed both ways:
an assignment carrying `(leaf, root)` on the canonical wires satisfies it
IFF `leaf` is a genuine depth-`k` member under `root` (∃ siblings +
direction bits folding leaf to root). General depth. -/
theorem manifest_membership_meaning {F : Type u} [Field F]
    (spec : Compiler.PermSpec F 2) (k : ℕ) (leaf root : F) :
    (∃ asg : Compiler.MWire.{u} k → F,
        asg Compiler.MWire.leafW = leaf ∧ asg Compiler.MWire.rootW = root ∧
        Compiler.systemAccepts asg
          (Compiler.membershipGadget spec Compiler.MWire.leafW Compiler.MWire.rootW
            (Compiler.canonPath k))) ↔
      Compiler.memberAtDepth spec k root leaf :=
  Compiler.membership_meaning spec k leaf root

/-- **`noteSpend_correct`** (`Compiler/NoteSpend.lean`,
[PRIVATE-TURN-air]) — **THE COMPOSED SPEND IFF**: the three closed gadgets
(range + two hash constraints + membership) over ONE shared witness accept
iff all four meanings hold together — value decomposed, nullifier =
nfHash(note), commitment = cmHash(SAME note), root = Merkle fold of the SAME
commitment. Composition is list append; nothing else. -/
theorem manifest_noteSpend_correct {F : Type u} [Field F] {Idx : Type u} {w k : ℕ}
    [NeZero w] (asg : Idx → F) (nfSpec cmSpec : Compiler.PermSpec F w)
    (trSpec : Compiler.PermSpec F 2) (noteW : Fin w → Idx) (vIdx : Fin w)
    (bitsW : Fin k → Idx) (nullifierW commitW rootW : Idx)
    (path : List (Idx × Idx)) :
    Compiler.systemAccepts asg
        (Compiler.noteSpendSystem nfSpec cmSpec trSpec noteW vIdx bitsW
          nullifierW commitW rootW path) ↔
      (((∀ i, asg (bitsW i) = 0 ∨ asg (bitsW i) = 1) ∧
          asg (noteW vIdx) = ∑ i : Fin k, asg (bitsW i) * (2 : F) ^ (i : ℕ)) ∧
        (asg nullifierW = Compiler.hashExec nfSpec fun i => asg (noteW i)) ∧
        (asg commitW = Compiler.hashExec cmSpec fun i => asg (noteW i)) ∧
        ((∀ sd ∈ path, asg sd.2 = 0 ∨ asg sd.2 = 1) ∧
          asg rootW = Compiler.merkleMuxExec trSpec (asg commitW)
            (path.map fun sd => (asg sd.1, asg sd.2)))) :=
  Compiler.noteSpend_correct asg nfSpec cmSpec trSpec noteW vIdx bitsW
    nullifierW commitW rootW path

/-- **`noteSpend_binds`** (`Compiler/NoteSpend.lean`) — **SOUNDNESS**: any
accepted assignment IS a valid shielded spend of the note it carries
(`ValidSpend`: k-bit value ∧ nullifier = hash(note) ∧ commitment a member of
the tree). The hiding half is the ZK layer (`selvage_zk_argument`, §8) — cited,
not re-derived; forging a path needs a collision — `[COMMIT-CR]`, the
floor. -/
theorem manifest_noteSpend_binds {F : Type u} [Field F] {Idx : Type u} {w k : ℕ}
    [NeZero w] (asg : Idx → F) (nfSpec cmSpec : Compiler.PermSpec F w)
    (trSpec : Compiler.PermSpec F 2) (noteW : Fin w → Idx) (vIdx : Fin w)
    (bitsW : Fin k → Idx) (nullifierW commitW rootW : Idx)
    (path : List (Idx × Idx))
    (hacc : Compiler.systemAccepts asg
      (Compiler.noteSpendSystem nfSpec cmSpec trSpec noteW vIdx bitsW
        nullifierW commitW rootW path)) :
    Compiler.ValidSpend nfSpec cmSpec trSpec vIdx k path.length
      (asg nullifierW) (asg rootW) (fun i => asg (noteW i)) :=
  Compiler.noteSpend_binds asg nfSpec cmSpec trSpec noteW vIdx bitsW
    nullifierW commitW rootW path hacc

/-! ## §11. The kernel — the semantic substrate's universal objects and conservation teeth -/

/-- **`balanced_turn_universal`** (`Kernel/TurnBalancedLimit.lean`, N2b).
The turn INCLUDING conservation is a universal object: the agreement data is
a wide-pullback limit (N2a, reused verbatim), the balanced data is the
equalizer of the balance sum against zero over it, and the equalizer
includes monomorphically. Residual: the one-diagram fused form
`[N2b-fibered]`. -/
theorem manifest_balanced_turn_universal {ι : Type u} [Fintype ι]
    {Carrier Turn TurnId Bal : Type u} [AddCommMonoid Bal]
    (step : Carrier → Turn → Carrier) (turnId : ι → Carrier → TurnId)
    (halfEdge : ι → Carrier → Turn → Bal) [Nonempty ι] (t : Turn) :
    Nonempty (CategoryTheory.Limits.IsLimit (hyperedgeCone step turnId t))
      ∧ Nonempty (CategoryTheory.Limits.IsLimit (balancedFork step turnId halfEdge t))
      ∧ CategoryTheory.Mono (balancedFork step turnId halfEdge t).ι :=
  balanced_turn_universal step turnId halfEdge t

/-- **`gwrite_umap_frame`** (`Kernel/Verbs.lean`). The verb algebra's frame
discipline: `gwrite` changes the keyed map ONLY at the written address —
every other coordinate reads exactly as before (and conservation is
definitional, `gwrite_conserves`). -/
theorem manifest_gwrite_umap_frame (k : KernelState) (u : UKey) (v : Option ℤ)
    (u' : UKey) (h : u' ≠ u) :
    (gwrite k u v).umap u' = k.umap u' :=
  gwrite_umap_frame k u v u' h

/-- **`create_unbacked_breaks`** (`Kernel/Verbs.lean`) —
**REFUTATION-SHAPED TOOTH**: creating a cell that already carries a NONZERO
balance strictly BREAKS conservation. The zero-balance side-condition on
`create_conserves` is load-bearing, not decorative. -/
theorem manifest_create_unbacked_breaks (k : KernelState) (c : CellId) (a : AssetId)
    (hc : c ∉ k.accounts) (hbal : k.bal c a ≠ 0) :
    totalAsset (create k c) a ≠ totalAsset k a :=
  create_unbacked_breaks k c a hc hbal

/-- **`privateTurn_public_indistinguishable`** (`Kernel/PrivateTurn.lean`,
[PRIVATE-TURN-kernel]). Two private-witness turns agreeing on their PUBLIC
data present IDENTICAL public views, whatever their private witnesses — the
balance leg agrees because BOTH turns are valid (`balanced` pins both sums
to 0). The cryptographic form is `privateTurn_witness_hidden` (§12). -/
theorem manifest_privateTurn_public_indistinguishable {ι : Type v} [Fintype ι]
    {Pub Priv Turn TurnId Bal : Type u} [AddCommMonoid Bal] [DecidableEq TurnId]
    {step : Pub × Priv → Turn → Pub × Priv}
    {turnId : ι → Pub × Priv → TurnId}
    {halfEdge : ι → Pub × Priv → Turn → Bal}
    (H₁ H₂ : PrivateHyperedge ι Pub Priv Turn TurnId Bal step turnId halfEdge)
    (hpub : ∀ i, (H₁.x i).1 = (H₂.x i).1)
    (ht : H₁.t = H₂.t) (htid : H₁.tid = H₂.tid) :
    H₁.publicView = H₂.publicView :=
  privateTurn_public_indistinguishable H₁ H₂ hpub ht htid

/-- **`leaky_step_leaks`** (`Kernel/PrivateTurn.lean`) —
**REFUTATION-SHAPED TOOTH**: a step that funnels the witness into the
public half LEAKS it — the witness-blindness premise of
`post_public_agrees` is genuine, and a deployed step must actually
discharge it. -/
theorem manifest_leaky_step_leaks :
    ∃ (step : ℤ × ℤ → ℤ → ℤ × ℤ) (s₁ s₂ : ℤ × ℤ),
      s₁.1 = s₂.1 ∧ s₁.2 ≠ s₂.2 ∧ (step s₁ 0).1 ≠ (step s₂ 0).1 :=
  leaky_step_leaks

/-! ## §12. Deployment hardening — grinding adversaries, hidden witnesses -/

/-- **`lightClientGrinding_sound`** (`Selvage/LightClientGrinding.lean`,
[LC-fs-adaptive] CLOSED) — **THE GRINDING HEADLINE**: the FS light client
against an adversary issuing `t` oracle queries and choosing its chain
AFTER seeing the answers forges with probability at most
`(t + n)·[n·(err⋆(δ) + 1/|F|)]` — the WARP grinding factor scaling the
fixed-chain bound. Residual: `[LC-grinding-native]` (transporting the
`n`-sharper native per-round accounting into this event vocabulary). -/
theorem manifest_lightClientGrinding_sound {Root ι F : Type} [Field F] {r : ℕ}
    (foldRoot : Root → F → Root → Root)
    [Fintype ι] [DecidableEq ι] [DecidableEq F] [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)}
    {A₀ : AccClaim Root F ι r} {T : ℕ} {chs : Fin T → Chain Root F ι r}
    {qs : List (LcQuery Root F ι r)}
    {wss : Fin T → List (ι → F)} {f0s : Fin T → ι → F}
    {δ dC Bstar : ℝ} {errstar : ℝ → ℝ} {n : ℕ}
    (hnd : qs.Nodup)
    (hcov : ∀ (i : Fin T) (k : Fin (chs i).length),
      linkPrefix A₀ (chs i) (k : ℕ) ∈ qs)
    (hn : ∀ i, (chs i).length ≤ n)
    (hne : ∀ i, chs i ≠ []) (hinj : Function.Injective chs)
    (halign : ∀ i, Aligned A₀ (chs i))
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ)
    (hlen : ∀ i, (wss i).length = (chs i).length)
    (hfalse : ∀ i, ∃ p ∈ (chs i).zip (wss i), ∀ v ∈ C, relDist p.2 v ≤ δ →
        ¬ AccClaim.Satisfies C p.1.claim v)
    (d : (i : Fin T) → Fin (chs i).length → F) :
    uniformProb (Fin qs.length → F) (fun c => ∃ i,
        ∃ w, relDist (foldWords
            (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
            (f0s i) (wss i)) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot
            (padSched (fsSchedule (Oracle.ofList qs c) A₀ (chs i) (d i)))
            A₀ (chs i)) w)
      ≤ ((qs.length : ℝ) + (n : ℝ))
          * ((n : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ))) :=
  lightClientGrinding_sound foldRoot hnd hcov hn hne hinj halign hdC hMCA
    hδ0 hδB hδC herr0 hlen hfalse d

/-- **`phantomGrind_beats_fixed_bound`** (`Selvage/LightClientGrinding.lean`) —
**REFUTATION-SHAPED TOOTH**: the built F₅ grind succeeds at `9/25`, STRICTLY
above the fixed-chain sharp bound `1/5` each candidate alone attains. No
bound of the fixed-chain form (no try-count factor) survives a grinding
adversary — the `(t+n)` scaling above is necessary, not bookkeeping. -/
theorem manifest_phantomGrind_beats_fixed_bound
    (d : (i : Fin 2) → Fin (Minidregg.Selvage.LCGrindExample.grindChs i).length → ZMod 5) :
    1 / (Fintype.card (ZMod 5) : ℝ)
      < uniformProb (Fin 4 → ZMod 5) (fun c => ∃ i,
          Verifies (reedSolomonCode Minidregg.Selvage.RSExample.dom₅ 2)
            (aggregate Minidregg.Selvage.LCExample.linRoot
              (padSched (fsSchedule
                (Oracle.ofList Minidregg.Selvage.LCGrindExample.grindQs c)
                Minidregg.Selvage.LCExample.phantomGenesis
                (Minidregg.Selvage.LCGrindExample.grindChs i) (d i)))
              Minidregg.Selvage.LCExample.phantomGenesis
              (Minidregg.Selvage.LCGrindExample.grindChs i))) :=
  Minidregg.Selvage.LCGrindExample.phantomGrind_beats_fixed_bound d

/-- **`privateReceipt_witness_hidden`** (`Assurance/PrivateReceipt.lean`) —
the private-witness checkpoint at the receipt: two turns carrying DIFFERENT
committed receipt words produce the SAME opened-symbol support under
masking — the verifier's `t`-symbol spot-check cannot distinguish them.
Perfect, not computational. Tooth: `witness_hidden_needs_mask` (γ = 0
leaks). -/
theorem manifest_privateReceipt_witness_hidden {F : Type} [Field F]
    {ι : Type} [Fintype ι] {t d : ℕ}
    (dom : ι ↪ F) (ht : t ≤ d) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q)) {γ : F} (hγ : γ ≠ 0)
    (f₁ f₂ : ι → F) :
    (fun r => openSymbols q (mask f₁ γ r)) '' (reedSolomonCode dom d)
      = (fun r => openSymbols q (mask f₂ γ r)) '' (reedSolomonCode dom d) :=
  privateReceipt_witness_hidden dom ht hq hγ f₁ f₂

/-- **`privateTurn_witness_hidden`** (`Assurance/PrivateTurn.lean`) — the
hiding half of the private-witness TURN object: two `PrivateTurn`s with the
same public parameters but different witnesses are indistinguishable to the
spot-check. With `noteSpend_binds` (soundly constrains, §10) and
`selvage_zk_argument` (proved in ZK, §8), this completes the private-witness
arc: hides ∧ soundly constrains ∧ in zero knowledge. -/
theorem manifest_privateTurn_witness_hidden {F : Type} [Field F]
    {ι : Type} [Fintype ι] {t d : ℕ}
    (T : PrivateTurn ι F t d) (w₁ w₂ : ι → F) :
    (fun r => openSymbols T.q (mask w₁ T.γ r)) '' (reedSolomonCode T.dom d)
      = (fun r => openSymbols T.q (mask w₂ T.γ r)) '' (reedSolomonCode T.dom d) :=
  privateTurn_witness_hidden T w₁ w₂

/-! ## §13. The residual ledger — prose, honest, not stubs

Every tag below is a NAMED obligation with a realizer or an explicit open
half — never a `def : Prop := True`. Status as of this manifest (matches
`docs/LOOM-COMPLETE.md`): **the v0 soundness formalization is COMPLETE** —
what remains is exactly the three-assumption cryptographic FLOOR (named,
inhabited, the same floor every hash-based SNARK carries) and the BEYOND-v0
research (named, not proved, never on the label).

**Residuals CLOSED since this manifest's first revision** — the
consolidation §§8–12 index:

* **`[OB-4-hiding-rbr]`** — CLOSED. The formerly-open research half of the
  ZK slot landed whole: constrained-mask hiding (`constrainedMask_hiding`),
  the multi-round chain simulator (`rbrZk_multiround`), the deployed
  triangular recommitment schedule (`triangularHiding_of_rounds`),
  quantifier confinement of the extractor's counterfactuals
  (`maskedChainExtraction_holds` + `masked_pair_ambiguous`), assembled as
  `zkRbrGame_holds`; the headline is `selvage_zk_argument`.
* **`[ACC-sound-rbr-game]`** — CLOSED: at the chain resolution by the
  two-point extractor (`extractChain_sound`, §3) and at the IOR resolution
  by `accFsSound_native`, which BUILDS the literal WARP-Def-4.2 instance on
  the accumulator's own reduction. The BCS root-and-columns re-packaging is
  `[ACC-rbr-bcs]`, beyond v0.
* **`[LC-fs-adaptive]`** — CLOSED by `lightClientGrinding_sound` at the
  `(t+n)`-scaled bound; `phantomGrind_beats_fixed_bound` is the tooth that
  the try-count factor is necessary.
* **`[SC-reshape]`** — DISCHARGED: the MLE realizer is BUILT
  (`MultilinearExtension`; `mle_retires_constraint`, consumed by the
  arithmetization apex).
* **`[AIR-sumcheck]` / `[AIR-sumcheck-quadratic]`** — CLOSED:
  `airGateSystem_sound` retires the FULL gate system (linear ∧ quadratic)
  with the PROVEN sumcheck; no unretired channel. The arithmetization is
  DERIVED end to end (`eval_agrees_exec` → `flatten_constraint_iff` →
  `airGateSystem_sound`) — no hand-authored constraint anywhere.
* **`[PRIVATE-TURN-air]`** — CLOSED: `noteSpend_correct` /
  `noteSpend_binds`, the Lean-authored (derived, never hand-written) sound
  shielded spend. The private-witness arc is complete: hides
  (`privateTurn_witness_hidden`), soundly constrains (`noteSpend_binds`),
  proved in ZK (`selvage_zk_argument`).
* **`[ACC-extract-bind]`(b)** — CLOSED (first revision):
  `committed_extract_bind` + `committed_word_recovered` bind the extraction
  algebra's witnesses to the prover's COMMITMENT. `[ERASURE-list]` (beyond
  unique decoding) is the remaining open half.

**The IRREDUCIBLE cryptographic floor** — assumptions, not gaps; kept
minimal, named, and inhabited (never an unproved `axiom`, never a
zero-instance class):

* **`hPG` / `[PROX-fold-distance]`** — the RS proximity gap at macroscopic
  δ (WHIR Thm 4.8 / BCIKS 2020/654), consumed as an explicit HYPOTHESIS
  everywhere (the `hPG`/`hMCA` premises above), proved unconditionally
  below the quantization radius (`foldDistancePreserving_of_lt_inv_card`)
  and at exact membership. The rate<1 soundness rides it; the whole tree
  quotes it rather than assuming it.
* **`[FS-ROM]`** — the deployed sponge realizes the lazy-sampling oracle
  handler; the handler is inhabited by `Oracle.empty`, no axiom. The
  uniform→hash-derived transport itself is proved (`lightClientFS_sound`,
  fixed chain; `lightClientGrinding_sound`, grinding).
* **`[COMMIT-CR]`** — the deployed Merkle/sponge realizes
  `BindingCommitment` only relative to collision resistance.
  `idealCommitment` inhabits the abstraction AXIOM-FREE, binding is proven
  load-bearing, and `NoteSpend` exhibits a toy-hash collision to keep the
  assumption's necessity concrete.

**BEYOND-v0 research, named** (Lean-authorable, genuinely open, none of it
on the label):

* **`[ZK-RBR-extract]` lemma A** — the sub-unique-decoding seam: recovering
  the recommitment increment from `t < d` opened columns via mutual
  correlated agreement. The straightline seam is proved at `t ≥ d`
  (`zkRbrGame_holds.straightline_seam`); the constrained-mask deployment
  (`t + r ≤ d`) needs the below-UD form.
* **`[ACC-rbr-bcs]`** — the BCS/root-alphabet packaging of the native RBR
  instance (PMsg = root + opened columns rather than the full round word);
  all the algebra is landed, the packaging re-run at that alphabet is not.
* **`[ACC-sound-list]` / `[ERASURE-list]`** — the Johnson/list-decoding
  regime; everything in this manifest is proved at UNIQUE DECODING (the
  conservative ~2–4× parameter regime).
* **`[OB-8-tower]`** — `sumcheck_lambda_secure` prices λ-bit security per
  field dial; the WHOLE-TOWER small-field accounting and the Binius-style
  binary-tower arithmetic are named, not assembled.
* **`[LC-grinding-native]`** — transporting `accFsSound_native`'s
  `n`-sharper per-round accounting into `lightClientGrinding_sound`'s event
  vocabulary; the bound SHAPE is closed, this is sharpening only.
* **`[DEC-prox-query]`** — `deciderProx_sound` counts ACCEPTING challenge
  TUPLES; the spot-check/repetition SCHEDULE a deployed verifier issues is
  not modeled.
* **NO PROVER; performance UNMEASURED.** Every theorem in this manifest is
  a VERIFIER guarantee over words, claims, and transcripts the tree
  already has in hand. There is no prover implementation, no emit path, no
  cost/latency measurement, and no wall-clock claim anywhere in this file
  or the tower it indexes.

None of these residuals is closed by this file — a manifest re-exports,
it does not discharge. Their status is exactly what the cited theorems'
own docstrings already say; repeating it here keeps the index legible
without re-litigating it. -/

/-! ## §14. Axiom audit — the complete v0 on the ATLAS-triple, machine-checked

No `sorry` anywhere in the cited tower (a `sorryAx` dependency below would
say so, loudly). The three axioms every nontrivial Mathlib-based proof
here inherits are Lean's own logical trio — `propext`, `Classical.choice`,
`Quot.sound` — never anything candidate-specific, never a proof-system
assumption smuggled in as an `axiom` declaration. The new headliners of
the COMPLETE v0 are audited below on the same triple: `selvage_zk_argument`
(the ZK argument of knowledge), `airGateSystem_sound` (full gate
soundness), `noteSpend_correct` (the sound shielded spend),
`lightClientGrinding_sound` (the grinding light client), and
`balanced_turn_universal` (the kernel's N2b). Sharper still:
`idealCommitment` (the commitment floor's witness) needs NONE of the trio,
and `eval_agrees_exec` (the arithmetization initiality keystone) needs no
`Classical.choice` — the circuit⟺executor agreement is choice-free. -/

/-- info: 'Minidregg.Assurance.manifest_loomV0_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_loomV0_holds
/-- info: 'Minidregg.Assurance.manifest_loomV0_light_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_loomV0_light_client
/-- info: 'Minidregg.Assurance.manifest_committed_extract_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_committed_extract_bind
/-- info: 'Minidregg.Assurance.manifest_idealCommitment' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms manifest_idealCommitment
/-- info: 'Minidregg.Assurance.manifest_oneShot_lightClient_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_oneShot_lightClient_false
/-- info: 'Minidregg.Assurance.manifest_OB2_depth_composition_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_OB2_depth_composition_false
/-- info: 'Minidregg.Assurance.manifest_selvage_zk_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_selvage_zk_argument
/-- info: 'Minidregg.Assurance.manifest_airGateSystem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_airGateSystem_sound
/-- info: 'Minidregg.Assurance.manifest_noteSpend_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_noteSpend_correct
/-- info: 'Minidregg.Assurance.manifest_lightClientGrinding_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_lightClientGrinding_sound
/-- info: 'Minidregg.Assurance.manifest_balanced_turn_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_balanced_turn_universal
/-- info: 'Minidregg.Assurance.manifest_eval_agrees_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_eval_agrees_exec

end Minidregg.Assurance
