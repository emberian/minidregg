/-
# `Assurance/ReceiptClaim.lean` — OB-3: the receipt Q as a native accumulated claim

THE KILL-CHECKPOINT (`docs/OB3-RECEIPT-ENCODING.md`). This bridge lives in `Assurance/`
by necessity: the import boundary forbids `Loom` importing `Kernel` (and vice versa), and
OB-3 is exactly where a kernel object (the receipt word, `Kernel/Receipt.lean`) meets a
proof-system object (the code, `Loom/ReedSolomon.lean`). `Assurance/` is unrestricted —
the apex layer — so it is the only lawful home.

**Checkpoint verdict (v0): PASS at the binding level.** The receipt word flattens to a
field vector; that vector determines the observed post-state (`flatten_faithful`), so
Loom's evaluation constraint `û(α)=μ` binds Q — the receipt IS the accumulator's committed
word, no verifier-simulator. The anti-ghost tooth (`flatten_tamper_changes`) fires
concretely: a tampered post-state produces a different word. No candidate failure site
(OB-3 §2 — authority non-amp, nullifier non-membership, keyed-map sparsity) bit at this
level; the keyed map's `none`/`some 0` hole was closed upstream by presence bits.

**Honestly scoped.** The BINDING half (a/b/c-word) is proved, over the DEPLOYED finite
field (not char-zero — that would be the ℤ-for-BabyBear trap), with the cast side-condition
carried as an explicit range-restricted hypothesis `castInj` (OB-3 §2's named range
obligation — never assumed silently; a global `Int.cast` injectivity would be FALSE at a
finite field, i.e. vacuous, so it is range-restricted). The FOLD half (d) is now ALSO
closed at the CLOSURE level: a `ReceiptClaim` is a native Loom accumulated claim
(`ReceiptClaim.acc`, provably the `AccClaim.ofConstraints` transport of its evaluation
constraints), and two receipt claims over one window fold via Loom's `foldClaims` to ONE
accumulated claim satisfied by the folded word (`receiptClaim_folds`, inheriting the
closure theorem `foldClaims_satisfies`) — the δ-proximity soundness of that fold stays
the SHARED `[ACC-sound]`/`[CRS-batch-sound]` residual, cited, not re-opened. The
PROXIMITY half (c at rate < 1) remains `[OB3-c-prox]`, stated with shape, never
`True`-stubbed, and NOT claimed as a landed keystone.
-/
import Kernel.Receipt
import Loom.ReedSolomon
import Loom.Accumulator

namespace Minidregg.Assurance

open Minidregg.Kernel Minidregg.Loom

/-- The flattened index of a window's word: one coordinate per observed balance cell, two
per observed key (presence bit at `0`, value at `1`) — the OB-3 §1 vector layout. -/
def FlatIx (w : Window) : Type :=
  {x // x ∈ w.cells} ⊕ ({x // x ∈ w.keys} × Fin 2)

instance (w : Window) : Fintype (FlatIx w) := by unfold FlatIx; infer_instance
instance (w : Window) : DecidableEq (FlatIx w) := by unfold FlatIx; infer_instance

variable {F : Type} [Field F]

/-- Flatten the receipt word into a field vector: balances cast; a key coordinate reads its
presence bit at `Fin 0`, its (cast) value at `Fin 1`. -/
def flatten (w : Window) (k : KernelState) : FlatIx w → F
  | Sum.inl c => (((uproj w k).1 c : ℤ) : F)
  | Sum.inr (u, i) =>
      let p := (uproj w k).2 u
      if i = 0 then ((p.1 : ℤ) : F) else ((p.2 : ℤ) : F)

/-- The finite range of ℤ-values a window observes on a state — balances, presence bits
(`{0,1}`), and key values. The cast side-condition `castInj` is scoped to this set: at a
finite deployed field, `Int.cast` is injective on a bounded range, and THIS is that range.
Never a global injectivity claim (that would be false, hence vacuous). -/
def obsRange (w : Window) (k : KernelState) : Finset ℤ :=
  (w.cells.image fun c => k.bal c.1 c.2)
    ∪ (w.keys.image fun u => (obsKey (k.umap u)).1)
    ∪ (w.keys.image fun u => (obsKey (k.umap u)).2)

/-- **Flatten faithfulness — the binding half of Q (OB-3 obligation a/b/c-word).** Given
the range-restricted cast injectivity, the field vector determines the receipt word, hence
(via `uproj_faithful`) the observed post-state. This is what makes "the receipt binds the
whole post-state" a fact about the WORD — so Loom's `û(α)=μ` constraint binds Q. -/
theorem flatten_faithful (w : Window) (k k' : KernelState)
    (castInj : ∀ z z' : ℤ, z ∈ obsRange w k → z' ∈ obsRange w k' →
      ((z : F) = (z' : F)) → z = z')
    (h : flatten (F := F) w k = flatten (F := F) w k') :
    uproj w k = uproj w k' := by
  rw [uproj_faithful]
  refine ⟨?_, ?_⟩
  · -- balances agree: read the `Sum.inl` coordinate, cast-inject over the range.
    intro c hc
    have hcell : ((((uproj w k).1 ⟨c, hc⟩ : ℤ)) : F) = ((((uproj w k').1 ⟨c, hc⟩ : ℤ)) : F) :=
      congrFun h (Sum.inl ⟨c, hc⟩)
    have hz : (uproj w k).1 ⟨c, hc⟩ ∈ obsRange w k := by
      unfold obsRange uproj
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
    have hz' : (uproj w k').1 ⟨c, hc⟩ ∈ obsRange w k' := by
      unfold obsRange uproj
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
    exact castInj _ _ hz hz' hcell
  · -- key entries agree: presence bit (Fin 0) + value (Fin 1) both cast-inject, then
    -- `obsKey_injective` recovers the `Option ℤ` entry.
    intro u hu
    have hp0 : ((((uproj w k).2 ⟨u, hu⟩).1 : ℤ) : F)
             = ((((uproj w k').2 ⟨u, hu⟩).1 : ℤ) : F) := by
      have := congrFun h (Sum.inr (⟨u, hu⟩, 0)); simpa [flatten] using this
    have hp1 : ((((uproj w k).2 ⟨u, hu⟩).2 : ℤ) : F)
             = ((((uproj w k').2 ⟨u, hu⟩).2 : ℤ) : F) := by
      have := congrFun h (Sum.inr (⟨u, hu⟩, 1)); simpa [flatten] using this
    have m0 : ((uproj w k).2 ⟨u, hu⟩).1 ∈ obsRange w k := by
      unfold obsRange uproj
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu))
    have m0' : ((uproj w k').2 ⟨u, hu⟩).1 ∈ obsRange w k' := by
      unfold obsRange uproj
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu))
    have m1 : ((uproj w k).2 ⟨u, hu⟩).2 ∈ obsRange w k := by
      unfold obsRange uproj
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)
    have m1' : ((uproj w k').2 ⟨u, hu⟩).2 ∈ obsRange w k' := by
      unfold obsRange uproj
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)
    have e0 := castInj _ _ m0 m0' hp0
    have e1 := castInj _ _ m1 m1' hp1
    -- the two coordinates are the components of the `ℤ × ℤ` obsKey pair
    have : (uproj w k).2 ⟨u, hu⟩ = (uproj w k').2 ⟨u, hu⟩ := Prod.ext e0 e1
    -- unfold uproj on the key half to recover the umap entries via obsKey_injective
    have hobs : obsKey (k.umap u) = obsKey (k'.umap u) := this
    exact obsKey_injective hobs

/-! ### The anti-ghost tooth — a tampered post-state changes the word (computing).

Concrete, over a real finite field `ZMod 5` (no general cast threading — the tamper is
exhibited and `decide`d). Honest state `k₀` vs the same state with nullifier 7 SPENT to
`some 0` — exactly the `none`/`some 0` hole the presence bit closes. The flattened words
differ at the presence-bit coordinate. -/

private def w₀ : Window := ⟨∅, {UKey.nullifier 7}⟩
private def k₀ : KernelState := ⟨∅, fun _ _ => 0, fun _ => [], fun _ => none⟩
private def k₀spent : KernelState :=
  { k₀ with umap := fun u => if u = UKey.nullifier 7 then some 0 else none }

/-- **[OB3-c teeth] — the anti-ghost, computing.** The tampered word differs from the
honest one at the nullifier's presence-bit coordinate: `flatten` at `ZMod 5` separates a
spent `some 0` from an unspent `none`. The binding is non-vacuous. -/
theorem flatten_tamper_changes :
    flatten (F := ZMod 5) w₀ k₀spent (Sum.inr (⟨UKey.nullifier 7, by decide⟩, 0))
      ≠ flatten (F := ZMod 5) w₀ k₀ (Sum.inr (⟨UKey.nullifier 7, by decide⟩, 0)) := by
  decide

/-! ### The receipt claim, and the two named residuals

`ReceiptClaim` packages Q as OB-3 §1's object: the word IS the flattening of the post-state
(membership in the code is the `rate < 1` refinement — at v0 the word is the vector; the
proximity constraint enters with the accumulator). The binding rides `flatten_faithful`. -/

/-- Q as an accumulated-claim shape: the committed word equals the post-state's flattening,
plus the evaluation-binding target `μ` (here the word itself; the digest/eval form rides
the γ-fold section below, where this claim becomes a native `AccClaim`). -/
structure ReceiptClaim (w : Window) (F : Type) [Field F] [DecidableEq F] where
  post : KernelState
  word : FlatIx w → F
  binds : word = flatten (F := F) w post

/-! ## [OB3-d-fold], the closure half — the receipt claim as a native accumulated claim

The kernel's receipt Q becomes a Loom `AccClaim`: the binding "word = flatten(post)" is
exactly a channel of per-coordinate EVALUATION constraints (`evalConstraint ix (word ix)`
— WHIR Def 4.5's in-domain `Z·eq` weight, one per flat coordinate), transported into
channel functionals by `dotWtL`. Two receipt claims over one window then fold by Loom's
γ-fold: `receiptClaim_folds` inherits the closure theorem `foldClaims_satisfies` (REUSED,
not re-derived), so the folded object is ONE well-formed accumulated claim satisfied by
the folded word — the receipt chain is one accumulated object, and the seam
`pre-root = prev.post-root` is a native accumulated equality at the claim level.

Index-arity note (why `ReceiptClaim.acc` is defined directly and not as
`AccClaim.ofConstraints` applied to `constraintList`): `foldClaims` requires both operands
at ONE channel arity `r`, and `ofConstraints` indexes by its list's length — for two
different claims those lengths are propositionally, not definitionally, equal. `acc`
indexes by the window's coordinate spine `ixList w` (shared by every claim over `w`, so
two claims are same-arity by `rfl`), and `acc_satisfies_iff_ofConstraints` PROVES it is
the same object as the `ofConstraints` transport over the RS code (through the sibling's
`constrainedRS`) — the fold-ready form and the batching form are one content, nothing
duplicated across the seam. -/

/-- The window's flat coordinates, enumerated — the channel spine every receipt claim
over `w` shares (what makes two claims' channels definitionally same-arity, hence
foldable). -/
noncomputable def ixList (w : Window) : List (FlatIx w) :=
  (Finset.univ : Finset (FlatIx w)).toList

theorem mem_ixList {w : Window} (ix : FlatIx w) : ix ∈ ixList w :=
  Finset.mem_toList.mpr (Finset.mem_univ ix)

/-- Quantifying over spine positions is quantifying over coordinates. -/
theorem forall_ixList {w : Window} {p : FlatIx w → Prop} :
    (∀ k : Fin (ixList w).length, p ((ixList w).get k)) ↔ ∀ ix : FlatIx w, p ix := by
  refine ⟨fun h ix => ?_, fun h k => h _⟩
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp (mem_ixList ix)
  exact hk ▸ h k

section Fold

variable {Root : Type} [DecidableEq F] {w : Window}

omit [DecidableEq F] in
/-- An evaluation constraint's pairing reads the word at its point (for ANY target — the
weight vector does not depend on it): `⟨(evalConstraint pt σ).wt, f⟩ = f pt`. -/
private theorem dotWt_evalConstraint {ι : Type} [Fintype ι] [DecidableEq ι]
    (pt : ι) (σ : F) (f : ι → F) :
    dotWt (evalConstraint pt σ).wt f = f pt :=
  satisfies_evalConstraint_iff.mpr rfl

/-- The receipt's binding channel in the sibling's list presentation
(`Loom/ConstrainedCode.lean`): one evaluation constraint per flat coordinate, target the
claimed word there. -/
noncomputable def ReceiptClaim.constraintList (rc : ReceiptClaim w F) :
    List (LinearConstraint (FlatIx w) F) :=
  (ixList w).map fun ix => evalConstraint ix (rc.word ix)

/-- **The OB-3 bridge.** The receipt claim as a native Loom accumulated claim:
commitment `rt` (opaque — binding is the commitment layer's obligation, per the
accumulator's root discipline), channel = the per-coordinate evaluation constraints of
the binding, arity the window's spine. Its satisfaction is EXACTLY "the word is
`flatten post` and lies in the code" (`acc_satisfies_iff`). -/
noncomputable def ReceiptClaim.acc (rc : ReceiptClaim w F) (rt : Root) :
    AccClaim Root F (FlatIx w) (ixList w).length :=
  ⟨rt, fun k =>
    (dotWtL (evalConstraint ((ixList w).get k) (rc.word ((ixList w).get k))).wt,
      rc.word ((ixList w).get k))⟩

/-- Two receipt claims over one window have literally the same channel functionals (an
evaluation constraint's weight vector does not depend on its target) —
`foldClaims_satisfies`'s `hshare` hypothesis, discharged by `rfl`: receipt claims are
born post-alignment. -/
theorem ReceiptClaim.acc_weights_shared (rc₁ rc₂ : ReceiptClaim w F) (rt₁ rt₂ : Root) :
    ∀ k, (rc₂.acc rt₂).weights k = (rc₁.acc rt₁).weights k :=
  fun _ => rfl

/-- Satisfaction of the bridged claim, characterized: the witness word IS the post-state's
flattening (and lies in the code) — OB-3 §1's Q, now read through Loom's claim relation. -/
theorem ReceiptClaim.acc_satisfies_iff {C : Submodule F (FlatIx w → F)}
    (rc : ReceiptClaim w F) (rt : Root) {f : FlatIx w → F} :
    AccClaim.Satisfies C (rc.acc rt) f ↔ f ∈ C ∧ f = flatten (F := F) w rc.post := by
  unfold AccClaim.Satisfies
  refine and_congr_right fun _ => ?_
  constructor
  · intro hall
    rw [← rc.binds]
    refine funext (forall_ixList.mp fun k => ?_)
    have h := hall k
    simp only [ReceiptClaim.acc, AccClaim.weights_apply, AccClaim.targets_apply,
      dotWtL_apply, dotWt_evalConstraint] at h
    exact h
  · rintro rfl
    intro k
    simp only [ReceiptClaim.acc, AccClaim.weights_apply, AccClaim.targets_apply,
      dotWtL_apply, dotWt_evalConstraint]
    exact (congrFun rc.binds _).symm

/-- The receipt claim is satisfied by its own word — the self-witness the fold consumes.
Code membership is a hypothesis: free at v0/full rate (`receiptClaim_folds_fullRate`);
its rate < 1 refinement is `[OB3-c-prox]`. -/
theorem ReceiptClaim.acc_self {C : Submodule F (FlatIx w → F)}
    (rc : ReceiptClaim w F) (rt : Root)
    (hmem : flatten (F := F) w rc.post ∈ C) :
    AccClaim.Satisfies C (rc.acc rt) (flatten (F := F) w rc.post) :=
  (rc.acc_satisfies_iff rt).mpr ⟨hmem, rfl⟩

/-- Membership in the sibling's constrained code cut by the receipt's constraint list is
exactly the binding: `constrainedRS` sees the same content the claim does. -/
theorem ReceiptClaim.mem_constrainedRS_iff_binds {dom : FlatIx w ↪ F} {d : ℕ}
    (rc : ReceiptClaim w F) {f : FlatIx w → F} :
    f ∈ constrainedRS dom d rc.constraintList
      ↔ f ∈ reedSolomonCode dom d ∧ f = flatten (F := F) w rc.post := by
  rw [mem_constrainedRS_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    rw [← rc.binds]
    refine funext fun ix => ?_
    have hmem : evalConstraint ix (rc.word ix) ∈ rc.constraintList :=
      List.mem_map.mpr ⟨ix, mem_ixList ix, rfl⟩
    exact satisfies_evalConstraint_iff.mp (h _ hmem)
  · rintro rfl c hc
    obtain ⟨ix, -, rfl⟩ := List.mem_map.mp hc
    exact satisfies_evalConstraint_iff.mpr (congrFun rc.binds ix).symm

/-- **The two presentations are one object** (the `AccClaim.ofConstraints` fit): over the
RS code, the fold-ready bridged claim and the `ofConstraints` transport of the receipt's
constraint list have the same satisfaction — chained through the sibling's
`constrainedRS` (`AccClaim.ofConstraints_satisfies_iff`). The roots may even differ: the
fold algebra never inspects them. -/
theorem ReceiptClaim.acc_satisfies_iff_ofConstraints {dom : FlatIx w ↪ F} {d : ℕ}
    (rc : ReceiptClaim w F) (rt rt' : Root) {f : FlatIx w → F} :
    AccClaim.Satisfies (reedSolomonCode dom d) (rc.acc rt) f
      ↔ AccClaim.Satisfies (reedSolomonCode dom d)
          (AccClaim.ofConstraints rt' rc.constraintList) f := by
  rw [rc.acc_satisfies_iff rt, AccClaim.ofConstraints_satisfies_iff,
    rc.mem_constrainedRS_iff_binds]

/-- **[OB3-d-fold], the closure.** Two receipt claims over ONE window, bridged to native
accumulated claims, fold at any challenge γ to ONE accumulated claim (`foldClaims` — a
well-formed `AccClaim` by construction) SATISFIED by the folded word
`flatten post₁ + γ • flatten post₂`: Loom's closure theorem `foldClaims_satisfies`
inherited verbatim (`hshare` is `acc_weights_shared`, i.e. `rfl`). The receipt chain is
thereby one accumulated object. δ-proximity soundness of the fold (the `(t−1)ℓ/|F|`
bound) is the shared `[ACC-sound]`/`[CRS-batch-sound]` residual — cited, not re-opened. -/
theorem receiptClaim_folds {C : Submodule F (FlatIx w → F)}
    (foldRoot : Root → F → Root → Root)
    (rc₁ rc₂ : ReceiptClaim w F) (rt₁ rt₂ : Root) (γ : F)
    (h₁ : flatten (F := F) w rc₁.post ∈ C)
    (h₂ : flatten (F := F) w rc₂.post ∈ C) :
    AccClaim.Satisfies C
      (foldClaims foldRoot (rc₁.acc rt₁) (rc₂.acc rt₂) γ)
      (flatten (F := F) w rc₁.post + γ • flatten (F := F) w rc₂.post) :=
  foldClaims_satisfies foldRoot γ (ReceiptClaim.acc_weights_shared rc₁ rc₂ rt₁ rt₂)
    (rc₁.acc_self rt₁ h₁) (rc₂.acc_self rt₂ h₂)

/-- The fold with code membership discharged: at full rate (`d = |FlatIx w|`) the RS code
is ⊤ (`reedSolomonCode_card_eq_top` — v0's "the word is the vector") and the two
flattenings are members for free. Premise inhabitation of `receiptClaim_folds`'s
hypotheses; the rate < 1 refinement is `[OB3-c-prox]`. -/
theorem receiptClaim_folds_fullRate (foldRoot : Root → F → Root → Root)
    (dom : FlatIx w ↪ F) (rc₁ rc₂ : ReceiptClaim w F) (rt₁ rt₂ : Root) (γ : F) :
    AccClaim.Satisfies (reedSolomonCode dom (Fintype.card (FlatIx w)))
      (foldClaims foldRoot (rc₁.acc rt₁) (rc₂.acc rt₂) γ)
      (flatten (F := F) w rc₁.post + γ • flatten (F := F) w rc₂.post) := by
  have htop := reedSolomonCode_card_eq_top (F := F) dom
  exact receiptClaim_folds foldRoot rc₁ rc₂ rt₁ rt₂ γ
    (by rw [htop]; exact Submodule.mem_top) (by rw [htop]; exact Submodule.mem_top)

/-- Satisfaction of the FOLDED receipt claim, characterized pointwise: the witness word is
the γ-combination of the two flattenings, coordinatewise — what the teeth below refute
for a ghost word. -/
theorem receiptFold_satisfies_iff {C : Submodule F (FlatIx w → F)}
    (foldRoot : Root → F → Root → Root)
    (rc₁ rc₂ : ReceiptClaim w F) (rt₁ rt₂ : Root) (γ : F) {f : FlatIx w → F} :
    AccClaim.Satisfies C (foldClaims foldRoot (rc₁.acc rt₁) (rc₂.acc rt₂) γ) f
      ↔ f ∈ C ∧ ∀ ix, f ix
          = flatten (F := F) w rc₁.post ix + γ * flatten (F := F) w rc₂.post ix := by
  unfold AccClaim.Satisfies
  refine and_congr_right fun _ => ?_
  rw [← forall_ixList (p := fun ix => f ix
    = flatten (F := F) w rc₁.post ix + γ * flatten (F := F) w rc₂.post ix)]
  refine forall_congr' fun k => ?_
  simp only [AccClaim.weights_apply, AccClaim.targets_apply, foldClaims_channel,
    ReceiptClaim.acc, dotWtL_apply, dotWt_evalConstraint]
  rw [← congrFun rc₁.binds ((ixList w).get k), ← congrFun rc₂.binds ((ixList w).get k)]

/-! ### Keystones for the fold (ATLAS: satisfiable + teeth, BUILT)

Over the file's tiny window `w₀` (one nullifier key, no cells) at `ZMod 5`: `FlatIx w₀`
has exactly 2 coordinates (presence bit + value), the domain embeds them at `{0,1} ⊂ F₅`,
and the full-rate RS code (`d = 2 = n`) makes code membership free — everything but the
fold algebra is concrete and computing. -/

private def dom₂ : FlatIx w₀ ↪ ZMod 5 :=
  ⟨fun ix => match ix with
    | Sum.inl _ => 3
    | Sum.inr (_, i) => (i.val : ZMod 5), by decide⟩

theorem card_FlatIx_w₀ : Fintype.card (FlatIx w₀) = 2 := by decide

/-- The honest receipt claim over the unspent state. -/
private def rcHonest : ReceiptClaim w₀ (ZMod 5) :=
  ⟨k₀, flatten (F := ZMod 5) w₀ k₀, rfl⟩

/-- The receipt claim over the spent state (`some 0` — the anti-ghost's target). -/
private def rcSpent : ReceiptClaim w₀ (ZMod 5) :=
  ⟨k₀spent, flatten (F := ZMod 5) w₀ k₀spent, rfl⟩

/-- **Satisfiable, computing**: two concrete receipt claims genuinely fold — for EVERY
challenge γ, the folded accumulated claim is satisfied by the folded word.
(`AccExample.trivialRoot` is the opaque recommitment schedule.) -/
theorem receipt_fold_satisfiable (γ : ZMod 5) :
    AccClaim.Satisfies (reedSolomonCode dom₂ 2)
      (foldClaims AccExample.trivialRoot (rcHonest.acc ()) (rcSpent.acc ()) γ)
      (flatten (F := ZMod 5) w₀ k₀ + γ • flatten (F := ZMod 5) w₀ k₀spent) := by
  have h := receiptClaim_folds_fullRate AccExample.trivialRoot dom₂ rcHonest rcSpent
    () () γ
  rwa [card_FlatIx_w₀] at h

/-- The presence-bit coordinate of the nullifier — where the ghost is caught. -/
private def pIx : FlatIx w₀ := Sum.inr (⟨UKey.nullifier 7, by decide⟩, 0)

/-- **Teeth, computing**: a GHOST fold — the second claim binds the SPENT state, but the
prover folds in the unspent word (pretending the nullifier is still fresh). Every
challenge γ ≠ 0 catches it: at the presence-bit coordinate the folded target reads
`0 + γ·1` while the ghost folded word reads `0 + γ·0`. (γ = 0 is the single blind
challenge — the fold that ignores the second claim; its probability 1/|F| is the
`[ACC-sound]` error shape, cf. `AccExample.fold_teeth`.) -/
theorem receipt_fold_teeth (γ : ZMod 5) (hγ : γ ≠ 0) :
    ¬ AccClaim.Satisfies (reedSolomonCode dom₂ 2)
      (foldClaims AccExample.trivialRoot (rcHonest.acc ()) (rcSpent.acc ()) γ)
      (flatten (F := ZMod 5) w₀ k₀ + γ • flatten (F := ZMod 5) w₀ k₀) := by
  intro h
  have hpt := ((receiptFold_satisfies_iff AccExample.trivialRoot rcHonest rcSpent
    () () γ).mp h).2 pIx
  have h0 : flatten (F := ZMod 5) w₀ k₀ pIx = 0 := by decide
  have h1 : flatten (F := ZMod 5) w₀ k₀spent pIx = 1 := by decide
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpt
  rw [show rcHonest.post = k₀ from rfl, show rcSpent.post = k₀spent from rfl] at hpt
  rw [h0, h1] at hpt
  exact hγ (by linear_combination -hpt)

/-- Sharpness of the tooth: at the single blind challenge γ = 0 the ghost fold IS
satisfied — the 1/|F| soundness-error event, exhibited. -/
example :
    AccClaim.Satisfies (reedSolomonCode dom₂ 2)
      (foldClaims AccExample.trivialRoot (rcHonest.acc ()) (rcSpent.acc ()) (0 : ZMod 5))
      (flatten (F := ZMod 5) w₀ k₀ + (0 : ZMod 5) • flatten (F := ZMod 5) w₀ k₀) := by
  have h := receipt_fold_satisfiable 0
  simpa using h

end Fold

/- ### The named residuals — PROSE, not vacuous Props

A `def : Prop := … True` would be the vacuous-obligation sin (see memory
`minidregg-audit-discipline`; the reflex to name an obligation as a `def : Prop` lands on
`True`, which any prover closes and which says nothing). Status after the fold section:

  [OB3-c-prox]  OPEN — the proximity refinement: at code rate < 1, a word δ-far (in
     `relDist`) from every codeword of an honest post-state FAILS the claim (the tooth
     beyond full rate, where membership is not free; equivalently, the code-membership
     hypotheses `h₁ h₂` of `receiptClaim_folds` become nontrivial). Needs Loom's RS
     proximity at rate < 1 threaded into an accept predicate. Realizer: WHIR/BCIKS
     proximity — the same carrier `Loom/ReedSolomon`'s `IsProximityGenerator` already
     names.

  [OB3-d-fold]  CLOSED at the closure level (this file, γ-fold section): the receipt
     claim IS a native accumulated claim (`ReceiptClaim.acc`, the same object as the
     `AccClaim.ofConstraints` transport — `acc_satisfies_iff_ofConstraints`), and two
     receipt claims over one window fold via Loom's `foldClaims` to ONE accumulated
     claim satisfied by the folded word (`receiptClaim_folds`, inheriting
     `foldClaims_satisfies` — the closure theorem REUSED, not re-derived), with
     computing keystones `receipt_fold_satisfiable` / `receipt_fold_teeth`. The receipt
     chain is one accumulated object. What remains is NOT re-opened here: δ-proximity
     soundness of the fold — that a δ-close-satisfiable folded claim certifies
     δ-close-satisfiable constituents except with probability `(t−1)ℓ/|F|` — is the
     SHARED `[ACC-sound]` residual of `Loom/Accumulator.lean` (whose exact-word kernel
     is already the theorem `card_batch_satisfying_le`, `[CRS-batch-sound]` in
     `Loom/ConstrainedCode.lean`).
-/

end Minidregg.Assurance
