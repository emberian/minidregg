/-
# `Assurance/ReceiptClaim.lean` — OB-3: the receipt Q as a native accumulated claim

THE KILL-CHECKPOINT (`docs/OB3-RECEIPT-ENCODING.md`). This bridge lives in `Assurance/`
by necessity: the import boundary forbids `Selvage` importing `Kernel` (and vice versa), and
OB-3 is exactly where a kernel object (the receipt word, `Kernel/Receipt.lean`) meets a
proof-system object (the code, `Selvage/ReedSolomon.lean`). `Assurance/` is unrestricted —
the apex layer — so it is the only lawful home.

**Checkpoint verdict (v0): PASS at the binding level.** The receipt word flattens to a
field vector; that vector determines the observed post-state (`flatten_faithful`), so
Selvage's evaluation constraint `û(α)=μ` binds Q — the receipt IS the accumulator's committed
word, no verifier-simulator. The anti-ghost tooth (`flatten_tamper_changes`) fires
concretely: a tampered post-state produces a different word. No candidate failure site
(OB-3 §2 — authority non-amp, nullifier non-membership, keyed-map sparsity) bit at this
level; the keyed map's `none`/`some 0` hole was closed upstream by presence bits.

**Honestly scoped.** The BINDING half (a/b/c-word) is proved, over the DEPLOYED finite
field (not char-zero — that would be the ℤ-for-BabyBear trap), with the cast side-condition
carried as an explicit range-restricted hypothesis `castInj` (OB-3 §2's named range
obligation — never assumed silently; a global `Int.cast` injectivity would be FALSE at a
finite field, i.e. vacuous, so it is range-restricted). The FOLD half (d) is now ALSO
closed at the CLOSURE level: a `ReceiptClaim` is a native Selvage accumulated claim
(`ReceiptClaim.acc`, provably the `AccClaim.ofConstraints` transport of its evaluation
constraints), and two receipt claims over one window fold via Selvage's `foldClaims` to ONE
accumulated claim satisfied by the folded word (`receiptClaim_folds`, inheriting the
closure theorem `foldClaims_satisfies`) — the δ-proximity soundness of that fold stays
the SHARED `[ACC-sound]`/`[CRS-batch-sound]` residual, cited, not re-opened. The
PROXIMITY half (c at rate < 1) — `[OB3-c-prox]` — is now CLOSED at the
EXACT-MEMBERSHIP level (Proximity section below): the rate<1 acceptance
`ReceiptClaim.proxAccepts` checks membership by Selvage's FRI/WHIR descent, and
`receiptClaim_proximity` bounds a δ-far receipt word's acceptance by `m·b·|F|^{m−1}`
(riding `proximity_sound`, REUSED). Below the quantization radius the fold-distance
premise is discharged UNCONDITIONALLY (`receiptClaim_proximity_subQuant`, zero residual
hypotheses; computing keystones — the spent-nullifier word is 1/5-far from the rate-1/2
code and laundered at EXACTLY one challenge in five). At macroscopic δ the same bound
rides the ONE standing RS proximity-gap hypothesis `hPG`
(`receiptClaim_proximity_ofProximityGenerator` — WHIR Thm 4.8 / BCIKS 2020/654, the
same hypothesis the whole rate<1 tree carries; cited, never assumed, NOT claimed).
-/
import Kernel.Receipt
import Selvage.ReedSolomon
import Selvage.Accumulator
import Selvage.Proximity

namespace Minidregg.Assurance

open Minidregg.Kernel Minidregg.Selvage

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
whole post-state" a fact about the WORD — so Selvage's `û(α)=μ` constraint binds Q. -/
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

The kernel's receipt Q becomes a Selvage `AccClaim`: the binding "word = flatten(post)" is
exactly a channel of per-coordinate EVALUATION constraints (`evalConstraint ix (word ix)`
— WHIR Def 4.5's in-domain `Z·eq` weight, one per flat coordinate), transported into
channel functionals by `dotWtL`. Two receipt claims over one window then fold by Selvage's
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
(`Selvage/ConstrainedCode.lean`): one evaluation constraint per flat coordinate, target the
claimed word there. -/
noncomputable def ReceiptClaim.constraintList (rc : ReceiptClaim w F) :
    List (LinearConstraint (FlatIx w) F) :=
  (ixList w).map fun ix => evalConstraint ix (rc.word ix)

/-- **The OB-3 bridge.** The receipt claim as a native Selvage accumulated claim:
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
flattening (and lies in the code) — OB-3 §1's Q, now read through Selvage's claim relation. -/
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
its rate < 1 refinement is the Proximity section below (`receiptClaim_proximity`). -/
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
`flatten post₁ + γ • flatten post₂`: Selvage's closure theorem `foldClaims_satisfies`
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
hypotheses; the rate < 1 refinement is the Proximity section below. -/
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

/-! ## [OB3-c-prox] — the rate<1 proximity refinement (the membership tooth)

At full rate the code is ⊤ and the membership conjunct of `AccClaim.Satisfies` is
FREE — the fold section above says so honestly, and its proximity content is zero.
This section is the refinement where that conjunct grows teeth: at rate < 1
(`deg 0 < |FlatIx w|`) membership is checked by Selvage's FRI/WHIR descent
(`proximityTest`, Selvage/Proximity.lean) instead of read off exactly, and the OB-3
checkpoint keeps its bite — a receipt word δ-FAR from the code passes the descent
on at most `m·b·|F|^{m−1}` of the `|F|^m` challenge tuples
(`receiptClaim_proximity`, riding `proximity_sound` — REUSED, not re-derived).
The claim's CHANNEL half (the binding `word = flatten post`) stays EXACT at claim
resolution, so a wrong-word ghost is rejected outright at EVERY challenge
(`proxAccepts_ne_reject`); its δ-relaxed evaluation form is the SHARED
`[ACC-sound]` residual, cited, not re-opened.

Two regimes, exactly as Selvage delivers `[PROX-fold-distance]`:
* sub-quantization `δ < 1/|level|`: `receiptClaim_proximity_subQuant` — the
  fold-distance premise discharged UNCONDITIONALLY by
  `foldDistancePreserving_of_lt_inv_card` (`b = 1`): zero residual hypotheses,
  and the keystones below compute it end-to-end.
* macroscopic `δ ∈ (0, 1−B)`: `receiptClaim_proximity_ofProximityGenerator` —
  rides the ONE standing RS proximity-gap hypothesis `hPG` (WHIR Thm 4.8 /
  BCIKS 2020/654), the SAME hypothesis Selvage/ReedSolomon.lean's Corollary 4.11
  and Selvage/Proximity.lean carry; a hypothesis, never an axiom, NOT claimed. -/

/-- The tower levels of a receipt descent: level 0 IS the window's flat spine
(definitionally — no transport, no coherence), the descent tail is arbitrary. -/
def rcLevels (w : Window) (tail : ℕ → Type) : ℕ → Type
  | 0 => FlatIx w
  | n + 1 => tail n

instance {w : Window} {tail : ℕ → Type} [∀ n, Fintype (tail n)] :
    ∀ n, Fintype (rcLevels w tail n)
  | 0 => inferInstanceAs (Fintype (FlatIx w))
  | n + 1 => inferInstanceAs (Fintype (tail n))

instance {w : Window} {tail : ℕ → Type} [∀ n, DecidableEq (tail n)] :
    ∀ n, DecidableEq (rcLevels w tail n)
  | 0 => inferInstanceAs (DecidableEq (FlatIx w))
  | n + 1 => inferInstanceAs (DecidableEq (tail n))

section Proximity

variable [DecidableEq F] {Root : Type} {w : Window} {tail : ℕ → Type} {m : ℕ}

omit [DecidableEq F] in
/-- Every level of a receipt tower is inhabited once the spine is: the squaring
projection carries a point down the descent. -/
theorem rcLevels_nonempty [h0 : Nonempty (FlatIx w)]
    (T : FoldingTower F (rcLevels w tail) m) :
    ∀ n, n ≤ m → Nonempty (rcLevels w tail n)
  | 0, _ => h0
  | n + 1, h => (rcLevels_nonempty T n (Nat.le_of_succ_le h)).map (T.data n h).sq

/-- The claim's channel constraints alone are the binding: `f` meets them iff
`f` IS the post-state's flattening (`acc_satisfies_iff` at `C = ⊤`, where the
membership conjunct is free). -/
theorem ReceiptClaim.channels_iff_binds (rc : ReceiptClaim w F) (rt : Root)
    (f : FlatIx w → F) :
    (∀ k, (rc.acc rt).weights k f = (rc.acc rt).targets k)
      ↔ f = flatten (F := F) w rc.post := by
  have h := rc.acc_satisfies_iff (C := (⊤ : Submodule F (FlatIx w → F))) rt (f := f)
  unfold AccClaim.Satisfies at h
  simpa using h

/-- **The rate<1 acceptance of a submitted receipt word**: `AccClaim.Satisfies`
with its membership conjunct replaced by the LDT descent — the word must pass
Selvage's `proximityTest` over the challenge tuple `r` (membership, now checked
probabilistically) and meet the claim's channels exactly (the binding). At full
rate the first conjunct is vacuous (`reedSolomonCode_card_eq_top`); at rate < 1
it is the real membership check. -/
def ReceiptClaim.proxAccepts (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    (f : FlatIx w → F) (r : Fin m → F) : Prop :=
  proximityTest T deg f (chalExt r) ∧
    ∀ k, (rc.acc rt).weights k f = (rc.acc rt).targets k

/-- Acceptance characterized: pass the descent AND be the honest flattening. -/
theorem ReceiptClaim.proxAccepts_iff (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    {f : FlatIx w → F} {r : Fin m → F} :
    rc.proxAccepts rt T deg f r
      ↔ proximityTest T deg f (chalExt r) ∧ f = flatten (F := F) w rc.post :=
  and_congr_right fun _ => rc.channels_iff_binds rt f

/-- **Completeness (the satisfiable side)**: an honestly-encoded receipt — one
whose flattening IS a rate<1 codeword — prox-accepts its own word at EVERY
challenge tuple (`proximity_complete` threaded through the claim). -/
theorem ReceiptClaim.proxAccepts_self (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
    (hmem : flatten (F := F) w rc.post ∈ reedSolomonCode (T.dom 0) (deg 0))
    (r : Fin m → F) :
    rc.proxAccepts rt T deg (flatten (F := F) w rc.post) r :=
  ⟨proximity_complete T hdeg hmem (chalExt r),
    (rc.channels_iff_binds rt _).mpr rfl⟩

/-- The binding prong stays exact at claim resolution: a word that is NOT the
claimed post-state's flattening fails the channels at EVERY challenge tuple —
rejected outright, no probability spent. (Its δ-relaxed evaluation form is the
shared `[ACC-sound]` residual — cited, not re-opened here.) -/
theorem ReceiptClaim.proxAccepts_ne_reject (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    {f : FlatIx w → F} (hne : f ≠ flatten (F := F) w rc.post) (r : Fin m → F) :
    ¬ rc.proxAccepts rt T deg f r :=
  fun h => hne ((rc.channels_iff_binds rt f).mp h.2)

variable [Fintype F]

/-- The accepting challenge tuples of a submitted word (classically measurable —
mirrors Selvage's `acceptSet`). -/
noncomputable def ReceiptClaim.proxAcceptSet (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    (f : FlatIx w → F) : Finset (Fin m → F) :=
  letI : DecidablePred fun r : Fin m → F => rc.proxAccepts rt T deg f r :=
    fun _ => Classical.propDecidable _
  Finset.univ.filter fun r => rc.proxAccepts rt T deg f r

theorem ReceiptClaim.mem_proxAcceptSet {rc : ReceiptClaim w F} {rt : Root}
    {T : FoldingTower F (rcLevels w tail) m} {deg : ℕ → ℕ}
    {f : FlatIx w → F} {r : Fin m → F} :
    r ∈ rc.proxAcceptSet rt T deg f ↔ rc.proxAccepts rt T deg f r := by
  simp [ReceiptClaim.proxAcceptSet]

/-- A ghost word — anything but the claimed flattening — has EMPTY acceptance:
the exact channel prong needs no randomness at all. -/
theorem ReceiptClaim.proxAcceptSet_eq_empty_of_ne (rc : ReceiptClaim w F)
    (rt : Root) (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    {f : FlatIx w → F} (hne : f ≠ flatten (F := F) w rc.post) :
    rc.proxAcceptSet rt T deg f = ∅ :=
  Finset.eq_empty_of_forall_notMem fun r hr =>
    rc.proxAccepts_ne_reject rt T deg hne r (ReceiptClaim.mem_proxAcceptSet.mp hr)

/-- Prox-acceptance refines the bare LDT acceptance — the event inclusion that
lets `proximity_sound` count the claim's acceptances. -/
theorem ReceiptClaim.proxAcceptSet_subset_acceptSet [∀ n, Fintype (tail n)]
    (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ) (f : FlatIx w → F) :
    rc.proxAcceptSet rt T deg f ⊆ acceptSet T deg f := fun _ hr =>
  mem_acceptSet.mpr (ReceiptClaim.mem_proxAcceptSet.mp hr).1

/-- **`[OB3-c-prox]`, counting form — the proximity tooth of the OB-3
checkpoint.** At rate < 1, a submitted receipt word δ-far from the code
prox-accepts on at most `m·b·|F|^{m−1}` of the `|F|^m` challenge tuples: the
acceptance event embeds in the bare LDT's and Selvage's `proximity_sound` (REUSED,
not re-derived) counts that. The per-round fold-distance premise `hfold` is the
same `[PROX-fold-distance]` interface Selvage delivers in two regimes — discharged
unconditionally below quantization (`…_subQuant`) and from the standing `hPG`
at macroscopic δ (`…_ofProximityGenerator`). -/
theorem receiptClaim_proximity [∀ n, Fintype (tail n)]
    (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    {f : FlatIx w → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (rc.proxAcceptSet rt T deg f).card ≤ m * (b * Fintype.card F ^ (m - 1)) :=
  le_trans
    (Finset.card_le_card (rc.proxAcceptSet_subset_acceptSet rt T deg f))
    (proximity_sound T deg hδ hfold hfar)

/-- Probability rendering: a δ-far receipt word prox-accepts with probability at
most `m·b/|F|` over the uniform challenge tuple — `proximity_sound_prob`'s
bound, inherited through the acceptance-event inclusion. -/
theorem receiptClaim_proximity_prob [∀ n, Fintype (tail n)]
    (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1)) δ b)
    {f : FlatIx w → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    ((rc.proxAcceptSet rt T deg f).card : ℝ) / (Fintype.card F : ℝ) ^ m
      ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
  refine le_trans ?_ (proximity_sound_prob T deg hδ hfold hfar)
  gcongr
  exact rc.proxAcceptSet_subset_acceptSet rt T deg f

/-- **`[OB3-c-prox]` CLOSED at exact-membership resolution — zero residual
hypotheses.** Below the quantization radius (`δ < 1/|level|` at every folded
level) the fold-distance premise is PROVED
(`foldDistancePreserving_of_lt_inv_card`, `b = 1`), so a δ-far receipt word
prox-accepts on at most `m·|F|^{m−1}` tuples (probability `m/|F|`) with NOTHING
left open. In this regime δ-far means exactly off-the-code; the macroscopic-δ
regime is the theorem below. -/
theorem receiptClaim_proximity_subQuant
    [∀ n, Fintype (tail n)] [Nonempty (FlatIx w)]
    (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδκ : ∀ j, j < m → δ < 1 / (Fintype.card (rcLevels w tail (j + 1)) : ℝ))
    {f : FlatIx w → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (rc.proxAcceptSet rt T deg f).card ≤ m * Fintype.card F ^ (m - 1) := by
  have h := receiptClaim_proximity rc rt T deg hδ0 (b := 1)
    (fun j hj => by
      haveI : Nonempty (rcLevels w tail (j + 1)) := rcLevels_nonempty T (j + 1) hj
      rw [hdeg j hj]
      exact foldDistancePreserving_of_lt_inv_card (T.data j hj) (deg (j + 1))
        hδ0 (hδκ j hj))
    hfar
  simpa using h

/-- **`[OB3-c-prox]` at macroscopic δ — on the ONE standing proximity-gap
hypothesis.** With PG(2) a proximity generator for each folded level's code —
WHIR Theorem 4.8 / BCIKS 2020/654, the SAME standing `hPG` carried by
Selvage/ReedSolomon.lean's Corollary 4.11 and Selvage/Proximity.lean's macroscopic
realizer; a HYPOTHESIS here, never an axiom, NOT claimed proved — a receipt
word δ-far from the rate<1 code prox-accepts on at most `m·b·|F|^{m−1}` tuples
for any `b ≥ err(δ)·|F|`. -/
theorem receiptClaim_proximity_ofProximityGenerator
    [∀ n, Fintype (tail n)] [∀ n, DecidableEq (tail n)] [Nonempty (FlatIx w)]
    (rc : ReceiptClaim w F) (rt : Root)
    (T : FoldingTower F (rcLevels w tail) m) (deg : ℕ → ℕ)
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1)) {B : ℝ} {err : ℝ → ℝ}
    (hPG : ∀ j, j < m → IsProximityGenerator (affineGenerator F)
      (reedSolomonCode (T.dom (j + 1)) (deg (j + 1))) B err)
    {δ : ℝ} (hδ0 : 0 < δ) (hδB : δ < 1 - B) {b : ℕ}
    (hb : err δ * (Fintype.card F : ℝ) ≤ (b : ℝ))
    {f : FlatIx w → F}
    (hfar : ¬ close δ (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (rc.proxAcceptSet rt T deg f).card ≤ m * (b * Fintype.card F ^ (m - 1)) :=
  receiptClaim_proximity rc rt T deg (le_of_lt hδ0)
    (fun j hj => by
      haveI : Nonempty (rcLevels w tail j) := rcLevels_nonempty T j (le_of_lt hj)
      rw [hdeg j hj]
      exact foldDistancePreserving_of_isProximityGenerator (T.data j hj)
        (deg (j + 1)) (hPG j hj) hδ0 hδB hb)
    hfar

end Proximity

/-! ### Keystones for the proximity tooth (ATLAS: satisfiable + teeth + premise
inhabitation — BUILT and computing)

A TWO-nullifier window: four flat coordinates, embedded at the negation-closed
`{1,2,3,4} ⊂ F₅` — the same domain as Selvage's `ProximityExample`, whose folded
level `{1,4}` (`dom1`) and degree schedule `2 → 1` are REUSED. Degree bound 2
over 4 points: rate 1/2 — the first site in this file where code membership is
NOT free.

* **satisfiable**: the honest (unspent) receipt word is the zero word — a
  genuine rate-1/2 codeword — and prox-accepts at EVERY challenge.
* **teeth**: SPENDING nullifier 7 flips its presence bit; the spent receipt
  word is a spike, provably 1/5-FAR from the code, and the descent catches it —
  acceptance computed EXACTLY as `{![4]}`: one laundering challenge in five,
  the `m·b/|F|` bound attained with equality, zero residual hypotheses.
* **premise inhabitation**: the rate-1/2 code holds a nonzero codeword and
  misses the spent word — a PROPER constraint, unlike the full-rate ⊤. -/

section ProxKeystone

open Polynomial

/-- Two nullifier keys: `FlatIx` has four coordinates (2 keys × presence/value). -/
private def w₄ : Window := ⟨∅, {UKey.nullifier 7, UKey.nullifier 8}⟩

theorem card_FlatIx_w₄ : Fintype.card (FlatIx w₄) = 4 := by decide

/-- Nullifier 7's presence-bit coordinate — where the tamper lands. -/
private def spikeIx : FlatIx w₄ := Sum.inr (⟨UKey.nullifier 7, by decide⟩, 0)

instance : Nonempty (FlatIx w₄) := ⟨spikeIx⟩

private abbrev tail₂ : ℕ → Type := fun _ => Fin 2

/-- The spine embedded at `{1,2,3,4}`: nullifier 7's pair at `{1,2}`, nullifier
8's at `{4,3}` — negation is key-swap. -/
private def dom₄ : FlatIx w₄ ↪ ZMod 5 :=
  ⟨fun ix => match ix with
    | Sum.inl _ => 0
    | Sum.inr (u, i) =>
        if u.1 = UKey.nullifier 7 then 1 + (i.val : ZMod 5)
        else 4 - (i.val : ZMod 5),
   by decide⟩

/-- Folding structure on the spine: negation swaps the key (same bit), squaring
projects onto the bit — the folded level is Selvage `ProximityExample`'s `{1,4}`
(`dom1`), reused. Every law is checked by `decide`. -/
private def data₄ : FoldingData (ZMod 5) dom₄ ProximityExample.dom1 where
  neg := fun ix => match ix with
    | Sum.inl c => Sum.inl c
    | Sum.inr (u, i) =>
        Sum.inr (if u.1 = UKey.nullifier 7
          then ⟨UKey.nullifier 8, by decide⟩ else ⟨UKey.nullifier 7, by decide⟩, i)
  dom_neg := by decide
  sq := fun ix => match ix with
    | Sum.inl _ => 0
    | Sum.inr (_, i) => i
  domSq_sq := by decide
  sec := fun k => Sum.inr (⟨UKey.nullifier 7, by decide⟩, k)
  sq_sec := by decide
  dom_ne_zero := by decide
  two_ne := by decide

/-- The receipt tower: the window's spine, then `ProximityExample`'s folded
domain (deeper levels idle at `Fin 2`; the descent stops at `m = 1`). -/
private def T₄ : FoldingTower (ZMod 5) (rcLevels w₄ tail₂) 1 where
  dom := fun n => match n with
    | 0 => dom₄
    | _ + 1 => ProximityExample.dom1
  data := fun j hj => match j, hj with
    | 0, _ => data₄
    | _ + 1, hj => absurd hj (by omega)

/-- The honest (unspent) receipt word is the ZERO word — in the rate-1/2 code. -/
theorem honest_word_mem :
    flatten (F := ZMod 5) w₄ k₀ ∈ reedSolomonCode dom₄ 2 := by
  have h : flatten (F := ZMod 5) w₄ k₀ = 0 := by decide
  rw [h]
  exact Submodule.zero_mem _

private def rcHonest₄ : ReceiptClaim w₄ (ZMod 5) :=
  ⟨k₀, flatten (F := ZMod 5) w₄ k₀, rfl⟩

private def rcSpent₄ : ReceiptClaim w₄ (ZMod 5) :=
  ⟨k₀spent, flatten (F := ZMod 5) w₄ k₀spent, rfl⟩

/-- **Satisfiable, computing**: the honest receipt prox-accepts its own word at
EVERY challenge — completeness fires through the claim at rate 1/2. -/
theorem receipt_prox_satisfiable (r : Fin 1 → ZMod 5) :
    rcHonest₄.proxAccepts () T₄ ProximityExample.degSched
      (flatten (F := ZMod 5) w₄ k₀) r :=
  rcHonest₄.proxAccepts_self () T₄ ProximityExample.degSched
    ProximityExample.degSched_halving honest_word_mem r

/-- The honest word is close to the code (to itself) at any radius ≥ 0. -/
example : close 0 (reedSolomonCode dom₄ 2) (flatten (F := ZMod 5) w₄ k₀) :=
  close_of_mem honest_word_mem le_rfl

private def zIx₁ : FlatIx w₄ := Sum.inr (⟨UKey.nullifier 7, by decide⟩, 1)
private def zIx₂ : FlatIx w₄ := Sum.inr (⟨UKey.nullifier 8, by decide⟩, 0)

/-- The spent word is OFF the rate-1/2 code: a degree-<2 polynomial matching it
would vanish at two of the four points (hence be zero, by root counting —
Selvage's `card_agreeSet_lt_of_ne`, reused) yet read 1 at the spiked presence
bit. The presence bit pushes the word off the code. -/
theorem spentWord_notMem :
    flatten (F := ZMod 5) w₄ k₀spent ∉ reedSolomonCode dom₄ 2 := by
  intro hmem
  obtain ⟨p, hdeg, hp⟩ := mem_reedSolomonCode_iff.mp hmem
  have hpne : p ≠ 0 := by
    intro h0
    have h1 := hp spikeIx
    rw [h0, eval_zero] at h1
    exact absurd h1 (by decide)
  have hcard := card_agreeSet_lt_of_ne dom₄ (d := 2) hdeg
    (q := 0) (by rw [degree_zero]; exact WithBot.bot_lt_coe _) hpne
  have hsub : ({zIx₁, zIx₂} : Finset (FlatIx w₄))
      ⊆ Finset.univ.filter fun i =>
          p.eval (dom₄ i) = (0 : Polynomial (ZMod 5)).eval (dom₄ i) := by
    intro i hi
    rw [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by rw [eval_zero, ← hp zIx₁]; decide⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by rw [eval_zero, ← hp zIx₂]; decide⟩
  have hpair : ({zIx₁, zIx₂} : Finset (FlatIx w₄)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by decide), Finset.card_singleton]
  have h2 := Finset.card_le_card hsub
  rw [hpair] at h2
  omega

/-- **The spent word is 1/5-FAR from the rate-1/2 code**: any codeword within
1/5 would sit inside the 1/4 quantization floor, hence equal it — but the spent
word is no codeword at all. -/
theorem spentWord_far :
    ¬ close (1 / 5 : ℝ) (reedSolomonCode dom₄ 2)
      (flatten (F := ZMod 5) w₄ k₀spent) := by
  rintro ⟨u, huC, hrel⟩
  have hne : flatten (F := ZMod 5) w₄ k₀spent ≠ u := fun h =>
    spentWord_notMem (h ▸ huC)
  have hfloor := one_div_card_le_relDist (F := ZMod 5) hne
  rw [card_FlatIx_w₄] at hfloor
  norm_num at hfloor
  linarith

/-- Premise inhabitation: rate<1 membership has CONTENT — the code holds a
nonzero codeword (the evaluations of `X`) and misses the spent word. Compare
the full-rate fold section, where the code is ⊤ and membership is free. -/
theorem rate_half_code_proper :
    ((dom₄ : FlatIx w₄ → ZMod 5) ∈ reedSolomonCode dom₄ 2)
      ∧ flatten (F := ZMod 5) w₄ k₀spent ∉ reedSolomonCode dom₄ 2 :=
  ⟨mem_reedSolomonCode_iff.mpr ⟨X, by rw [degree_X]; decide, fun i => by simp⟩,
    spentWord_notMem⟩

/-- **Teeth, zero residual hypotheses**: the far spent word prox-accepts on at
most ONE of the five challenge tuples — `receiptClaim_proximity_subQuant` with
every premise discharged (fold-distance by the PROVED sub-quantization
realizer; nothing assumed). -/
theorem receipt_prox_teeth :
    (rcSpent₄.proxAcceptSet () T₄ ProximityExample.degSched
      (flatten (F := ZMod 5) w₄ k₀spent)).card ≤ 1 := by
  have h := receiptClaim_proximity_subQuant rcSpent₄ () T₄
    ProximityExample.degSched ProximityExample.degSched_halving
    (δ := (1 / 5 : ℝ)) (by norm_num)
    (fun j hj => by
      have h0 : j = 0 := by omega
      subst h0
      show (1 / 5 : ℝ) < 1 / (Fintype.card (rcLevels w₄ tail₂ 1) : ℝ)
      rw [(by decide : Fintype.card (rcLevels w₄ tail₂ 1) = 2)]
      norm_num)
    spentWord_far
  simpa using h

/-- The catch computed EXACTLY: the descent accepts the spent word iff the
challenge is the single laundering `α = 4` — the spike folds to `(3+3α, 0)`,
constant only there. -/
theorem spent_accept_iff (α : ZMod 5) :
    proximityTest T₄ ProximityExample.degSched
      (flatten (F := ZMod 5) w₄ k₀spent) (chalExt ![α]) ↔ α = 4 := by
  show fold data₄ (flatten (F := ZMod 5) w₄ k₀spent) α
      ∈ reedSolomonCode ProximityExample.dom1 1 ↔ α = 4
  rw [mem_reedSolomonCode_one_iff]
  revert α
  decide

/-- The tooth FIRES: at the good challenge 1 the far spent word is REJECTED. -/
example : ¬ rcSpent₄.proxAccepts () T₄ ProximityExample.degSched
    (flatten (F := ZMod 5) w₄ k₀spent) ![1] := fun h =>
  absurd ((spent_accept_iff 1).mp h.1) (by decide)

/-- The acceptance set IS `{![4]}` — `receipt_prox_teeth`'s bound is attained
with equality: exactly the `m·b/|F| = 1/5` laundering event (cf. the fold
section's γ = 0 blind challenge). -/
theorem proxAcceptSet_spent :
    rcSpent₄.proxAcceptSet () T₄ ProximityExample.degSched
      (flatten (F := ZMod 5) w₄ k₀spent) = {![4]} := by
  ext r
  rw [ReceiptClaim.mem_proxAcceptSet, Finset.mem_singleton,
    ReceiptClaim.proxAccepts_iff]
  have hr : r = ![r 0] := funext fun j => by fin_cases j; rfl
  constructor
  · rintro ⟨htest, -⟩
    rw [hr] at htest ⊢
    rw [(spent_accept_iff (r 0)).mp htest]
  · rintro rfl
    exact ⟨(spent_accept_iff 4).mpr rfl, rfl⟩

/-- The bound is attained: acceptance count exactly 1. -/
example : (rcSpent₄.proxAcceptSet () T₄ ProximityExample.degSched
    (flatten (F := ZMod 5) w₄ k₀spent)).card = 1 := by
  rw [proxAcceptSet_spent, Finset.card_singleton]

/-- Sharpness: at `α = 4` the far word IS laundered through the descent — the
soundness error is a genuine phenomenon, not slack in the bound. -/
example : rcSpent₄.proxAccepts () T₄ ProximityExample.degSched
    (flatten (F := ZMod 5) w₄ k₀spent) ![4] :=
  (rcSpent₄.proxAccepts_iff () T₄ ProximityExample.degSched).mpr
    ⟨(spent_accept_iff 4).mpr rfl, rfl⟩

/-- The other prong: the UNSPENT word submitted against the claim binding the
SPENT state fails the exact channels at EVERY challenge — the ghost needs no
probability at all. -/
example (r : Fin 1 → ZMod 5) :
    ¬ rcSpent₄.proxAccepts () T₄ ProximityExample.degSched
      (flatten (F := ZMod 5) w₄ k₀) r :=
  rcSpent₄.proxAccepts_ne_reject () T₄ ProximityExample.degSched (by decide) r

end ProxKeystone

/- ### The named residuals — PROSE, not vacuous Props

A `def : Prop := … True` would be the vacuous-obligation sin (see memory
`minidregg-audit-discipline`; the reflex to name an obligation as a `def : Prop` lands on
`True`, which any prover closes and which says nothing). Status after the fold section:

  [OB3-c-prox]  CLOSED at the EXACT-MEMBERSHIP level (this file, Proximity section) —
     NOT still fully open. The rate<1 accept predicate exists
     (`ReceiptClaim.proxAccepts`: Selvage's `proximityTest` for membership + the claim's
     exact channels for binding), and a receipt word δ-far from the rate<1 code
     prox-accepts on at most `m·b·|F|^{m−1}` challenge tuples
     (`receiptClaim_proximity`, probability form `receiptClaim_proximity_prob`) —
     riding Selvage's `proximity_sound`, REUSED, not re-derived. Regime split, exactly
     as Selvage delivers `[PROX-fold-distance]`:
       • sub-quantization δ < 1/|level|: UNCONDITIONAL
         (`receiptClaim_proximity_subQuant`, `b = 1` via
         `foldDistancePreserving_of_lt_inv_card`) — zero residual hypotheses, and
         the keystones COMPUTE it: the spent-nullifier word (presence bit pushes it
         off the rate-1/2 code) is 1/5-far (`spentWord_far`), caught at four of five
         challenges with acceptance set EXACTLY `{![4]}` (`proxAcceptSet_spent`) —
         bound attained with equality.
       • macroscopic δ ∈ (0, 1−B): rides the ONE standing RS proximity-gap
         hypothesis `hPG` (`receiptClaim_proximity_ofProximityGenerator` — WHIR
         Thm 4.8 / BCIKS 2020/654), the SAME hypothesis Selvage/ReedSolomon.lean's
         Corollary 4.11 and Selvage/Proximity.lean carry. Cited, not re-opened, NOT
         claimed proved; its UD-regime instantiation stays the ladder's next rung
         (docs/LOOM-RECOMPOSITION.md §5).
     What is NOT covered here, stated plainly: the channel half stays EXACT at claim
     resolution (a wrong word is rejected outright, `proxAccepts_ne_reject`); its
     δ-relaxed evaluation form — random-point channel checks — is the SHARED
     `[ACC-sound]` residual below, and the oracle/Merkle query phase is
     `[DEC-open]`-adjacent (Selvage/Proximity.lean's honest scope limits apply
     verbatim).

  [OB3-d-fold]  CLOSED at the closure level (this file, γ-fold section): the receipt
     claim IS a native accumulated claim (`ReceiptClaim.acc`, the same object as the
     `AccClaim.ofConstraints` transport — `acc_satisfies_iff_ofConstraints`), and two
     receipt claims over one window fold via Selvage's `foldClaims` to ONE accumulated
     claim satisfied by the folded word (`receiptClaim_folds`, inheriting
     `foldClaims_satisfies` — the closure theorem REUSED, not re-derived), with
     computing keystones `receipt_fold_satisfiable` / `receipt_fold_teeth`. The receipt
     chain is one accumulated object. What remains is NOT re-opened here: δ-proximity
     soundness of the fold — that a δ-close-satisfiable folded claim certifies
     δ-close-satisfiable constituents except with probability `(t−1)ℓ/|F|` — is the
     SHARED `[ACC-sound]` residual of `Selvage/Accumulator.lean` (whose exact-word kernel
     is already the theorem `card_batch_satisfying_le`, `[CRS-batch-sound]` in
     `Selvage/ConstrainedCode.lean`).
-/

end Minidregg.Assurance
