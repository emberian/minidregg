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
finite field, i.e. vacuous, so it is range-restricted). The PROXIMITY half (c at rate < 1)
and the FOLD half (d — two claims fold to one CRS claim) need the accumulator γ-fold
machinery not yet in the tree; they are `[OB3-c-prox]`/`[OB3-d-fold]`, stated with shape,
never `True`-stubbed, and NOT claimed as landed keystones.
-/
import Kernel.Receipt
import Loom.ReedSolomon

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
plus the evaluation-binding target `μ` (here the word itself; the digest/eval form is the
γ-fold layer's concern, `[OB3-d-fold]`). -/
structure ReceiptClaim (w : Window) (F : Type) [Field F] [DecidableEq F] where
  post : KernelState
  word : FlatIx w → F
  binds : word = flatten (F := F) w post

/- ### The two named residuals — PROSE, not vacuous Props

A `def : Prop := … True` would be the vacuous-obligation sin (caught twice tonight — see
memory `minidregg-audit-discipline`; the reflex to name an obligation as a `def : Prop`
lands on `True`, which any prover closes and which says nothing). Both become real theorems
when the accumulator γ-fold machinery lands; recorded here with their intended shape:

  [OB3-c-prox]  the proximity refinement — at code rate < 1, a word δ-far (in `relDist`)
     from every codeword of an honest post-state FAILS the claim (the tooth beyond full
     rate, where membership is not free). Needs Loom's RS proximity at rate < 1 threaded
     into an accept predicate. Realizer: WHIR/BCIKS proximity — the same carrier
     `Loom/ReedSolomon`'s `IsProximityGenerator` already names.

  [OB3-d-fold]  the fold — two `ReceiptClaim`s over one window fold to ONE CRS claim
     (closure under the γ-fold rule, LOOM §6), so the chain is one accumulated object and
     the seam `pre-root = prev.post-root` is a native accumulated equality. Needs the
     γ-fold construction. Realizer: WARP/WHIR Constr. 5.5 / 7.4.
-/

end Minidregg.Assurance
