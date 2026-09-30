/-
# Theory.Conservation -- conservation is membership in a kernel

DATAMODEL.md §3.1 ("Value"), §3.9, §4.1.  For a namespace whose values form an
additive group `G`, a transition's *delta* is `post − pre` read with absence as
`0`.  Conservation is not a property of one operation at a time: it is the
statement that the delta lies in the kernel of the per-asset sum

  `assetSum : (Acc × Asset →₀ G) →+ (Asset →₀ G) := Finsupp.mapDomain Prod.snd`.

A *posting* `single (src, a) (−m) + single (dst, a) m` lies in that kernel, and
the postings generate it (`postings_generate_kernel`, the augmentation-kernel
fact for a free abelian group, proved here directly).  "Every admitted
operation is a posting" and "admitted transitions conserve" are therefore one
fact about a subgroup.

The store is an abstract parameter: a *value view* `S → (K →₀ G)` is any
reading of a store's group-valued namespace with absence as `0`.  The concrete
views of the existing `Book` and the declared-effect `FieldStore` live in
`Theory.ConservationBridge`; the promoted `Theory.Store` (lane A1) supplies one
more such view without changing anything here.

This module imports Mathlib only.
-/
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

namespace Minidregg.Theory.Conservation

open Finsupp

set_option autoImplicit false

/-! ## The delta of a transition -/

section Delta

variable {S K G : Type*} [AddCommGroup G]

/-- The difference homomorphism on value vectors: `(pre, post) ↦ post − pre`. -/
noncomputable def differenceHom : (K →₀ G) × (K →₀ G) →+ (K →₀ G) :=
  AddMonoidHom.snd _ _ - AddMonoidHom.fst _ _

/-- The delta of a transition `pre → post` under a value view.  It is the
difference homomorphism evaluated at the two readings. -/
noncomputable def delta (value : S → K →₀ G) (pre post : S) : K →₀ G :=
  differenceHom (value pre, value post)

theorem delta_eq (value : S → K →₀ G) (pre post : S) :
    delta value pre post = value post - value pre := rfl

@[simp] theorem delta_apply (value : S → K →₀ G) (pre post : S) (k : K) :
    delta value pre post k = value post k - value pre k := by
  simp [delta_eq]

@[simp] theorem delta_self (value : S → K →₀ G) (s : S) : delta value s s = 0 := by
  simp [delta_eq]

/-- The delta of a composite transition is the sum of the deltas of its parts
(the cocycle law of the difference homomorphism). -/
theorem delta_add (value : S → K →₀ G) (s₁ s₂ s₃ : S) :
    delta value s₁ s₂ + delta value s₂ s₃ = delta value s₁ s₃ := by
  simp only [delta_eq]
  abel

/-- A transition that adds a fixed vector to the reading has exactly that delta. -/
theorem delta_of_value_eq (value : S → K →₀ G) {pre post : S} {v : K →₀ G}
    (h : value post = value pre + v) : delta value pre post = v := by
  rw [delta_eq, h]
  abel

/-- The delta along a chain of states is the sum of the step deltas. -/
theorem delta_chain (value : S → K →₀ G) :
    ∀ (s : S) (rest : List S),
      delta value s (rest.getLastD s) =
        ((s :: rest).zip rest |>.map fun p => delta value p.1 p.2).sum
  | s, [] => by simp
  | s, t :: rest => by
      have ih := delta_chain value t rest
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      rw [← ih, delta_add]
      cases rest with
      | nil => simp
      | cons _ _ => simp [List.getLastD]

end Delta

/-! ## The per-asset sum and the conservation predicate -/

section AssetSum

variable {Acc Asset G : Type*} [AddCommGroup G]

/-- The per-asset sum `Σ`: forget the account coordinate. -/
noncomputable def assetSum : (Acc × Asset →₀ G) →+ (Asset →₀ G) :=
  Finsupp.mapDomain.addMonoidHom Prod.snd

@[simp] theorem assetSum_single (x : Acc × Asset) (m : G) :
    assetSum (single x m) = single x.2 m := by
  simp [assetSum]

/-- A value vector conserves when its per-asset sum vanishes. -/
def Conserves (d : Acc × Asset →₀ G) : Prop := assetSum d = 0

/-- A transition conserves when its delta does. -/
def ConservesBetween {S : Type*} (value : S → Acc × Asset →₀ G) (pre post : S) : Prop :=
  Conserves (delta value pre post)

theorem conserves_iff_mem_ker (d : Acc × Asset →₀ G) :
    Conserves d ↔ d ∈ (assetSum : (Acc × Asset →₀ G) →+ (Asset →₀ G)).ker :=
  (AddMonoidHom.mem_ker).symm

/-- **Conservation is kernel membership of the delta.** -/
theorem conserves_iff_delta_mem_ker {S : Type*} (value : S → Acc × Asset →₀ G)
    (pre post : S) :
    ConservesBetween value pre post ↔
      delta value pre post ∈ (assetSum : (Acc × Asset →₀ G) →+ (Asset →₀ G)).ker :=
  conserves_iff_mem_ker _

/-- Conserving transitions compose: the kernel is closed under the cocycle. -/
theorem ConservesBetween.trans {S : Type*} {value : S → Acc × Asset →₀ G}
    {s₁ s₂ s₃ : S} (h₁ : ConservesBetween value s₁ s₂)
    (h₂ : ConservesBetween value s₂ s₃) : ConservesBetween value s₁ s₃ := by
  unfold ConservesBetween Conserves at *
  rw [← delta_add, map_add, h₁, h₂, add_zero]

/-! ## Postings -/

/-- One debit and one equal credit of asset `a`. -/
noncomputable def posting (src dst : Acc) (a : Asset) (m : G) : Acc × Asset →₀ G :=
  single (src, a) (-m) + single (dst, a) m

theorem posting_apply [DecidableEq Acc] [DecidableEq Asset]
    (src dst : Acc) (a : Asset) (m : G) (k : Acc × Asset) :
    posting src dst a m k =
      (if (src, a) = k then -m else 0) + (if (dst, a) = k then m else 0) := by
  simp only [posting, Finsupp.add_apply, single_apply]

/-- Every posting lies in the kernel of the per-asset sum. -/
theorem posting_mem_ker (src dst : Acc) (a : Asset) (m : G) :
    posting src dst a m ∈ (assetSum : (Acc × Asset →₀ G) →+ (Asset →₀ G)).ker := by
  rw [AddMonoidHom.mem_ker, posting, map_add, assetSum_single, assetSum_single,
    single_neg, neg_add_cancel]

/-- The set of all postings. -/
def postings : Set (Acc × Asset →₀ G) :=
  Set.range fun p : Acc × Acc × Asset × G => posting p.1 p.2.1 p.2.2.1 p.2.2.2

/-- With any base account `b`, a vector in the kernel is the sum, over its
support, of postings from `b` to each coordinate's account. -/
theorem eq_sum_postings_of_mem_ker (b : Acc) (v : Acc × Asset →₀ G)
    (hv : v ∈ (assetSum : (Acc × Asset →₀ G) →+ (Asset →₀ G)).ker) :
    v = v.sum fun x m => posting b x.1 x.2 m := by
  classical
  rw [AddMonoidHom.mem_ker] at hv
  have split : (v.sum fun x m => posting b x.1 x.2 m) =
      -(v.sum fun x m => single (b, x.2) m) + v.sum fun x m => single x m := by
    rw [← Finsupp.sum_neg, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun x _ => ?_
    simp [posting, single_neg]
  have base : (v.sum fun x m => single (b, x.2) m) = 0 := by
    have comp : (v.sum fun x m => single (b, x.2) m) =
        mapDomain (fun a : Asset => (b, a)) (mapDomain Prod.snd v) := by
      rw [← mapDomain_comp]
      rfl
    rw [comp]
    change mapDomain _ (assetSum v) = 0
    rw [hv, mapDomain_zero]
  rw [split, base, neg_zero, zero_add, Finsupp.sum_single]

/-- **The postings generate the kernel of the per-asset sum** (the augmentation
kernel).  The closure is over all postings; `eq_sum_postings_of_mem_ker` gives
the explicit finite decomposition. -/
theorem postings_generate_kernel :
    AddSubgroup.closure (postings : Set (Acc × Asset →₀ G)) =
      (assetSum : (Acc × Asset →₀ G) →+ (Asset →₀ G)).ker := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    exact posting_mem_ker _ _ _ _
  · intro v hv
    rcases isEmpty_or_nonempty Acc with hAcc | ⟨⟨b⟩⟩
    · have : v = 0 := Subsingleton.elim _ _
      rw [this]
      exact zero_mem _
    · rw [eq_sum_postings_of_mem_ker b v hv]
      exact sum_mem fun x _ =>
        AddSubgroup.subset_closure ⟨(b, x.1, x.2, v x), rfl⟩

/-- The list form of §3.9's sketch: every kernel vector is a finite sum of
postings. -/
theorem exists_postings_list_of_mem_ker (v : Acc × Asset →₀ G)
    (hv : v ∈ (assetSum : (Acc × Asset →₀ G) →+ (Asset →₀ G)).ker) :
    ∃ ps : List (Acc × Acc × Asset × G),
      v = (ps.map fun p => posting p.1 p.2.1 p.2.2.1 p.2.2.2).sum := by
  classical
  rcases isEmpty_or_nonempty Acc with hAcc | ⟨⟨b⟩⟩
  · exact ⟨[], Subsingleton.elim _ _⟩
  · refine ⟨v.support.toList.map fun x => (b, x.1, x.2, v x), ?_⟩
    conv_lhs => rw [eq_sum_postings_of_mem_ker b v hv]
    rw [List.map_map, Finsupp.sum, ← Finset.sum_map_toList]
    rfl

/-! ## Restricting the sum to a finite account set -/

/-- `v` touches only accounts in `A`. -/
def SupportedIn (A : Finset Acc) (v : Acc × Asset →₀ G) : Prop :=
  ∀ x ∈ v.support, x.1 ∈ A

theorem supportedIn_zero (A : Finset Acc) : SupportedIn A (0 : Acc × Asset →₀ G) := by
  intro x hx
  simp at hx

theorem SupportedIn.add [DecidableEq Acc] [DecidableEq Asset] {A : Finset Acc}
    {v w : Acc × Asset →₀ G} (hv : SupportedIn A v) (hw : SupportedIn A w) :
    SupportedIn A (v + w) := by
  intro x hx
  rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h
  · exact hv x h
  · exact hw x h

theorem supportedIn_list_sum [DecidableEq Acc] [DecidableEq Asset] {A : Finset Acc}
    (vs : List (Acc × Asset →₀ G)) (h : ∀ v ∈ vs, SupportedIn A v) :
    SupportedIn A vs.sum := by
  induction vs with
  | nil => exact supportedIn_zero A
  | cons v rest ih =>
      rw [List.sum_cons]
      exact (h v (by simp)).add (ih fun w hw => h w (by simp [hw]))

theorem supportedIn_single {A : Finset Acc} {x : Acc × Asset} (m : G) (hx : x.1 ∈ A) :
    SupportedIn A (single x m) := by
  intro y hy
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hy)]
  exact hx

theorem supportedIn_posting [DecidableEq Acc] [DecidableEq Asset] {A : Finset Acc}
    {src dst : Acc} (a : Asset) (m : G) (hs : src ∈ A) (hd : dst ∈ A) :
    SupportedIn A (posting src dst a m) :=
  (supportedIn_single _ hs).add (supportedIn_single _ hd)

/-- On a vector touching only accounts in `A`, the per-asset sum is the finite
sum over `A`.  This is the bridge to ledgers that total over a registered
account set rather than over the support. -/
theorem sum_accounts_eq_assetSum [DecidableEq Asset] (A : Finset Acc)
    (v : Acc × Asset →₀ G) (hv : SupportedIn A v) (a : Asset) :
    ∑ acc ∈ A, v (acc, a) = assetSum v a := by
  classical
  set T := v.support.image Prod.snd
  have sub : v.support ⊆ A ×ˢ T := by
    intro x hx
    exact Finset.mem_product.mpr ⟨hv x hx, Finset.mem_image_of_mem _ hx⟩
  have expand : assetSum v a = ∑ x ∈ A ×ˢ T, single x.2 (v x) a := by
    change (mapDomain Prod.snd v) a = _
    rw [mapDomain, Finsupp.sum_apply]
    exact Finsupp.sum_of_support_subset v sub _ (fun _ _ => by simp)
  rw [expand, Finset.sum_product]
  refine Finset.sum_congr rfl fun acc _ => ?_
  simp only [single_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · have : (acc, a) ∉ v.support := fun hx => h (Finset.mem_image_of_mem _ hx)
    exact Finsupp.notMem_support_iff.mp this

/-- A conserving vector touching only `A` has zero finite total over `A`, per asset. -/
theorem Conserves.sum_accounts_eq_zero [DecidableEq Asset] {A : Finset Acc}
    {v : Acc × Asset →₀ G} (hc : Conserves v) (hv : SupportedIn A v) (a : Asset) :
    ∑ acc ∈ A, v (acc, a) = 0 := by
  rw [sum_accounts_eq_assetSum A v hv, hc, Finsupp.zero_apply]

end AssetSum

/-! ## Per-grant bounds compose (§3.7)

`Scope.maxDelta` (B3) bounds the magnitude of each admitted move.  The delta of
a patch made of admitted moves is then bounded coordinatewise by `maxDelta`
times the number of moves. -/

section Bounds

variable {Acc Asset G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

theorem abs_posting_apply_le (src dst : Acc) (a : Asset) (m : G) (k : Acc × Asset) :
    |posting src dst a m k| ≤ |m| := by
  classical
  rw [posting_apply]
  split_ifs <;> simp

/-- A move `(src, dst, a, m)` as a posting. -/
noncomputable def movePosting (mv : Acc × Acc × Asset × G) : Acc × Asset →₀ G :=
  posting mv.1 mv.2.1 mv.2.2.1 mv.2.2.2

/-- **Bounds compose.** If every move has magnitude at most `maxDelta`, the
delta of the patch has magnitude at most `moves.length • maxDelta` at every key. -/
theorem abs_moves_sum_apply_le (maxDelta : G) (moves : List (Acc × Acc × Asset × G))
    (bounded : ∀ mv ∈ moves, |mv.2.2.2| ≤ maxDelta) (k : Acc × Asset) :
    |(moves.map movePosting).sum k| ≤ moves.length • maxDelta := by
  induction moves with
  | nil => simp
  | cons mv rest ih =>
      rw [List.map_cons, List.sum_cons, Finsupp.add_apply, List.length_cons, succ_nsmul']
      calc |movePosting mv k + (rest.map movePosting).sum k|
          ≤ |movePosting mv k| + |(rest.map movePosting).sum k| := abs_add_le _ _
        _ ≤ maxDelta + rest.length • maxDelta :=
            add_le_add ((abs_posting_apply_le _ _ _ _ _).trans (bounded mv (by simp)))
              (ih fun w hw => bounded w (by simp [hw]))

omit [LinearOrder G] [IsOrderedAddMonoid G] in
/-- Every move vector list sums into the kernel. -/
theorem moves_sum_mem_ker (moves : List (Acc × Acc × Asset × G)) :
    (moves.map movePosting).sum ∈
      (assetSum : (Acc × Asset →₀ G) →+ (Asset →₀ G)).ker :=
  list_sum_mem fun _ hv => by
    obtain ⟨mv, _, rfl⟩ := List.mem_map.mp hv
    exact posting_mem_ker _ _ _ _

end Bounds

/-! ## The general-theorem poles at the level of vectors -/

/-- A two-account transfer conserves. -/
theorem transfer_conserves : Conserves (posting (0 : ℕ) 1 (0 : ℕ) (5 : ℤ)) :=
  (conserves_iff_mem_ker _).mpr (posting_mem_ker _ _ _ _)

/-- A mint-shaped delta (credit with no debit) does not conserve. -/
theorem mint_not_conserves : ¬ Conserves (single ((1 : ℕ), (0 : ℕ)) (2 : ℤ)) := by
  unfold Conserves
  rw [assetSum_single]
  simp

/-- info: 'Minidregg.Theory.Conservation.conserves_iff_delta_mem_ker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conserves_iff_delta_mem_ker
/-- info: 'Minidregg.Theory.Conservation.postings_generate_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms postings_generate_kernel
/-- info: 'Minidregg.Theory.Conservation.posting_mem_ker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms posting_mem_ker
/-- info: 'Minidregg.Theory.Conservation.delta_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms delta_add
/-- info: 'Minidregg.Theory.Conservation.sum_accounts_eq_assetSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sum_accounts_eq_assetSum
/-- info: 'Minidregg.Theory.Conservation.abs_moves_sum_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms abs_moves_sum_apply_le
/-- info: 'Minidregg.Theory.Conservation.transfer_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transfer_conserves
/-- info: 'Minidregg.Theory.Conservation.mint_not_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mint_not_conserves

end Minidregg.Theory.Conservation
