/-
# Theory.ViewMerge — federation merge is a colimit of partial views (N6, poset shadow).

`docs/KERNEL-NECESSITY.md` §N6: the whole-history object is the colimit of the diagram
of partial views; federation-merge is that colimit one level up, and LaceMerge's
join-semilattice is its poset shadow. This file is the shadow, stated as the named
categorical fact and armed with computed witnesses on the concrete carrier `Finset ℕ`
(a view = the set of admitted event ids; merge = `∪`).

Partial views of a replicated log form a `SemilatticeSup V`; a preorder is a category
(`homOfLE`), so a view diagram has cocones, and the merge is the cocone that is a
colimit. LaceMerge's four laws — idempotent, commutative, associative, monotone — are
`sup_idem`, `sup_comm`, `sup_assoc`, `le_sup_left`: the instance subsumes the ancestor's
four one-line proofs, so they are not restated here.

What is proved:
  * `binary_merge_is_colimit` — the merge of two views is their binary coproduct. One
    line from mathlib (`Preorder.isColimitBinaryCofan`); it is here as the NAMED
    statement "the merge is the colimit", not as new mathematics.
  * `finite_merge_is_colimit` — for any finite family of views, every cocone whose
    point is the family's `Finset.sup` is a colimit of the discrete diagram: the
    whole-history object of N partial views is their colimit. Hypothesis `[OrderBot V]`
    (the empty family merges to the empty view) rather than `Nonempty J` with `sup'`.
  * `chain_merge_is_colimit` — a finite prefix of a monotone chain of views merges to
    its top element, which is the colimit of the chain diagram. In any preorder; the
    infinite chain is deliberately absent (a chain in `Finset ℕ` need not have a `Finset`
    supremum, and no completeness is assumed).
  * `not_colimit_of_strict_upper_bound` and its computed instance
    `strict_upper_bound_not_colimit` — teeth: a cocone at a STRICT upper bound of two
    views is not a colimit. Views `{0,1}` and `{1,2}`: the cocone at `{0,1,2}` is a
    colimit (`merge_colimit_computed`); the cocone at `{0,1,2,3}` is not.
  * `lawful_views_merge_as_colimit` — the bridge to `Theory.Confluence`: under
    I-confluence the merge of two lawful views is their coproduct among the lawful
    views. Teeth in this vocabulary: on the PN-counter, the two non-negative replica
    views whose merge overdraws have NO least upper bound among the lawful views
    (`overdraft_has_no_lawful_merge`) — four incomparable minimal lawful upper bounds
    exist, one per way of covering the shortfall — so `pair xL yL` has no colimit in
    the lawful subcategory at all (`overdraft_pair_has_no_colimit`).

Residual:
  * `[N6-receipt-colimit]` the receipt-chain colimit (the Selvage accumulator as an
    incremental colimit computation carrying proofs) is not here.
  * `[N6-blocklace]` equivocation exclusion and per-author strands are not modeled; a
    view here is a bare set of event ids.
  * `[N6-cross-canonical]` breadstuffs' `crossCanonical_is_the_gap` is not yet ported.
-/
import Theory.Confluence

namespace Minidregg.Theory.ViewMerge

open CategoryTheory Limits Minidregg.Theory.Confluence

universe u v

/-! ## §1 — The merge is the colimit. -/

section Generic

variable {V : Type u}

/-- The merge of two views is their binary coproduct. Mathlib's
`Preorder.isColimitBinaryCofan`, named for what it says here. -/
theorem binary_merge_is_colimit [SemilatticeSup V] (x y : V) :
    Nonempty (IsColimit (BinaryCofan.mk (P := x ⊔ y) (homOfLE le_sup_left)
      (homOfLE le_sup_right))) :=
  ⟨Preorder.isColimitBinaryCofan x y⟩

/-- The `Finset.sup` of a finite family is the least upper bound of the discrete diagram
it spans. -/
theorem isLUB_range_discrete [SemilatticeSup V] [OrderBot V] {J : Type v} [Fintype J]
    (f : J → V) : IsLUB (Set.range (Discrete.functor f).obj) (Finset.univ.sup f) :=
  ⟨by rintro _ ⟨j, rfl⟩; exact Finset.le_sup (Finset.mem_univ j.as),
   fun _ hu => Finset.sup_le fun j _ => hu ⟨⟨j⟩, rfl⟩⟩

/-- **N partial views merge to their colimit.** Every cocone over the discrete diagram
of a finite family of views whose point is the family's `Finset.sup` is a colimit. -/
theorem finite_merge_is_colimit [SemilatticeSup V] [OrderBot V] {J : Type v} [Fintype J]
    (f : J → V) (c : Cocone (Discrete.functor f)) (hc : c.pt = Finset.univ.sup f) :
    Nonempty (IsColimit c) :=
  ⟨Preorder.isColimitOfIsLUB _ c (hc ▸ isLUB_range_discrete f)⟩

/-- The top of a finite monotone chain is the least upper bound of the chain diagram. -/
theorem isLUB_range_chain [Preorder V] {n : ℕ} (g : Fin (n + 1) →o V) :
    IsLUB (Set.range g.monotone.functor.obj) (g (Fin.last n)) := by
  rw [Monotone.functor_obj]
  refine IsGreatest.isLUB ⟨⟨Fin.last n, rfl⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact g.monotone (Fin.le_last i)

/-- **A finite prefix of a chain merges to its top.** Every cocone over the chain diagram
`Fin (n+1) ⥤ V` of a monotone `g` whose point is `g (Fin.last n)` is a colimit. -/
theorem chain_merge_is_colimit [Preorder V] {n : ℕ} (g : Fin (n + 1) →o V)
    (c : Cocone g.monotone.functor) (hc : c.pt = g (Fin.last n)) : Nonempty (IsColimit c) :=
  ⟨Preorder.isColimitOfIsLUB _ c (hc ▸ isLUB_range_chain g)⟩

/-- The object range of the `pair` diagram is the two-element set. -/
theorem range_pair_obj {C : Type u} [Category.{v} C] (X Y : C) :
    Set.range (pair X Y).obj = {X, Y} := by
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨j⟩, rfl⟩
    cases j <;> simp
  · rintro (rfl | rfl)
    · exact ⟨⟨WalkingPair.left⟩, rfl⟩
    · exact ⟨⟨WalkingPair.right⟩, rfl⟩

/-- **Teeth, general form.** A cocone on two views sitting STRICTLY above their merge is
not a colimit: a colimit point is the least upper bound, and the merge is a smaller one. -/
theorem not_colimit_of_strict_upper_bound [SemilatticeSup V] {x y : V} (c : Cocone (pair x y))
    (hlt : x ⊔ y < c.pt) : IsEmpty (IsColimit c) :=
  ⟨fun hcol => by
    have h := Preorder.isLUB_of_isColimit _ hcol
    rw [range_pair_obj] at h
    exact absurd (h.2 (isLUB_pair (a := x) (b := y)).1) (not_le_of_gt hlt)⟩

/-- **Lawful views merge as their coproduct** — `Confluence.merge_is_coproduct` in
federation vocabulary: under I-confluence the merge of two lawful views is their
coproduct in the category of lawful views. -/
theorem lawful_views_merge_as_colimit [SemilatticeSup V] {I : Invariant V} (h : IConfluent I)
    (x y : {v // I v}) :
    Nonempty (IsColimit (BinaryCofan.mk (P := (⟨x.1 ⊔ y.1, h _ _ x.2 y.2⟩ : {v // I v}))
      (homOfLE (Subtype.coe_le_coe.mp le_sup_left))
      (homOfLE (Subtype.coe_le_coe.mp le_sup_right)))) :=
  merge_is_coproduct h x y

end Generic

/-! ## §2 — Computed witnesses on `Finset ℕ`. -/

namespace Witness

/-- A view that admitted events 0 and 1. -/
def viewA : Finset ℕ := {0, 1}

/-- A view that admitted events 1 and 2. -/
def viewB : Finset ℕ := {1, 2}

theorem merge_computed : viewA ⊔ viewB = {0, 1, 2} := by decide
theorem viewA_le_merge : viewA ≤ {0, 1, 2} := by decide
theorem viewB_le_merge : viewB ≤ {0, 1, 2} := by decide
theorem viewA_le_strict : viewA ≤ {0, 1, 2, 3} := by decide
theorem viewB_le_strict : viewB ≤ {0, 1, 2, 3} := by decide

/-- The cocone at `{0,1,2}` is a colimit of `viewA`, `viewB`. -/
theorem merge_colimit_computed :
    Nonempty (IsColimit (BinaryCofan.mk (P := ({0, 1, 2} : Finset ℕ))
      (homOfLE viewA_le_merge) (homOfLE viewB_le_merge))) := by
  refine ⟨Preorder.isColimitOfIsLUB _ _ ?_⟩
  rw [range_pair_obj]
  show IsLUB {viewA, viewB} ({0, 1, 2} : Finset ℕ)
  rw [← merge_computed]
  exact isLUB_pair

/-- The cocone at the strict upper bound `{0,1,2,3}` is NOT a colimit: `{0,1,2}` is a
smaller upper bound. -/
theorem strict_upper_bound_not_colimit :
    IsEmpty (IsColimit (BinaryCofan.mk (P := ({0, 1, 2, 3} : Finset ℕ))
      (homOfLE viewA_le_strict) (homOfLE viewB_le_strict))) :=
  not_colimit_of_strict_upper_bound _ (by
    rw [merge_computed]
    exact lt_iff_le_and_ne.mpr ⟨by decide, by decide⟩)

/-- Three overlapping views. -/
def views3 : Fin 3 → Finset ℕ := ![{0, 1}, {1, 2}, {2, 3}]

theorem views3_sup_computed : Finset.univ.sup views3 = {0, 1, 2, 3} := by decide

/-- The whole-history object of the three views is their colimit. -/
theorem views3_colimit :
    Nonempty (IsColimit (Preorder.coconeOfUpperBound (Discrete.functor views3)
      (isLUB_range_discrete views3).1)) :=
  finite_merge_is_colimit views3 _ rfl

/-- A growing chain of views. -/
def chain3 : Fin 3 →o Finset ℕ := ⟨![{0}, {0, 1}, {0, 1, 2}], by decide⟩

theorem chain3_top_computed : chain3 (Fin.last 2) = {0, 1, 2} := by decide

/-- The chain's top is the colimit of the chain. -/
theorem chain3_colimit :
    Nonempty (IsColimit (Preorder.coconeOfUpperBound chain3.monotone.functor
      (isLUB_range_chain chain3).1)) :=
  chain_merge_is_colimit chain3 _ rfl

/-! ### Teeth for the bridge: lawful PN-counter views with no lawful merge.

`Confluence.Witness.xView`, `yView` are both non-negative; their merge is not. Among
the non-negative views, `{xView, yView}` has no least upper bound: covering the
shortfall of 3 on replica 0 or on replica 1 gives two incomparable lawful upper bounds
whose meet is the (unlawful) merge itself. -/

open Minidregg.Theory.Confluence.Witness in
/-- The lawful (non-negative) views of the two-replica PN-counter. -/
abbrev LawfulPN := {s : PN // 0 ≤ value s}

open Minidregg.Theory.Confluence.Witness in
def xL : LawfulPN := ⟨xView, by decide⟩

open Minidregg.Theory.Confluence.Witness in
def yL : LawfulPN := ⟨yView, by decide⟩

open Minidregg.Theory.Confluence.Witness in
/-- Replica 0 covers the shortfall of 3. -/
def coverOn0 : LawfulPN := ⟨![(8, 4), (0, 4)], by decide⟩

open Minidregg.Theory.Confluence.Witness in
/-- Replica 1 covers the shortfall of 3. -/
def coverOn1 : LawfulPN := ⟨![(5, 4), (3, 4)], by decide⟩

-- The `open … in` also activates `Confluence.Witness`'s scoped `DecidableRel (· ≤ ·)`
-- instances on `Fin 2 → ℕ × ℕ`, which the `decide` calls on PN order facts below use.
open Minidregg.Theory.Confluence.Witness in
/-- **No lawful merge.** The two lawful views have no least upper bound among the
lawful views. -/
theorem overdraft_has_no_lawful_merge : ¬ ∃ z : LawfulPN, IsLUB {xL, yL} z := by
  rintro ⟨z, hz⟩
  have hx : xL ≤ z := hz.1 (Set.mem_insert _ _)
  have hy : yL ≤ z := hz.1 (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hub : ∀ u : LawfulPN, xL ≤ u → yL ≤ u → u ∈ upperBounds {xL, yL} := by
    intro u hxu hyu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hxu
    · exact hyu
  have h0 : z ≤ coverOn0 :=
    hz.2 (hub _ (Subtype.coe_le_coe.mp (by decide)) (Subtype.coe_le_coe.mp (by decide)))
  have h1 : z ≤ coverOn1 :=
    hz.2 (hub _ (Subtype.coe_le_coe.mp (by decide)) (Subtype.coe_le_coe.mp (by decide)))
  have hlow : xView ⊔ yView ≤ z.1 := sup_le hx hy
  have hup : z.1 ≤ coverOn0.1 ⊓ coverOn1.1 := le_inf h0 h1
  have hmeet : coverOn0.1 ⊓ coverOn1.1 = xView ⊔ yView := by decide
  have hz1 : z.1 = xView ⊔ yView := le_antisymm (hmeet ▸ hup) hlow
  have hval : 0 ≤ value z.1 := z.2
  rw [hz1] at hval
  exact absurd hval (by decide)

/-- **No colimit among the lawful views.** The pair diagram of the two lawful views has
no colimit in the category of lawful views: `Preorder.hasColimit_iff_hasLUB`. -/
theorem overdraft_pair_has_no_colimit : ¬ HasColimit (pair xL yL) := fun h =>
  overdraft_has_no_lawful_merge (by
    obtain ⟨z, hz⟩ := (Preorder.hasColimit_iff_hasLUB (pair xL yL)).mp h
    exact ⟨z, by rwa [range_pair_obj] at hz⟩)

end Witness

/-! ## §3 — Axiom pins. -/

/-- info: 'Minidregg.Theory.ViewMerge.binary_merge_is_colimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms binary_merge_is_colimit

/-- info: 'Minidregg.Theory.ViewMerge.finite_merge_is_colimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finite_merge_is_colimit

/-- info: 'Minidregg.Theory.ViewMerge.chain_merge_is_colimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms chain_merge_is_colimit

/--
info: 'Minidregg.Theory.ViewMerge.not_colimit_of_strict_upper_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms not_colimit_of_strict_upper_bound

/-- info: 'Minidregg.Theory.ViewMerge.lawful_views_merge_as_colimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lawful_views_merge_as_colimit

/-- info: 'Minidregg.Theory.ViewMerge.Witness.merge_colimit_computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Witness.merge_colimit_computed

/--
info: 'Minidregg.Theory.ViewMerge.Witness.strict_upper_bound_not_colimit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Witness.strict_upper_bound_not_colimit

/-- info: 'Minidregg.Theory.ViewMerge.Witness.views3_colimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Witness.views3_colimit

/-- info: 'Minidregg.Theory.ViewMerge.Witness.chain3_colimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Witness.chain3_colimit

/--
info: 'Minidregg.Theory.ViewMerge.Witness.overdraft_has_no_lawful_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Witness.overdraft_has_no_lawful_merge

/--
info: 'Minidregg.Theory.ViewMerge.Witness.overdraft_pair_has_no_colimit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Witness.overdraft_pair_has_no_colimit

end Minidregg.Theory.ViewMerge
