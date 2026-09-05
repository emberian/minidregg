/-
# Theory.ExceptionalSetLocalRing — exceptional sets in a local ring are bounded by the residue field

**The question this file settles.**  A sumcheck / lattice-commitment "challenge set" (an
*exceptional set*, `IsExceptional`) is a set whose pairwise differences of distinct elements are
UNITS.  Over a field every set is exceptional; over a ring that is not a field the question is how
large an exceptional set can be.  For a **local** ring the answer is exact: an exceptional set is
one on which the residue map is injective, so it can be no larger than the residue field.  This is
what puts the ceiling `|A| ≤ 2` on every exceptional set of `ℤ_{2^k}[X]/(X^N + 1)` (residue field
`F_2`), and what lets a Galois ring `GR(2^k, d)` (residue field `F_{2^d}`) carry exceptional sets
of size `2^d`.

**Statements (statement-first; every hypothesis is a constraint, see the teeth).**

* `isExceptional_iff_injOn` — for a **local homomorphism** `f : R →+* S` into a **field**,
  `IsExceptional A ↔ Set.InjOn f A`.  (`⇐` needs both hypotheses; `⇒` holds for any hom into a
  nontrivial ring, `injOn_of_isExceptional`.)
* `isUnit_sub_of_injOn_residue` / `isExceptional_iff_injOn_residue` — the instance at
  `f = IsLocalRing.residue R` of a local ring `R`: injectivity of the residue map on `A` is
  exactly the exceptional-set property.
* `card_le_card_residueField` / `card_le_card_residueField_of_isExceptional` — **the ceiling**:
  `A.card ≤ Fintype.card (ResidueField R)`.
* `card_le_two_of_card_residueField_eq_two` — the `F_2` corollary: residue field of size two ⇒
  every exceptional set has at most two elements.

**Witness / falsifier / premise inhabitation — all on Mathlib's real `ZMod 4`.**

* *Premise inhabitation.*  `ZMod 4` is a local ring.  Mathlib has NO such instance (there is none
  for `ZMod (p^k)` at this revision); `instIsLocalRingZMod4` supplies it by decision on the
  16 pairs `(a, b)` of `IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add`.
* *Satisfying witness.*  `A = {0, 1}`: `isExceptional_zero_one` (`1 − 0 = 1` is a unit) and
  `injOn_residue_zero_one`.
* *Falsifying case — the injectivity hypothesis is load-bearing.*  `A = {0, 2}`:
  `residue_two_eq_residue_zero` (both residues are `0`, so `not_injOn_residue_zero_two`) and
  `not_isUnit_two_zmod4` (so `not_isExceptional_zero_two`).  Dropping injectivity drops the
  conclusion.
* *The ceiling is attained and sharp at `ZMod 4`.*  `card_residueField_zmod4 : |k| = 2`, so by
  the general theorem `card_le_two_of_isExceptional_zmod4` every exceptional subset of `ZMod 4`
  has `≤ 2` elements — and `card_le_two_of_isExceptional_zmod4_by_decision` says the same thing
  by exhaustive decision over all 16 subsets, an independent derivation of the same statement
  (the general argument checks the computation; the computation checks that the general argument
  was instantiated at the right ring).

**Reused from Mathlib** (this file hand-rolls none of it): `IsLocalRing.residue`,
`IsLocalRing.residue_eq_zero_iff`, `IsLocalRing.mem_maximalIdeal`, `IsLocalRing.residue_surjective`,
the `IsLocalHom (residue R)` instance, `IsUnit.of_map`, `Finset.card_image_of_injOn`,
`Finset.card_le_univ`, `isUnit_iff_exists_inv`.
-/
import Mathlib.Tactic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

namespace Minidregg.Theory.ExceptionalSetLocalRing

open IsLocalRing

set_option autoImplicit false

/-! ## 0. The notion -/

/-- An **exceptional set** (sumcheck / lattice challenge set): the difference of any two distinct
elements is a unit. -/
def IsExceptional {R : Type*} [Ring R] (A : Set R) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → IsUnit (a - b)

/-! ## 1. The general lemma, homomorphism form

`f : R →+* S` a **local** homomorphism (units pull back to units) into a **field**.  These are the
two hypotheses that make `Set.InjOn f A` imply the unit property; the converse needs neither. -/

section Hom

variable {R S : Type*} [CommRing R]

/-- Pairwise units ⇒ `f` is injective on `A`, for ANY ring hom into a nontrivial ring: a unit
never maps to `0`. -/
theorem injOn_of_isExceptional [Ring S] [Nontrivial S] (f : R →+* S) {A : Set R}
    (hA : IsExceptional A) :
    Set.InjOn f A := by
  intro a ha b hb hab
  by_contra hne
  have hu : IsUnit (f (a - b)) := (hA a ha b hb hne).map f
  rw [map_sub, hab, sub_self] at hu
  exact not_isUnit_zero hu

/-- **The general lemma.**  `f` a local hom into a field and injective on `A` ⇒ every
difference of distinct elements of `A` is a unit. -/
theorem isExceptional_of_injOn [Field S] (f : R →+* S) [IsLocalHom f] {A : Set R}
    (hA : Set.InjOn f A) : IsExceptional A := by
  intro a ha b hb hne
  have hf : f (a - b) ≠ 0 := by
    rw [map_sub, sub_ne_zero]
    exact fun h => hne (hA ha hb h)
  exact IsUnit.of_map f _ (isUnit_iff_ne_zero.mpr hf)

/-- Both directions: for a local hom into a field, exceptional ⇔ injective. -/
theorem isExceptional_iff_injOn [Field S] (f : R →+* S) [IsLocalHom f] {A : Set R} :
    IsExceptional A ↔ Set.InjOn f A :=
  ⟨injOn_of_isExceptional f, isExceptional_of_injOn f⟩

end Hom

/-! ## 2. The general lemma at the residue map of a local ring, and the ceiling -/

section Local

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A finite local ring has a finite residue field (the residue map is onto).  Mathlib does not
find this by instance search because `ResidueField` is a `def`. -/
instance finite_residueField [Finite R] : Finite (ResidueField R) :=
  Finite.of_surjective _ (residue_surjective (R := R))

/-- **Lemma 1 as specified.**  `R` local, `residue R` injective on `A` ⇒ pairwise-unit
differences. -/
theorem isUnit_sub_of_injOn_residue {A : Set R} (hA : Set.InjOn (residue R) A) :
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → IsUnit (a - b) :=
  isExceptional_of_injOn (residue R) hA

/-- In a local ring, exceptional ⇔ the residue map is injective on the set. -/
theorem isExceptional_iff_injOn_residue {A : Set R} :
    IsExceptional A ↔ Set.InjOn (residue R) A :=
  isExceptional_iff_injOn (residue R)

/-- **The ceiling (injectivity form).**  A set on which the residue map is injective is no larger
than the residue field. -/
theorem card_le_card_residueField [Fintype (ResidueField R)] {A : Finset R}
    (hA : Set.InjOn (residue R) A) : A.card ≤ Fintype.card (ResidueField R) := by
  classical
  rw [← Finset.card_image_of_injOn hA]
  exact Finset.card_le_univ _

/-- **The ceiling (exceptional-set form).**  Every exceptional set of a local ring is no larger
than its residue field. -/
theorem card_le_card_residueField_of_isExceptional [Fintype (ResidueField R)] {A : Finset R}
    (hA : IsExceptional (A : Set R)) : A.card ≤ Fintype.card (ResidueField R) :=
  card_le_card_residueField (isExceptional_iff_injOn_residue.mp hA)

/-- The same ceiling with `Nat.card`, for a merely `Finite` residue field. -/
theorem card_le_natCard_residueField_of_isExceptional [Finite (ResidueField R)] {A : Finset R}
    (hA : IsExceptional (A : Set R)) : A.card ≤ Nat.card (ResidueField R) := by
  haveI := Fintype.ofFinite (ResidueField R)
  rw [Nat.card_eq_fintype_card]
  exact card_le_card_residueField_of_isExceptional hA

/-- **The `F_2` corollary.**  Residue field of size two (e.g. `ℤ_{2^k}[X]/(X^N + 1)`) ⇒ every
exceptional set has at most two elements. -/
theorem card_le_two_of_card_residueField_eq_two [Fintype (ResidueField R)]
    (h2 : Fintype.card (ResidueField R) = 2) {A : Finset R} (hA : IsExceptional (A : Set R)) :
    A.card ≤ 2 :=
  h2 ▸ card_le_card_residueField_of_isExceptional hA

end Local

/-! ## 3. Witness, falsifier, premise inhabitation — on `ZMod 4`

Everything here is decided on Mathlib's real `ZMod 4` (after rewriting `IsUnit` to
`∃ c, a * c = 1`, which is decidable over a finite commutative monoid). -/

section ZMod4

instance : Fact (1 < 4) := ⟨by norm_num⟩

/-- Premise inhabitation: `ZMod 4` is a local ring.  Mathlib has no such instance at this
revision; decided over the 16 pairs `(a, b)`. -/
instance instIsLocalRingZMod4 : IsLocalRing (ZMod 4) := by
  have key : ∀ a b : ZMod 4, (∃ c, (a + b) * c = 1) → (∃ c, a * c = 1) ∨ (∃ c, b * c = 1) := by
    decide
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add ?_
  intro a b h
  simpa only [isUnit_iff_exists_inv] using key a b (isUnit_iff_exists_inv.mp h)

/-- `2` is not a unit of `ZMod 4`. -/
theorem not_isUnit_two_zmod4 : ¬IsUnit (2 : ZMod 4) := by
  rw [isUnit_iff_exists_inv]; decide

/-- `1` is a unit of `ZMod 4` (trivially — recorded because it is the witness's difference). -/
theorem isUnit_one_sub_zero_zmod4 : IsUnit ((1 : ZMod 4) - 0) := by simp

/-- The residue map of `ZMod 4` identifies `2` with `0`. -/
theorem residue_two_eq_residue_zero : residue (ZMod 4) 2 = residue (ZMod 4) 0 := by
  rw [map_zero, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  exact not_isUnit_two_zmod4

/-- …and `3` with `1`. -/
theorem residue_three_eq_residue_one : residue (ZMod 4) 3 = residue (ZMod 4) 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  exact not_isUnit_two_zmod4

/-- **Satisfying witness.**  `{0, 1} ⊆ ZMod 4` is exceptional: its only difference is `±1`. -/
theorem isExceptional_zero_one : IsExceptional ({0, 1} : Set (ZMod 4)) := by
  intro a ha b hb hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rw [isUnit_iff_exists_inv]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hne
  · decide
  · decide
  · exact absurd rfl hne

/-- …equivalently, the residue map is injective on `{0, 1}`. -/
theorem injOn_residue_zero_one : Set.InjOn (residue (ZMod 4)) ({0, 1} : Set (ZMod 4)) :=
  isExceptional_iff_injOn_residue.mp isExceptional_zero_one

/-- **Falsifier, hypothesis side.**  The residue map is NOT injective on `{0, 2}`. -/
theorem not_injOn_residue_zero_two : ¬Set.InjOn (residue (ZMod 4)) ({0, 2} : Set (ZMod 4)) :=
  fun h => by
    have h02 : (0 : ZMod 4) = 2 :=
      h (by simp) (by simp) residue_two_eq_residue_zero.symm
    exact absurd h02 (by decide)

/-- **Falsifier, conclusion side.**  `{0, 2}` is NOT exceptional: `2 − 0 = 2` is not a unit.
Together with `not_injOn_residue_zero_two`: the injectivity hypothesis of
`isUnit_sub_of_injOn_residue` is a genuine constraint. -/
theorem not_isExceptional_zero_two : ¬IsExceptional ({0, 2} : Set (ZMod 4)) := fun h =>
  not_isUnit_two_zmod4 (by simpa using h 2 (by simp) 0 (by simp) (by decide))

/-- The residue field of `ZMod 4` has exactly two elements: `residue` is onto, and it folds
`{0, 1, 2, 3}` to `{residue 0, residue 1}` with `residue 0 ≠ residue 1`. -/
theorem card_residueField_zmod4 : Nat.card (ResidueField (ZMod 4)) = 2 := by
  classical
  haveI : Fintype (ResidueField (ZMod 4)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.image_univ_of_surjective (residue_surjective (R := ZMod 4))]
  have huniv : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [huniv]
  simp only [Finset.image_insert, Finset.image_singleton]
  rw [residue_two_eq_residue_zero, residue_three_eq_residue_one]
  have hfold : ({residue (ZMod 4) 0, residue (ZMod 4) 1, residue (ZMod 4) 0, residue (ZMod 4) 1} :
      Finset (ResidueField (ZMod 4))) = {residue (ZMod 4) 0, residue (ZMod 4) 1} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [hfold, Finset.card_pair_eq_two_iff, map_zero, map_one]
  exact zero_ne_one

/-- **The ceiling at `ZMod 4`, from the general theorem.**  Every exceptional subset of `ZMod 4`
has at most two elements. -/
theorem card_le_two_of_isExceptional_zmod4 {A : Finset (ZMod 4)} (hA : IsExceptional (A : Set (ZMod 4))) :
    A.card ≤ 2 := by
  have h := card_le_natCard_residueField_of_isExceptional hA
  rwa [card_residueField_zmod4] at h

/-- **The same ceiling, by exhaustive decision** over all 16 subsets of `ZMod 4` — an
independent derivation of `card_le_two_of_isExceptional_zmod4`. -/
theorem card_le_two_of_isExceptional_zmod4_by_decision {A : Finset (ZMod 4)}
    (hA : IsExceptional (A : Set (ZMod 4))) : A.card ≤ 2 := by
  have key : ∀ A : Finset (ZMod 4),
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ c, (a - b) * c = 1) → A.card ≤ 2 := by decide
  refine key A fun a ha b hb hne => ?_
  exact isUnit_iff_exists_inv.mp (hA a (Finset.mem_coe.mpr ha) b (Finset.mem_coe.mpr hb) hne)

/-- And the ceiling is ATTAINED: `{0, 1}` has two elements and is exceptional. -/
theorem card_zero_one_eq_two : ({0, 1} : Finset (ZMod 4)).card = 2 := by decide

end ZMod4

/-! ## 4. Axiom pins -/

/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.injOn_of_isExceptional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms injOn_of_isExceptional
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.isExceptional_of_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isExceptional_of_injOn
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.isExceptional_iff_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isExceptional_iff_injOn
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.isUnit_sub_of_injOn_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isUnit_sub_of_injOn_residue
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.isExceptional_iff_injOn_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isExceptional_iff_injOn_residue
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.card_le_card_residueField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_le_card_residueField
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.card_le_card_residueField_of_isExceptional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_le_card_residueField_of_isExceptional
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.card_le_natCard_residueField_of_isExceptional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_le_natCard_residueField_of_isExceptional
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.card_le_two_of_card_residueField_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_le_two_of_card_residueField_eq_two
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.instIsLocalRingZMod4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms instIsLocalRingZMod4
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.not_isUnit_two_zmod4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_isUnit_two_zmod4
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.residue_two_eq_residue_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms residue_two_eq_residue_zero
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.isExceptional_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isExceptional_zero_one
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.injOn_residue_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms injOn_residue_zero_one
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.not_injOn_residue_zero_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_injOn_residue_zero_two
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.not_isExceptional_zero_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_isExceptional_zero_two
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.card_residueField_zmod4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_residueField_zmod4
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.card_le_two_of_isExceptional_zmod4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_le_two_of_isExceptional_zmod4
/-- info: 'Minidregg.Theory.ExceptionalSetLocalRing.card_le_two_of_isExceptional_zmod4_by_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_le_two_of_isExceptional_zmod4_by_decision

end Minidregg.Theory.ExceptionalSetLocalRing
