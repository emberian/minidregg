/- Templates over rigid Self/Super (OB-LTUO LT2, docs/objective-bend/MODULAR-TYPING.md §6).

Step 2: `canonical_instantiate`. The checker compares types by `Ty.canonical` (sorted
rows, first field of a name wins). A template is checked with rigid variables and
emitted at instances `τ.instantiate σ`; for a conversion the template's checker
accepted (`a.canonical = b.canonical`) to remain a conversion at the instance, canonical
form must commute with instantiation up to a final `canonical`:

    (τ.instantiate σ).canonical = (τ.canonical.instantiate σ).canonical

including the override case (a tail instantiated with a row that repeats a listed
field: the listed one, which is first, wins on both sides). No sortedness premise is
needed: `insertCanonical` is first-match, and the two facts it rests on
(`insertCanonical_same`, `insertCanonical_comm`) hold for every row. -/
import Theory.ObjectiveBendTypes
import Theory.AxiomPin
namespace Minidregg.Theory.ObjectiveBendTemplates
open ObjectiveBendTypes
set_option autoImplicit false

theorem lt_of_not_lt_ne {a b : String} (h1 : ¬ a < b) (h2 : a ≠ b) : b < a :=
  Decidable.byContradiction fun h3 => h2 (String.le_antisymm (String.not_lt.mp h3) (String.not_lt.mp h1))

theorem tri {a b : String} (h : a ≠ b) : (a < b ∧ ¬ b < a) ∨ (b < a ∧ ¬ a < b) := by
  by_cases l : a < b
  · exact .inl ⟨l, String.lt_asymm l⟩
  · have g := lt_of_not_lt_ne l h
    exact .inr ⟨g, l⟩

/-- Inserting a name twice keeps the second insertion. -/
theorem insertCanonical_same (row : Ty) (name : String) (first second : Ty) :
    (row.insertCanonical name first).insertCanonical name second = row.insertCanonical name second := by
  induction row with
  | field prior old tail _ ih =>
    by_cases he : name = prior
    · subst he; simp [Ty.insertCanonical]
    · by_cases hl : name < prior
      · simp [Ty.insertCanonical, he, hl]
      · simp [Ty.insertCanonical, he, hl, ih]
  | _ => simp [Ty.insertCanonical]

/-- Inserting two different names commutes. -/
theorem insertCanonical_comm (row : Ty) (n p : String) (a b : Ty) (ne : n ≠ p) :
    (row.insertCanonical n a).insertCanonical p b = (row.insertCanonical p b).insertCanonical n a := by
  have ne' : p ≠ n := fun h => ne h.symm
  induction row with
  | field q o t _ ih =>
    by_cases hn : n = q
    · subst hn
      by_cases hp : p < n
      · simp [Ty.insertCanonical, ne, ne', hp, String.lt_asymm hp]
      · have : n < p := lt_of_not_lt_ne hp ne'
        simp [Ty.insertCanonical, ne', hp]
    · by_cases hp : p = q
      · subst hp
        by_cases hl : n < p
        · simp [Ty.insertCanonical, ne, ne', hl, String.lt_asymm hl]
        · simp [Ty.insertCanonical, ne, hl]
      · have hp' : q ≠ p := fun h => hp h.symm
        rcases tri hn with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases tri hp with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
          rcases tri ne with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
          simp [Ty.insertCanonical, a1, a2, b1, b2, c1, c2, hn, hp, hp', ne, ne', ih] <;>
          first
          | exact absurd (String.lt_trans (String.lt_trans ‹_› ‹_›) ‹_›) (String.lt_irrefl _)
          | skip
  | _ =>
    by_cases hl : n < p
    · simp [Ty.insertCanonical, ne, ne', hl, String.lt_asymm hl]
    · have hl' : p < n := lt_of_not_lt_ne hl ne
      simp [Ty.insertCanonical, ne, ne', hl, hl']

theorem canonical_instantiate_insert (σ : Nat → Ty) (row : Ty) (name : String) (member : Ty) :
    ((row.insertCanonical name member).instantiate σ).canonical =
      ((row.instantiate σ).canonical).insertCanonical name ((member.instantiate σ).canonical) := by
  induction row with
  | field prior old tail _ ih =>
    by_cases he : name = prior
    · subst he
      simp [Ty.insertCanonical, Ty.instantiate, Ty.canonical, insertCanonical_same]
    · by_cases hl : name < prior
      · simp [Ty.insertCanonical, he, hl, Ty.instantiate, Ty.canonical]
      · simp only [Ty.insertCanonical, he, hl, if_false, Ty.instantiate, Ty.canonical]
        rw [ih, insertCanonical_comm _ _ _ _ _ he]
  | _ => simp [Ty.insertCanonical, Ty.instantiate, Ty.canonical]

/-- Canonical form commutes with instantiation, up to a final `canonical`. -/
theorem canonical_instantiate (σ : Nat → Ty) (type : Ty) :
    (type.instantiate σ).canonical = (type.canonical.instantiate σ).canonical := by
  induction type with
  | field name member tail ihm iht =>
    simp only [Ty.instantiate, Ty.canonical]
    rw [canonical_instantiate_insert, ← iht, ← ihm]
  | arrow reuse q d c ihd ihc => simp [Ty.instantiate, Ty.canonical, ihd, ihc]
  | specification m e ihm ihe => simp [Ty.instantiate, Ty.canonical, ihm, ihe]
  | prototype s t ihs iht => simp [Ty.instantiate, Ty.canonical, ihs, iht]
  | variant r ih => simp [Ty.instantiate, Ty.canonical, ih]
  | computation p r a ihp ihr iha => simp [Ty.instantiate, Ty.canonical, ihp, ihr, iha]
  | _ => simp [Ty.instantiate, Ty.canonical]

/-- So a conversion the template's checker accepted survives every instantiation. -/
theorem canonical_eq_instantiate (σ : Nat → Ty) {a b : Ty} (h : a.canonical = b.canonical) :
    (a.instantiate σ).canonical = (b.instantiate σ).canonical := by
  rw [canonical_instantiate σ a, canonical_instantiate σ b, h]

#assert_axioms insertCanonical_same insertCanonical_comm canonical_instantiate_insert canonical_instantiate
  canonical_eq_instantiate
end Minidregg.Theory.ObjectiveBendTemplates
