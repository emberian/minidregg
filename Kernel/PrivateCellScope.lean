/-
# Kernel.PrivateCellScope — a reader's scope is a bounded union of class prefixes

Owed item 2 of docs/PRIVATE-CELLS-STATE.md. A blinded cell's private index keys
each address by a fixed-width visibility-class tag followed by its address path
(`Theory.PrivateCellTrie.ClassKeys`). A reader under `fields` is shown exactly
the `Visible` addresses (`ResourceObservationAdmission.Visible`: kept by the
scope, not the hiding key). This module says that set is selected by a bounded
list of tag prefixes, one per named field (or the empty prefix for a full
scope), so a complete opening of a reader's view is at most that many class
openings (`Theory.PrivateCellTrie.classRevealComplete`).

The class of an address is its field (`fieldOf kind address : Option CellField`),
a function of the address alone, never of the store, value or caller. The
covering relation is a two-level forest (`CellField.covers`: `body` covers each
`atomsOf low`, every field itself), so a prefix code realises it: `body` opens
its 3-bit family prefix, every other field opens its whole tag.

* `ClassCode`: the laws a class prefix code must meet, on the fields that fit its
  width (`Fits`).
* `scopeSelectsVisible`: for every code, kind, scope and fitting non-blinding
  address, `Visible` holds exactly when some scope prefix is a prefix of the
  address's tag (and so of its full path, `scopeSelectsPath`).
* `scopePrefixes_card`: at most one prefix per named field, one for a full scope.
* `bitCode`: a concrete code of width `4 + W` on fields whose parameters are below
  `2^W` (satisfiable). Teeth (`Witness`): a scope naming `atomsOf 3` does not
  select `atomsOf 4` or `body`'s plain addresses; naming `body` selects both.

Owed: the fitting premise for declared kinds (a slot is `.slot field.value` with
an unbounded `Digest` value; admission must bound it below `2^W`, the digest
width) and the address-path half of the keys.
-/
module

public import Kernel.ResourceObservationAdmission

@[expose] public section

namespace Minidregg.Kernel.PrivateCellScope

set_option autoImplicit false

open Minidregg.Compiler
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (CellField)
open Minidregg.Kernel.ResourceObservationAdmission

/-- A class prefix code: the tag of each address's field (`none` for an address
with no field), and the prefix a reader naming one field opens. -/
structure ClassCode where
  width : Nat
  Fits : CellField → Prop
  tag : Option CellField → List Bool
  opens : CellField → List Bool
  tag_width : ∀ field, (∀ f, field = some f → Fits f) → (tag field).length = width
  opens_iff : ∀ outer inner, Fits outer → Fits inner →
    (opens outer <+: tag (some inner) ↔ outer.covers inner = true)
  opens_not_none : ∀ outer, Fits outer → ¬ opens outer <+: tag none

/-- The prefixes a reader under `fields` opens. -/
def scopePrefixes (code : ClassCode) : Option (Finset CellField) → Finset (List Bool)
  | none => {[]}
  | some named => named.image code.opens

theorem scopePrefixes_card (code : ClassCode) (fields : Option (Finset CellField)) :
    (scopePrefixes code fields).card ≤ match fields with | none => 1 | some named => named.card := by
  cases fields with
  | none => simp [scopePrefixes]
  | some named => exact Finset.card_image_le

/-- Every field a scope names fits the code. -/
def ScopeFits (code : ClassCode) : Option (Finset CellField) → Prop
  | none => True
  | some named => ∀ f ∈ named, code.Fits f

/-- **Scope selection (statement).** On fitting scopes and addresses, the reader's
view is exactly the addresses whose tag starts with one of the scope's prefixes. -/
def ScopeSelectsVisible (code : ClassCode) : Prop :=
  ∀ (kind : CanonicalCellRegistry.Kind) (fields : Option (Finset CellField))
    (address : Address (CanonicalCellRegistry.layout kind)),
    ScopeFits code fields → (∀ f, fieldOf kind address = some f → code.Fits f) →
    CanonicalCellRegistry.isBlinding kind address = false →
    (Visible fields kind address ↔ ∃ p ∈ scopePrefixes code fields, p <+: code.tag (fieldOf kind address))

theorem scopeSelectsVisible (code : ClassCode) : ScopeSelectsVisible code := by
  intro kind fields address scopeFits addressFits notBlinding
  unfold Visible Kept
  cases fields with
  | none =>
      constructor
      · intro _
        exact ⟨[], by simp [scopePrefixes], List.nil_prefix⟩
      · intro _
        refine ⟨?_, notBlinding⟩
        split <;> trivial
  | some named =>
      simp only [scopePrefixes, Finset.mem_image]
      constructor
      · rintro ⟨kept, _⟩
        split at kept
        · rename_i f found
          obtain ⟨outer, member, covers⟩ := kept
          refine ⟨code.opens outer, ⟨outer, member, rfl⟩, ?_⟩
          rw [found]
          exact (code.opens_iff outer f (scopeFits outer member) (addressFits f found)).mpr covers
        · cases kept
      · rintro ⟨p, ⟨outer, member, rfl⟩, prefixed⟩
        refine ⟨?_, notBlinding⟩
        split
        · rename_i f found
          rw [found] at prefixed
          exact ⟨outer, member,
            (code.opens_iff outer f (scopeFits outer member) (addressFits f found)).mp prefixed⟩
        · rename_i found
          rw [found] at prefixed
          exact absurd prefixed (code.opens_not_none outer (scopeFits outer member))

/-- An opened prefix is no longer than the tag width. -/
theorem opens_length_le (code : ClassCode) (outer : CellField) (fits : code.Fits outer) :
    (code.opens outer).length ≤ code.width := by
  have prefixed := (code.opens_iff outer outer fits fits).mpr (CellField.covers_refl outer)
  have := prefixed.length_le
  rwa [code.tag_width (some outer) (fun f same => by cases same; exact fits)] at this

/-- The same selection on full key paths `tag ++ address bits`. -/
theorem scopeSelectsPath (code : ClassCode) (kind : CanonicalCellRegistry.Kind)
    (fields : Option (Finset CellField)) (address : Address (CanonicalCellRegistry.layout kind))
    (rest : List Bool) (scopeFits : ScopeFits code fields)
    (addressFits : ∀ f, fieldOf kind address = some f → code.Fits f)
    (notBlinding : CanonicalCellRegistry.isBlinding kind address = false) :
    Visible fields kind address ↔
      ∃ p ∈ scopePrefixes code fields, p <+: code.tag (fieldOf kind address) ++ rest := by
  rw [scopeSelectsVisible code kind fields address scopeFits addressFits notBlinding]
  have short : ∀ p ∈ scopePrefixes code fields, p.length ≤ (code.tag (fieldOf kind address)).length := by
    intro p member
    rw [code.tag_width _ addressFits]
    cases fields with
    | none => simp [scopePrefixes] at member; subst member; simp
    | some named =>
        simp only [scopePrefixes, Finset.mem_image] at member
        obtain ⟨outer, inNamed, rfl⟩ := member
        exact opens_length_le code outer (scopeFits outer inNamed)
  constructor
  · rintro ⟨p, member, prefixed⟩
    exact ⟨p, member, prefixed.trans (List.prefix_append _ _)⟩
  · rintro ⟨p, member, prefixed⟩
    exact ⟨p, member, List.prefix_of_prefix_length_le prefixed (List.prefix_append _ _) (short p member)⟩

/-! ## A concrete code -/

/-- `w` low bits of `n`, least significant first. -/
def bitsW (w n : Nat) : List Bool := (List.range w).map n.testBit

theorem bitsW_length (w n : Nat) : (bitsW w n).length = w := by simp [bitsW]

theorem bitsW_injective {w n m : Nat} (hn : n < 2 ^ w) (hm : m < 2 ^ w)
    (same : bitsW w n = bitsW w m) : n = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · have := congrArg (fun l => l[i]?) same
    simpa [bitsW, List.getElem?_map, List.getElem?_range hi] using this
  · have grow : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hn grow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm grow)]

/-- The 3-bit family of a field: `body` and its `atomsOf` sub-fields share one. -/
def family : Option CellField → List Bool
  | some (.slot _) => [false, false, false]
  | some (.balance _) => [false, false, true]
  | some .code => [false, true, false]
  | some .body => [false, true, true]
  | some (.atomsOf _) => [false, true, true]
  | some .annotations => [true, false, false]
  | none => [true, false, true]

/-- The field's parameter bits after a sub-field marker. -/
def detail (w : Nat) : Option CellField → List Bool
  | some (.slot n) => false :: bitsW w n
  | some (.balance a) => false :: bitsW w a
  | some (.atomsOf low) => true :: bitsW w low
  | _ => false :: bitsW w 0

def bitTag (w : Nat) (field : Option CellField) : List Bool := family field ++ detail w field

def bitFits (w : Nat) : CellField → Prop
  | .slot n => n < 2 ^ w
  | .balance a => a < 2 ^ w
  | .atomsOf low => low < 2 ^ w
  | _ => True

def bitOpens (w : Nat) : CellField → List Bool
  | .body => family (some .body)
  | f => bitTag w (some f)

theorem bitTag_length (w : Nat) (field : Option CellField) : (bitTag w field).length = 4 + w := by
  rcases field with _ | f
  · simp [bitTag, family, detail, bitsW_length]; omega
  · cases f <;> simp [bitTag, family, detail, bitsW_length] <;> omega

theorem bitTag_injective (w : Nat) {a b : CellField} (fa : bitFits w a) (fb : bitFits w b)
    (same : bitTag w (some a) = bitTag w (some b)) : a = b := by
  cases a <;> cases b <;> simp [bitTag, family, detail] at same ⊢ <;>
    exact bitsW_injective fa fb same

theorem prefix_eq_of_length {p q : List Bool} (prefixed : p <+: q) (same : p.length = q.length) : p = q :=
  prefixed.eq_of_length same

/-- The concrete code of width `4 + w`. -/
def bitCode (w : Nat) : ClassCode where
  width := 4 + w
  Fits := bitFits w
  tag := bitTag w
  opens := bitOpens w
  tag_width := fun field _ => bitTag_length w field
  opens_iff := by
    intro outer inner fo fi
    by_cases isBody : outer = .body
    · subst isBody
      cases inner <;> simp [bitOpens, bitTag, family, detail, CellField.covers, CellField.isAtoms]
    · have opensTag : bitOpens w outer = bitTag w (some outer) := by
        cases outer <;> first | exact absurd rfl isBody | rfl
      rw [opensTag]
      constructor
      · intro prefixed
        have := bitTag_injective w fo fi
          (prefixed.eq_of_length (by rw [bitTag_length, bitTag_length]))
        subst this
        exact CellField.covers_refl _
      · intro covers
        rw [CellField.covers_eq_of_ne_body isBody covers]
  opens_not_none := by
    intro outer _
    by_cases isBody : outer = .body
    · subst isBody
      simp [bitOpens, bitTag, family, detail]
    · have opensTag : bitOpens w outer = bitTag w (some outer) := by
        cases outer <;> first | exact absurd rfl isBody | rfl
      rw [opensTag]
      intro prefixed
      have := prefixed.eq_of_length (by rw [bitTag_length, bitTag_length])
      cases outer <;> simp [bitTag, family, detail] at this

/-! ## Witnesses -/

namespace Witness

/-- A member's grant opens its own atoms' class and no other's. -/
theorem atoms_grant_selects_own :
    (bitCode 64).opens (.atomsOf 3) <+: (bitCode 64).tag (some (.atomsOf 3)) ∧
      ¬ (bitCode 64).opens (.atomsOf 3) <+: (bitCode 64).tag (some (.atomsOf 4)) ∧
      ¬ (bitCode 64).opens (.atomsOf 3) <+: (bitCode 64).tag (some .body) := by
  decide

/-- `body` opens every member's atoms and the plain body, and no annotation. -/
theorem body_selects_atoms :
    (bitCode 64).opens .body <+: (bitCode 64).tag (some (.atomsOf 3)) ∧
      (bitCode 64).opens .body <+: (bitCode 64).tag (some .body) ∧
      ¬ (bitCode 64).opens .body <+: (bitCode 64).tag (some .annotations) := by
  decide

end Witness

#assert_axioms scopeSelectsVisible
#assert_axioms scopeSelectsPath
#assert_axioms bitTag_injective
#assert_axioms Witness.atoms_grant_selects_own
#assert_axioms Witness.body_selects_atoms

end Minidregg.Kernel.PrivateCellScope
