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

* `scopeSelectsVisible_checked`: at `bitCode 256`, with the fitting premises
  replaced by the private index's admission check (`addressFits`: a declared key's
  digests below `2^256`; content and streams always fit) and the reader's scope cut
  to its fitting fields (`fitScope`, which changes no fitting address's
  visibility). Teeth: `Witness.slot_overflow_shares_tag`.

Owed: the address-path half of the keys.
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

/-! ## Fitting at the digest width

`bitCode W` is exact only on fields whose parameters are below `2^W`; above it
two fields share a tag (`Witness.slot_overflow_shares_tag`). Content atoms always
fit at `W ≥ 64` (`atomLow` is the low 64 bits). A declared key's digests are
unbounded on the wire (`digestCodec`'s escape form), so the private index admits
a declared key only when `keyFits` holds: the gate the blinded-cell receiver
applies before a write enters the index. A reader's scope is cut to its fitting
fields (`fitScope`), which changes nothing it sees at a fitting address. -/

open Minidregg.Theory.EffectDeclaration (StateKey)

/-- A declared key's digests are below `2^w`. -/
def keyFits (w : Nat) : StateKey → Bool
  | .objectField _ field => decide (field.value < 2 ^ w)
  | .accountBalance _ asset => decide (asset.value < 2 ^ w)
  | .fieldDeclared _ field => decide (field.value < 2 ^ w)
  | _ => true

theorem declaredField_fits {w : Nat} {key : StateKey} (fits : keyFits w key = true) :
    bitFits w (declaredField key) := by
  cases key <;> simp_all [keyFits, declaredField, bitFits]

theorem contentField_fits (w : Nat) (space : Minidregg.Theory.Hyperdocument.Namespace) :
    bitFits w (contentField space) := by
  cases space <;> trivial

instance bitFitsDecidable (w : Nat) : DecidablePred (bitFits w) := fun f => by
  cases f <;> unfold bitFits <;> infer_instance

instance (w : Nat) : DecidablePred (bitCode w).Fits := bitFitsDecidable w

/-- The private index's admission check on one address of a registry cell. -/
def addressFits (w : Nat) : (kind : CanonicalCellRegistry.Kind) →
    Address (CanonicalCellRegistry.layout kind) → Bool
  | .declaredObject, address | .accountMetadata, address | .declaredProgram, address =>
      keyFits w address.2
  | _, _ => true

/-- **A checked address fits** `bitCode w` for every `w ≥ 64`. -/
theorem fits_of_addressFits {w : Nat} (wide : 64 ≤ w) (kind : CanonicalCellRegistry.Kind)
    (address : Address (CanonicalCellRegistry.layout kind)) (checked : addressFits w kind address = true) :
    ∀ f, fieldOf kind address = some f → (bitCode w).Fits f := by
  intro f found
  show bitFits w f
  cases kind with
  | content =>
      simp only [fieldOf] at found
      split at found
      · cases found
      · cases found
        unfold contentFieldAt
        split
        · show ContentResource.atomLow _ < 2 ^ w
          exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by decide) wide)
        · exact contentField_fits w _
  | declaredObject | accountMetadata | declaredProgram =>
      simp only [fieldOf] at found
      split at found
      · cases found
      · cases found
        exact declaredField_fits checked
  | stream | worldKind =>
      simp only [fieldOf] at found
      cases found
      trivial
  | _ => simp [fieldOf] at found

/-- A scope cut to its fields that fit `bitCode w`. -/
noncomputable def fitScope (w : Nat) : Option (Finset CellField) → Option (Finset CellField)
  | none => none
  | some named => some (named.filter (bitFits w))

theorem fitScope_fits (w : Nat) (fields : Option (Finset CellField)) :
    ScopeFits (bitCode w) (fitScope w fields) := by
  cases fields with
  | none => trivial
  | some named =>
      intro f member
      exact (Finset.mem_filter.mp member).2

/-- Cutting a scope to its fitting fields keeps every fitting address's visibility. -/
theorem visible_fitScope (w : Nat) (fields : Option (Finset CellField)) (kind : CanonicalCellRegistry.Kind)
    (address : Address (CanonicalCellRegistry.layout kind))
    (addressFits : ∀ f, fieldOf kind address = some f → bitFits w f) :
    Visible (fitScope w fields) kind address ↔ Visible fields kind address := by
  unfold Visible Kept
  cases fields with
  | none => rfl
  | some named =>
      simp only [fitScope]
      split
      · rename_i f found
        simp only [CellField.NamedBy, Finset.mem_filter]
        constructor
        · rintro ⟨⟨outer, ⟨member, _⟩, covers⟩, nb⟩
          exact ⟨⟨outer, member, covers⟩, nb⟩
        · rintro ⟨⟨outer, member, covers⟩, nb⟩
          refine ⟨⟨outer, ⟨member, ?_⟩, covers⟩, nb⟩
          by_cases isBody : outer = .body
          · subst isBody; trivial
          · rw [CellField.covers_eq_of_ne_body isBody covers]
            exact addressFits f found
      · simp

/-- **Scope selection under the admission check**, at the digest width: for every
reader scope, an address the private index admitted (`addressFits 256`, not the
blinding) is visible exactly when one of the cut scope's prefixes starts its tag. -/
theorem scopeSelectsVisible_checked (kind : CanonicalCellRegistry.Kind) (fields : Option (Finset CellField))
    (address : Address (CanonicalCellRegistry.layout kind)) (checked : addressFits 256 kind address = true)
    (notBlinding : CanonicalCellRegistry.isBlinding kind address = false) :
    Visible fields kind address ↔
      ∃ p ∈ scopePrefixes (bitCode 256) (fitScope 256 fields), p <+: (bitCode 256).tag (fieldOf kind address) := by
  have fits := fits_of_addressFits (by decide) kind address checked
  rw [← visible_fitScope 256 fields kind address fits]
  exact scopeSelectsVisible (bitCode 256) kind (fitScope 256 fields) address (fitScope_fits 256 fields) fits notBlinding

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

/-- The width bound has teeth: past it, two slots share a tag, so a reader of
slot `0` would be shown slot `2^256`. -/
theorem slot_overflow_shares_tag :
    (bitCode 256).tag (some (.slot (2 ^ 256))) = (bitCode 256).tag (some (.slot 0)) ∧
      CellField.slot (2 ^ 256) ≠ .slot 0 := by
  refine ⟨?_, by simp⟩
  have low : ∀ i ∈ List.range 256, (2 ^ 256).testBit i = Nat.testBit 0 i := by
    intro i member
    have := List.mem_range.mp member
    rw [Nat.testBit_two_pow, Nat.zero_testBit]
    simp only [decide_eq_false_iff_not]
    omega
  show bitTag 256 _ = bitTag 256 _
  simp only [bitTag, detail, bitsW, family, List.map_congr_left low]

/-- The check refuses such a key. -/
theorem overflow_refused : ∀ object, keyFits 256 (.objectField object ⟨2 ^ 256⟩) = false := by
  intro object
  simp [keyFits]

end Witness

#assert_axioms scopeSelectsVisible
#assert_axioms scopeSelectsPath
#assert_axioms bitTag_injective
#assert_axioms Witness.atoms_grant_selects_own
#assert_axioms Witness.body_selects_atoms
#assert_axioms fits_of_addressFits
#assert_axioms visible_fitScope
#assert_axioms scopeSelectsVisible_checked
#assert_axioms Witness.slot_overflow_shares_tag
#assert_axioms Witness.overflow_refused

end Minidregg.Kernel.PrivateCellScope
