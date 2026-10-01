/-
# Kernel.NarrowedViewHidingWitness -- the K-FIELDS leak as a theorem, and its fix

K-FIELDS' narrowed read (`RESOURCE-VIEW/v4`) carried the cell's own root, an
unsalted cSHAKE256 of the whole store encoding.  A reader restricted to field 3
therefore held a commitment to every other field, with no hiding.

The defect, on the journey's ledger (fields 1, 3 and 4 of one declared object;
the reader names field 3): two stores that agree on every address the reader
may see, and differ at field 4, give the reader byte-identical narrowed stores
— and different views, unless cSHAKE256 collides on that pair
(`narrowed_view_not_independent`).  The kernel cannot evaluate cSHAKE256, so
"the roots differ" is stated as its only alternative, a collision on two
distinct preimages; the counterexample itself (the agreement and the
difference) is decided.

The fix (`Compiler.StoreHiding`, view v5): the root is over salted per-entry
leaves keyed by the cell's blinding, and the reader receives opened entries
with their salts and only the leaves of the rest.  On the same pair, blinded,
every item the reader can open is byte-identical before and after the write to
field 4 (`narrowed_view_hides_field_four`), and what still moves is the root and
field 4's sealed leaf: the metadata channel, stated in the same theorem.
-/
import Kernel.ResourceObservationAdmission
import Compiler.StoreHiding

namespace Minidregg.Kernel.NarrowedViewHidingWitness

open Minidregg.Compiler
open Minidregg.Compiler.StoreCodec
open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ResourceObservationAdmission

set_option autoImplicit false

/-! ## The journey's ledger -/

def ledger : ResourceId .object := ⟨7⟩

def fieldAt (field : Nat) : Address effectLayout := (StateKey.objectField ledger ⟨field⟩).address

/-- Fields 1, 3 and 4 hold 0, 11 and 20 (the K-FIELDS ledger after `r-writes-1`). -/
def before : Store effectLayout :=
  (((0 : Store effectLayout).set (fieldAt 1) (some 0)).set (fieldAt 3) (some 11)).set
    (fieldAt 4) (some 20)

/-- The same ledger after the owner writes field 4. -/
def after : Store effectLayout := before.set (fieldAt 4) (some 21)

/-- The reader names field 3. -/
def reader : Option (Finset CellField) := some {.slot 3}

theorem field_four_not_kept : ¬ Kept reader (fieldOf .declaredObject) (fieldAt 4) := by
  decide

theorem field_three_kept : Kept reader (fieldOf .declaredObject) (fieldAt 3) := by
  decide

theorem fieldAt_injective {left right : Nat} (different : left ≠ right) :
    fieldAt left ≠ fieldAt right := by
  intro same
  simp [fieldAt, StateKey.address] at same
  exact different same

/-- The pair agrees on every address the reader keeps. -/
theorem covered_agree :
    narrowStore reader (fieldOf .declaredObject) after =
      narrowStore reader (fieldOf .declaredObject) before := by
  apply DFinsupp.ext
  intro address
  by_cases kept : Kept reader (fieldOf .declaredObject) address
  · rw [observe_returns_named_fields after kept, observe_returns_named_fields before kept]
    have different : address ≠ fieldAt 4 := by
      rintro rfl
      exact field_four_not_kept kept
    exact Store.set_ne before (fieldAt 4) _ address different
  · unfold narrowStore
    rw [DFinsupp.filter_apply_neg _ kept, DFinsupp.filter_apply_neg _ kept]

theorem pair_differs : after ≠ before := by
  intro same
  have atFour := congrArg (fun store : Store effectLayout => store (fieldAt 4)) same
  simp [after, before] at atFour

/-! ## The defect, on the retired scheme -/

def legacyRootCustomization : List UInt8 := "DREGG.STORE.ROOT/v1".toUTF8.toList

/-- The v4 cell root: an unsalted cSHAKE256 of the whole store encoding. -/
def legacyRoot (store : Store effectLayout) : Digest :=
  (Sp800185Cshake256.hash legacyRootCustomization
    (StoreCodec.encode DeclaredEffectCell.wire store)).digest

/-- The v4 narrowed view: the cell's own root and the narrowed store. -/
def legacyView (fields : Option (Finset CellField)) (store : Store effectLayout) :
    Digest × Store effectLayout :=
  (legacyRoot store, narrowStore fields (fieldOf .declaredObject) store)

/-- A cSHAKE256 collision between two distinct store encodings. -/
structure LegacyCollision (left right : Store effectLayout) : Prop where
  different : StoreCodec.encode DeclaredEffectCell.wire left ≠
    StoreCodec.encode DeclaredEffectCell.wire right
  rootsEqual : legacyRoot left = legacyRoot right

/-- **The defect.**  The reader's narrowed stores are equal, the stores are not,
and the v4 views are equal only if cSHAKE256 collides on the pair: the v4 view
is not independent of field 4, which the reader may not read. -/
theorem narrowed_view_not_independent :
    narrowStore reader (fieldOf .declaredObject) after =
        narrowStore reader (fieldOf .declaredObject) before ∧
      after ≠ before ∧
      (legacyView reader after = legacyView reader before → LegacyCollision after before) :=
  ⟨covered_agree, pair_differs, fun same =>
    ⟨fun encoded => pair_differs (encode_injective DeclaredEffectCell.wire encoded),
      congrArg Prod.fst same⟩⟩

/-! ## The fix, on the same pair -/

/-- A blinding (a concrete stand-in: the theorem is about structure, and the
deployed one is a 256-bit value derived by the owner's client). -/
def blinding : Int := 271828182845904523536

def blinded (store : Store effectLayout) : Store effectLayout :=
  store.set StateKey.blinding.address (some blinding)

theorem blinding_not_field_four : DeclaredEffectCell.wire.blinding ≠ some (fieldAt 4) := by
  decide

/-- **The fix.**  Under view v5 every item the field-3 reader can open is
byte-identical before and after the owner's write to field 4; what moves is
the root (unless cSHAKE256 collides) — the reader learns that something it may
not read changed, and nothing of what. -/
theorem narrowed_view_hides_field_four :
    StoreHiding.opened DeclaredEffectCell.wire (Visible reader .declaredObject)
        ((blinded before).set (fieldAt 4) (some 21)) =
      StoreHiding.opened DeclaredEffectCell.wire (Visible reader .declaredObject) (blinded before) ∧
    (saltedRoot DeclaredEffectCell.wire ((blinded before).set (fieldAt 4) (some 21)) ≠
        saltedRoot DeclaredEffectCell.wire (blinded before) ∨
      RootCollision DeclaredEffectCell.wire ((blinded before).set (fieldAt 4) (some 21))
        (blinded before) ∨
      ∃ first ∈ (entries DeclaredEffectCell.wire
            ((blinded before).set (fieldAt 4) (some 21))).map
          (opening DeclaredEffectCell.wire ((blinded before).set (fieldAt 4) (some 21))),
        ∃ second ∈ (entries DeclaredEffectCell.wire (blinded before)).map
          (opening DeclaredEffectCell.wire (blinded before)), LeafCollision first second) := by
  apply StoreHiding.change_detection_only_via_root
  · exact fun visible => field_four_not_kept visible.1
  · exact blinding_not_field_four
  · show (blinded before) (fieldAt 4) = some 20
    have different : fieldAt 4 ≠ StateKey.blinding.address := by decide
    simp [blinded, before, Store.set_ne _ _ _ _ different]
  · decide

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.NarrowedViewHidingWitness.narrowed_view_not_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms narrowed_view_not_independent
/-- info: 'Minidregg.Kernel.NarrowedViewHidingWitness.narrowed_view_hides_field_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms narrowed_view_hides_field_four

end Minidregg.Kernel.NarrowedViewHidingWitness
