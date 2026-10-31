/-
# Resource-scoped authority policy views

Admission privately checks the complete committed authority domain. A user
resource's law receives only the explicitly named grants relevant to its own
operation. Other resources' keys, capabilities, epochs and nullifiers are not
serialized into a predicate-readable oracle.
-/
module

public import Compiler.CredentialAuthorityEntryCodec

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Compiler.ResourceAuthorityProjection

open Minidregg.Theory
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Store

set_option autoImplicit false

abbrev Authority := Store CredentialAuthorityState.layout

def bytesSlots (stem : String) : Nat → List UInt8 → List (String × Int)
  | _, [] => []
  | index, byte :: rest => (s!"{stem}/{index}", Int.ofNat byte.toNat) :: bytesSlots stem (index + 1) rest

/-! ### Demanded byte blocks

A law reads a projection's per-byte slots only by name; a block no demanded name can reach is
never encoded (`bytesSlotsDemanded`, `bytesSlotsDemanded_filter`). -/

/-- `p` occurs in a list of characters. -/
def infixB (p : List Char) : List Char → Bool
  | [] => p.isEmpty
  | l@(_ :: rest) => p.isPrefixOf l || infixB p rest

theorem infixB_append (p : List Char) : ∀ (a b : List Char), infixB p (a ++ (p ++ b)) = true
  | [], b => by
      cases h : p ++ b with
      | nil =>
          have empty : p = [] := (List.append_eq_nil_iff.mp h).1
          simp [infixB, empty]
      | cons c rest =>
          simp only [List.nil_append, h, infixB]
          rw [← h]
          simp [(List.isPrefixOf_iff_prefix).mpr (List.prefix_append p b)]
  | c :: a, b => by
      simp only [List.cons_append, infixB, infixB_append p a b, Bool.or_true]

/-- Whether some demanded name contains `stem`: every slot name of a `stem` byte block, under any
key prefix, does. -/
def demandsStem (keys : List String) (stem : String) : Bool :=
  keys.any fun key => infixB stem.toList key.toList

theorem bytesSlots_names (stem : String) :
    ∀ (offset : Nat) (bytes : List UInt8) (slot : String × Int),
      slot ∈ bytesSlots stem offset bytes → ∃ rest : List Char, slot.1.toList = stem.toList ++ rest
  | _, [], _, member => by simp [bytesSlots] at member
  | offset, byte :: bytes, slot, member => by
      simp only [bytesSlots, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨(toString "/").toList ++ (toString offset).toList,
          by simp only [String.toList_append, List.append_assoc]; rfl⟩
      · exact bytesSlots_names stem (offset + 1) bytes slot member

/-- A byte block no demanded name can reach filters to nothing, under any key prefix. -/
theorem bytesSlots_filter_undemanded (pfx stem : String) (keys : List String)
    (offset : Nat) (bytes : List UInt8) (undemanded : demandsStem keys stem = false) :
    (bytesSlots stem offset bytes).filter (fun slot => keys.contains (pfx ++ slot.1)) = [] := by
  refine List.filter_eq_nil_iff.mpr fun slot member contains => ?_
  obtain ⟨rest, named⟩ := bytesSlots_names stem offset bytes slot member
  have reached : demandsStem keys stem = true := by
    refine List.any_eq_true.mpr ⟨pfx ++ slot.1, by simpa using contains, ?_⟩
    rw [String.toList_append, named]
    exact infixB_append stem.toList pfx.toList rest
  rw [undemanded] at reached
  exact Bool.false_ne_true reached

/-- A `stem` byte block, encoded only when a demanded name can be one of its slots. -/
def bytesSlotsDemanded (keys : List String) (stem : String) (bytes : Unit → List UInt8) :
    List (String × Int) :=
  if demandsStem keys stem then bytesSlots stem 0 (bytes ()) else []

theorem bytesSlotsDemanded_filter (keys : List String) (pfx stem : String)
    (bytes : Unit → List UInt8) :
    (bytesSlotsDemanded keys stem bytes).filter (fun slot => keys.contains (pfx ++ slot.1)) =
      (bytesSlots stem 0 (bytes ())).filter (fun slot => keys.contains (pfx ++ slot.1)) := by
  unfold bytesSlotsDemanded
  cases gate : demandsStem keys stem with
  | true => rfl
  | false => rw [bytesSlots_filter_undemanded pfx stem keys 0 _ gate]; rfl

theorem bytesSlotsDemanded_restrict (keys : List String) (stem : String) (bytes : Unit → List UInt8) :
    (bytesSlotsDemanded keys stem bytes).filter (fun slot => keys.contains slot.1) =
      (bytesSlots stem 0 (bytes ())).filter (fun slot => keys.contains slot.1) := by
  simpa using bytesSlotsDemanded_filter keys "" stem bytes

def selfRevoked (logical : Authority) (identifier : CapabilityId) : Bool :=
  (logical ⟨.revoked, .capability identifier⟩).isSome

/-- Both fields are selected by literal source-derived identifiers. Absence
remains visible as absence, not a fabricated grant or an implicit all-zero key.
The revoked slot reports this grant's own revocation key, not a claim that all
lineage, epoch, caveat or expiry checks passed; those remain admission gates. -/
def grantSlots (stem : String) (kind : ResourceKind) (identifier : CapabilityId)
    (logical : Authority) : List (String × Int) :=
  let capability := logical ⟨.capability kind, identifier⟩
  let revoked := selfRevoked logical identifier
  [(s!"{stem}/present", if capability.isSome then 1 else 0),
   (s!"{stem}/revoked", if revoked = true then 1 else 0)] ++
    bytesSlots (stem ++ "/bytes") 0
      ((StreamCodec.option (CredentialAuthorityEntryCodec.storedCapabilityStream kind)).encode capability)

/-- Framing law: every unselected authority coordinate can differ, including
all unrelated resource grants and signing keys, without changing these slots. -/
theorem grantSlots_noninterference (stem : String) (kind : ResourceKind) (identifier : CapabilityId)
    (left right : Authority)
    (sameGrant : left ⟨.capability kind, identifier⟩ = right ⟨.capability kind, identifier⟩)
    (sameRevocation : left ⟨.revoked, .capability identifier⟩ =
      right ⟨.revoked, .capability identifier⟩) :
    grantSlots stem kind identifier left = grantSlots stem kind identifier right := by
  simp only [grantSlots, selfRevoked, sameGrant, sameRevocation]
  rfl

/-- Even a concrete mutation at an unselected coordinate is invisible to a
resource policy. This includes unrelated private signing-key and grant data. -/
theorem grantSlots_write_unselected (stem : String) (kind : ResourceKind) (identifier : CapabilityId)
    (logical : Authority) (address : Address CredentialAuthorityState.layout)
    (value : Option (CredentialAuthorityState.layout.Value address.1))
    (notGrant : address ≠ ⟨.capability kind, identifier⟩)
    (notRevocation : address ≠ ⟨.revoked, .capability identifier⟩) :
    grantSlots stem kind identifier (logical.set address value) =
      grantSlots stem kind identifier logical := by
  apply grantSlots_noninterference
  · exact Store.set_ne logical address value _ (Ne.symm notGrant)
  · exact Store.set_ne logical address value _ (Ne.symm notRevocation)

/-- These named scalar statuses come from the selected canonical fields. -/
theorem grantSlots_status (stem : String) (kind : ResourceKind) (identifier : CapabilityId)
    (logical : Authority) :
    (grantSlots stem kind identifier logical).take 2 =
      [(s!"{stem}/present", if (logical ⟨.capability kind, identifier⟩).isSome then 1 else 0),
       (s!"{stem}/revoked", if selfRevoked logical identifier = true then 1 else 0)] := by
  simp [grantSlots]

/-- info: 'Minidregg.Compiler.ResourceAuthorityProjection.grantSlots_noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grantSlots_noninterference

/-- info: 'Minidregg.Compiler.ResourceAuthorityProjection.grantSlots_write_unselected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grantSlots_write_unselected

/-- info: 'Minidregg.Compiler.ResourceAuthorityProjection.grantSlots_status' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grantSlots_status

end Minidregg.Compiler.ResourceAuthorityProjection
