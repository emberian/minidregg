/-
# Resource-scoped authority policy views

Admission privately checks the complete committed authority domain. A user
resource's law receives only the explicitly named grants relevant to its own
operation. Other resources' keys, capabilities, epochs and nullifiers are not
serialized into a predicate-readable oracle.
-/
import Compiler.CredentialAuthorityEntryCodec

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

def selfRevoked (logical : Authority) (identifier : CapabilityId) : Bool :=
  (logical ⟨.revoked, .capability identifier⟩).getD false

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
