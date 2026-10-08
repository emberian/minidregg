/- Constructed absence-shape poles for the deployed bridge/history.
These are finite intent-level witnesses, not signed receiver admission evidence.
The journey replay pole supplies receiving-path evidence. Cell IDs are small
stand-ins for the hash-derived object/state/package/domain coordinates. -/
import Kernel.DeployedHistory
import Kernel.ObjectiveActivityWire
import Kernel.ObjectiveDomain

namespace Minidregg.Kernel.ObjectiveTurnTotality

open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.World
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Kernel.DurableDataIntent (DataIntent)
open Minidregg.Kernel.ObjectiveActivityWire (Post Seal intentOf)
open Minidregg.Compiler

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Minimal whole-blob images for the roles in the two absence shapes. -/
def payloadCell (role : ObjectiveActivityCell.Role) : Cell deployedR :=
  ⟨.objectiveActivity, ProtectedCell.stateOfOption ObjectiveActivityCell.spec
    (some ⟨role, [], []⟩)⟩

/-- Package cell 3 is present; object 1 and state 2 are fresh. -/
def preWorld : World deployedR DurableDataIntent.TransactionId Digest :=
  ⟨(0 : Cells deployedR).update 3 (some (payloadCell .package)), 0⟩

/-- The receiver's exact storage model: sum of full post image lengths. -/
def sealing : Seal where
  guards := []
  nullifiers := []
  event := ⟨1, ⟨0⟩, ⟨0⟩, []⟩
  subject := none
  charge posts guards := fun lane => match lane with
    | .incidences => 1
    | .memoryTouches => posts.length + guards.length
    | .storageBytes => (posts.map fun p => p.bytes.length).sum
    | _ => 0

def post (id : Nat) (role : ObjectiveActivityCell.Role) : Post :=
  ⟨⟨id⟩, ResourceBirthCodec.rootBytes [], encodeCell (some (payloadCell role))⟩

/-- Row 11 shape: an object record is born with no state post; both package
and still-absent state are guarded by the actual shared intent constructor. -/
def seedlessCreateIntent : DataIntent ResourceBirthCodec.rootBytes :=
  intentOf ResourceBirthCodec.rootBytes ⟨11⟩ [post 1 .object]
    [⟨⟨3⟩, ResourceBirthCodec.rootBytes (encodeCell (some (payloadCell .package)))⟩,
     ⟨⟨2⟩, ResourceBirthCodec.rootBytes []⟩] [] sealing

/-- Row 10 shape: registering a domain writes its record and a member's
record while guarding that member's legal absent state. -/
def statelessDomainIntent : DataIntent ResourceBirthCodec.rootBytes :=
  intentOf ResourceBirthCodec.rootBytes ⟨10⟩ [post 4 .domain, post 1 .object]
    [⟨⟨2⟩, ResourceBirthCodec.rootBytes []⟩] [] sealing

/-- No zero-storage history: the deployed value-byte charge accepts row 11. -/
theorem seedless_create_is_turn :
    (Turn.ofIntent bridge DeployedHistory.history preWorld seedlessCreateIntent).isOk = true := by
  decide +kernel

/-- The absent state guard survives the derivation as an absence pin. -/
theorem seedless_create_pins_state :
    (Turn.ofIntent bridge DeployedHistory.history preWorld seedlessCreateIntent).toOption.map
      (·.absent) = some [2] := by
  decide +kernel

/-- Stateless members contribute no joint state slots, as the OB domain permits. -/
theorem stateless_member_joint_slots : ObjectiveActivity.jointSlots 0 [none] = some [] := rfl

/-- The deployed bridge and nonzero charge model accept the row 10 shape. -/
theorem stateless_domain_member_is_turn :
    (Turn.ofIntent bridge DeployedHistory.history preWorld statelessDomainIntent).isOk = true := by
  decide +kernel

theorem stateless_domain_member_pins_state :
    (Turn.ofIntent bridge DeployedHistory.history preWorld statelessDomainIntent).toOption.map
      (·.absent) = some [2] := by
  decide +kernel

/-- Permanent retirement is not fresh absence. -/
theorem retired_state_guard_refused :
    refusalOf (ofCells bridge DeployedHistory.history (fun c => preWorld.cells c)
      (fun c => c == 2) seedlessCreateIntent) = some (.retiredCell 2) := by
  decide +kernel

#assert_axioms seedless_create_is_turn seedless_create_pins_state
#assert_axioms stateless_member_joint_slots stateless_domain_member_is_turn
#assert_axioms stateless_domain_member_pins_state retired_state_guard_refused

end Minidregg.Kernel.ObjectiveTurnTotality
