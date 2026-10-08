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

/-- A birth which immediately ends posts a tombstone at its fresh record ID. -/
def freshRetirementIntent : DataIntent ResourceBirthCodec.rootBytes :=
  intentOf ResourceBirthCodec.rootBytes ⟨12⟩
    [⟨⟨1⟩, ResourceBirthCodec.rootBytes [],
      ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry .retired⟩]
    [] [] sealing

/-- The pre-fix codec has no carrier kind and refuses this real post shape. -/
theorem fresh_retirement_without_carrier_refused :
    refusalOf (Turn.ofIntent { bridge with codec.retirementKind := none }
      DeployedHistory.history preWorld freshRetirementIntent) = some (.retireAbsent 1) := by
  decide +kernel

/-- The deployed codec burns the fresh ID by creating it empty and retiring it atomically. -/
theorem fresh_retirement_is_turn :
    (Turn.ofIntent bridge DeployedHistory.history preWorld freshRetirementIntent).isOk = true := by
  decide +kernel

theorem fresh_retirement_creates_and_retires :
    (Turn.ofIntent bridge DeployedHistory.history preWorld freshRetirementIntent).toOption.map
      (fun t => (t.creates.map Prod.fst, t.retires, t.charge .storageBytes)) =
      some ([1], [1], 0) := by
  decide +kernel

/-- Even a burn cannot reuse an already retired identifier. -/
theorem fresh_retirement_reuse_refused :
    refusalOf (ofCells bridge DeployedHistory.history (fun c => preWorld.cells c)
      (fun c => c == 1) freshRetirementIntent) = some (.retiredCell 1) := by
  decide +kernel

/-- A funded pre-world for executing the fresh retirement, not just deriving it. -/
def burnWorld : World deployedR DurableDataIntent.TransactionId Digest :=
  { preWorld with
    system := Store.set (Store.set (Store.set (genesisSystem DeployedHistory.history)
        ⟨SysSpace.allowance, .incidences⟩ (some (10 : Nat)))
        ⟨SysSpace.allowance, .memoryTouches⟩ (some (10 : Nat)))
        ⟨SysSpace.allowance, .storageBytes⟩ (some (10 : Nat)) }

/-- The fresh tombstone is an actual World step and records permanent retirement. -/
theorem fresh_retirement_steps_permanently :
    ∃ t w', Turn.ofIntent bridge DeployedHistory.history burnWorld freshRetirementIntent = .ok t ∧
      World.step DeployedHistory.history burnWorld t = some w' ∧
      w'.cells 1 = none ∧ w'.retired 1 = some () := by
  have ok : (Turn.ofIntent bridge DeployedHistory.history burnWorld freshRetirementIntent).isOk = true := by
    decide +kernel
  cases hd : Turn.ofIntent bridge DeployedHistory.history burnWorld freshRetirementIntent with
  | error r => rw [hd] at ok; change false = true at ok; cases ok
  | ok t =>
      obtain ⟨w', step, _, _⟩ := ofIntent_step bridge DeployedHistory.history hd
        (show burnWorld.head = some (0, ⟨0⟩) from rfl)
        (show burnWorld.journal freshRetirementIntent.transactionId = none from rfl)
        (by decide +kernel)
        (by intro n hn; simp [freshRetirementIntent, intentOf, sealing] at hn)
        (by intro lane ne; cases lane <;> decide +kernel)
        (by decide +kernel)
      have names : (Turn.ofIntent bridge DeployedHistory.history burnWorld freshRetirementIntent).toOption.map
          (·.retires) = some [1] := by decide +kernel
      rw [hd] at names
      have member : 1 ∈ t.retires := by
        have eq : t.retires = [1] := Option.some.inj names
        simp [eq]
      exact ⟨t, w', rfl, step, step_retire DeployedHistory.history step 1 member⟩

#assert_axioms fresh_retirement_steps_permanently

#assert_axioms fresh_retirement_without_carrier_refused fresh_retirement_is_turn
#assert_axioms fresh_retirement_creates_and_retires fresh_retirement_reuse_refused

#assert_axioms seedless_create_is_turn seedless_create_pins_state
#assert_axioms stateless_member_joint_slots stateless_domain_member_is_turn
#assert_axioms stateless_domain_member_pins_state retired_state_guard_refused

end Minidregg.Kernel.ObjectiveTurnTotality
