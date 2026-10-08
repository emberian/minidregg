/-
# Kernel.ObjectiveActivityCell — the registry role of the kernel activity cells

Every cell the kernel activity (`Kernel.ObjectiveActivity`) writes, other than
the Book, is one registry cell of this kind (`CanonicalCellRegistry.Kind.objectiveActivity`):
an activity record, an answer slot, an object declared state, a published
activity package, an object record or an inbox, built by the one protected-cell construction
(`Kernel.ProtectedCell`, this family's `spec`). `body` is the kernel's own
framed bytes (`encodeRecord`, `AnswerSlot.encode`, `dataBytes`,
`ObjectiveBendSourceArtifact.encode`). With `UserShape` false for the kind, no
resource birth may install one, and every other source facet's intents are refused
by name if they write any coordinate at or above `reservedBase`
(`Kernel.ObjectiveActivityGate.ordinaryGate`, `protectedWrite`): only the kernel
activity's own typed turns write them (`Kernel.ObjectiveActivityReceiver` under
`ControlFacet.objectiveActivity`).
-/
import Kernel.ProtectedCell

namespace Minidregg.Kernel.ObjectiveActivityCell

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- Registry tag 19 (after 17 worldKind, 18 worldInstance); schema 91018. -/
def registryTag : UInt8 := 19
def schemaId : Nat := 91018
def wireVersion : Nat := 1

inductive Role where
  | record
  | slot
  | state
  | package
  /-- An object's record (`Kernel.ObjectRecord`): pin, law, upgrade policy, payer. -/
  | object
  /-- A per-(sender, target) message queue (`Kernel.Inbox`). -/
  | inbox
  /-- An invariant domain (`Kernel.ObjectiveDomain`): members and joint law. -/
  | domain
  deriving DecidableEq, Repr

def Role.tag : Role → Nat
  | .record => 0 | .slot => 1 | .state => 2 | .package => 3 | .object => 4 | .inbox => 5 | .domain => 6

def Role.ofTag : Nat → Role
  | 0 => .record | 1 => .slot | 2 => .state | 3 => .package | 4 => .object | 5 => .inbox | _ => .domain

def roleStream : StreamCodec Role :=
  StreamCodec.xmap StreamCodec.nat Role.tag Role.ofTag (by intro role; cases role <;> rfl)

/-- The activity family: `DREGG.OBJECTIVE.ACTIVITY.CELL.ID/v1`,
`DREGG.OBJECTIVE.ACTIVITY.CELL.STATE/v1`, frame `DREGG/OBJECTIVE/ACTIVITY-CELL`. -/
abbrev spec : ProtectedCell.Spec where
  Role := Role
  roleStream := roleStream
  idCustomization := "DREGG.OBJECTIVE.ACTIVITY.CELL.ID/v1".toUTF8.toList
  rootCustomization := "DREGG.OBJECTIVE.ACTIVITY.CELL.STATE/v1".toUTF8.toList
  wireFrame := "DREGG/OBJECTIVE/ACTIVITY-CELL".toUTF8.toList
  wireVersion := wireVersion

abbrev Payload := ProtectedCell.Payload spec
abbrev payloadStream : StreamCodec Payload := ProtectedCell.payloadStream spec
abbrev reservedBase : Nat := ProtectedCell.reservedBase
abbrev coordinate (domain : Digest) (role : Role) (key : List UInt8) : Nat :=
  ProtectedCell.coordinate spec domain role key
theorem coordinate_reserved (domain : Digest) (role : Role) (key : List UInt8) :
    reservedBase ≤ coordinate domain role key := ProtectedCell.coordinate_reserved spec domain role key
abbrev layout : Store.Layout.{0, 0, 0} := ProtectedCell.layout spec
abbrev payloadAt (state : Store layout) : Option Payload := ProtectedCell.payloadAt spec state
abbrev materializer : Materializer layout Digest := ProtectedCell.materializer spec
abbrev CellValid (domain : Digest) (cellId : Nat) (payload : Payload) : Prop :=
  ProtectedCell.CellValid spec domain cellId payload
abbrev cellOf (payload : Payload) : Materialized materializer := ProtectedCell.cellOf spec payload

end Minidregg.Kernel.ObjectiveActivityCell
