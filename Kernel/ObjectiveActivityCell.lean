/-
# Kernel.ObjectiveActivityCell — the registry role of the kernel activity's cells

Every cell the kernel activity (`Kernel.ObjectiveActivity`) writes, other than
the Book, is one registry cell of this role (`CanonicalCellRegistry.Kind.objectiveActivity`):
an activity record, an answer slot, an object's declared state, or a published
activity package. Each holds one value:

| namespace | key    | value                                   | discipline |
|-----------|--------|-----------------------------------------|------------|
| `cell`    | `Unit` | `Payload {role, key, body}`             | RAM        |

`body` is the kernel's own framed bytes (`encodeRecord`, `AnswerSlot.encode`,
`dataBytes`, `ObjectiveBendSourceArtifact.encode`). `key` is the coordinate's
preimage, and the cell's identifier is a function of the deployment domain, the
role and the key alone (`coordinate`). The registry's loaded-and-final law is
`CellValid`: a cell of this role sits exactly at its coordinate. With
`UserShape` false for the role, no resource birth may install one, and no other
receiver selects the role, so these coordinates are protected: only the
activity receiver writes them (`Kernel.ObjectiveActivityReceiver`).
-/
import Compiler.PolicyRecordCodec
import Theory.ResourceBirth
import Theory.AssertAxioms

namespace Minidregg.Kernel.ObjectiveActivityCell

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.IndexedProgram
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
  deriving DecidableEq, Repr

def Role.tag : Role → Nat
  | .record => 0 | .slot => 1 | .state => 2 | .package => 3

def Role.ofTag : Nat → Role
  | 0 => .record | 1 => .slot | 2 => .state | _ => .package

def roleStream : StreamCodec Role :=
  StreamCodec.xmap StreamCodec.nat Role.tag Role.ofTag (by intro role; cases role <;> rfl)

/-- One activity cell: its role, the preimage of its coordinate, and the kernel's bytes. -/
structure Payload where
  role : Role
  key : List UInt8
  body : List UInt8
  deriving DecidableEq, Repr

def payloadStream : StreamCodec Payload :=
  StreamCodec.xmap (StreamCodec.product roleStream (StreamCodec.product bytesStream bytesStream))
    (fun payload => (payload.role, payload.key, payload.body))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro payload; cases payload; rfl)

/-- `DREGG.OBJECTIVE.ACTIVITY.CELL.ID/v1` -/
def idCustomization : List UInt8 := "DREGG.OBJECTIVE.ACTIVITY.CELL.ID/v1".toUTF8.toList
/-- `DREGG.OBJECTIVE.ACTIVITY.CELL.STATE/v1` -/
def rootCustomization : List UInt8 := "DREGG.OBJECTIVE.ACTIVITY.CELL.STATE/v1".toUTF8.toList

/-- The protected coordinate space. Every activity cell id is at or above
`2^256`; every id a resource birth may choose is below it
(`CanonicalCellRegistry.UserInitial`), and every id another receiver derives is a
256-bit digest. So no birth can squat an activity coordinate (a predictable
future answer slot, an object's state cell, a package cell), and no activity
write can land on another role's cell. -/
def reservedBase : Nat := 2 ^ 256

/-- The cell a role/key pair lives at, in one deployment. -/
def coordinate (domain : Digest) (role : Role) (key : List UInt8) : Nat :=
  reservedBase + (Sp800185Cshake256.hash idCustomization
    ((StreamCodec.product digestStream (StreamCodec.product roleStream bytesStream)).encode
      (domain, role, key))).digest.value

/-- Every coordinate is in the protected space. -/
theorem coordinate_reserved (domain : Digest) (role : Role) (key : List UInt8) :
    reservedBase ≤ coordinate domain role key := Nat.le_add_right _ _

/-! ## The cell: one RAM address -/

abbrev layout : Store.Layout.{0, 0, 0} where
  Namespace := Unit
  Key := fun _ => Unit
  Value := fun _ => Payload
  discipline := fun _ => .ram

def payloadAddress : Address layout := ⟨(), ()⟩

def stateOfOption : Option Payload → Store layout
  | none => 0
  | some payload => (0 : Store layout).set payloadAddress (some payload)

def payloadAt (state : Store layout) : Option Payload := state payloadAddress

@[simp] theorem payloadAt_stateOfOption (payload : Option Payload) :
    payloadAt (stateOfOption payload) = payload := by
  cases payload <;> simp [payloadAt, stateOfOption]

theorem state_ext (state : Store layout) : state = stateOfOption (payloadAt state) := by
  apply DFinsupp.ext
  rintro ⟨⟨⟩, ⟨⟩⟩
  cases present : state payloadAddress with
  | none => simp [payloadAt, stateOfOption, present]
  | some payload => simp [payloadAt, stateOfOption, present]

def wirePayloadStream := StreamCodec.product StreamCodec.nat (StreamCodec.option payloadStream)

/-- `DREGG/OBJECTIVE/ACTIVITY-CELL` -/
def wireFrame : List UInt8 := "DREGG/OBJECTIVE/ACTIVITY-CELL".toUTF8.toList

def encode (state : Store layout) : List UInt8 :=
  wireFrame ++ wirePayloadStream.encode (wireVersion, payloadAt state)

def decodeRaw (bytes : List UInt8) : Option (Store layout) :=
  if bytes.take wireFrame.length = wireFrame then do
    let (version, payload) ← wirePayloadStream.toLawful.decode (bytes.drop wireFrame.length)
    if version = wireVersion then some (stateOfOption payload) else none
  else none

@[simp] theorem decodeRaw_encode (state : Store layout) :
    decodeRaw (encode state) = some state := by
  have decoded := wirePayloadStream.toLawful.decode_encode (wireVersion, payloadAt state)
  change wirePayloadStream.toLawful.decode
    (wirePayloadStream.encode (wireVersion, payloadAt state)) =
      some (wireVersion, payloadAt state) at decoded
  simp [decodeRaw, encode, decoded, ← state_ext state]

def decode (bytes : List UInt8) : Option (Store layout) := do
  let state ← decodeRaw bytes
  if encode state = bytes then some state else none

@[simp] theorem decode_encode (state : Store layout) : decode (encode state) = some state := by
  simp [decode]

theorem decode_canonical {bytes : List UInt8} {state : Store layout}
    (accepted : decode bytes = some state) : encode state = bytes := by
  unfold decode at accepted
  cases raw : decodeRaw bytes with
  | none => simp [raw] at accepted
  | some selected =>
      simp only [raw, bind, Option.bind] at accepted
      split at accepted
      next canonical =>
        cases Option.some.inj accepted
        exact canonical
      next => contradiction

def stateCodec : LawfulCodec (Store layout) where
  encode := encode
  decode := decode
  decode_encode := decode_encode

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def materializer : Materializer layout Digest where
  codec := stateCodec
  rootBytes := rootBytes

/-- The loaded/final law: an activity cell sits at its coordinate. -/
def CellValid (domain : Digest) (cellId : Nat) (payload : Payload) : Prop :=
  cellId = coordinate domain payload.role payload.key

instance cellValidDecidable (domain : Digest) (cellId : Nat) (payload : Payload) :
    Decidable (CellValid domain cellId payload) := by
  unfold CellValid; infer_instance

/-- The materialized cell holding one payload. -/
def cellOf (payload : Payload) : Materialized materializer :=
  materialize materializer (stateOfOption (some payload))

@[simp] theorem payloadAt_cellOf (payload : Payload) :
    payloadAt (cellOf payload).logical = some payload := by
  simp [cellOf, materialize]

/-- A payload at its own coordinate is valid there. -/
theorem cellValid_coordinate (domain : Digest) (payload : Payload) :
    CellValid domain (coordinate domain payload.role payload.key) payload := rfl

#assert_axioms payloadAt_stateOfOption
#assert_axioms state_ext
#assert_axioms decodeRaw_encode
#assert_axioms decode_encode
#assert_axioms decode_canonical
#assert_axioms payloadAt_cellOf
#assert_axioms cellValid_coordinate
#assert_axioms coordinate_reserved
end Minidregg.Kernel.ObjectiveActivityCell
