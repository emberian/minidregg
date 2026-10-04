/-
# Kernel.ProtectedCell — a kernel role's cells at protected coordinates

A kernel family whose cells no user may install (the kernel activity,
`Kernel.ObjectiveActivityCell`; seats and invitations, `Kernel.SeatCell`) keeps
each of its cells as one registry cell of its own kind holding one value:

| namespace | key    | value                                   | discipline |
|-----------|--------|-----------------------------------------|------------|
| `cell`    | `Unit` | `Payload {role, key, body}`             | RAM        |

`body` is the family's own framed bytes; `key` is the coordinate's preimage, and
the cell's identifier is a function of the deployment domain, the role and the
key alone (`coordinate`). The registry's loaded-and-final law for such a kind is
`CellValid`: a cell sits exactly at its coordinate. Every coordinate is at or
above `reservedBase = 2^256`, and every id a resource birth may choose is below it
(`CanonicalCellRegistry.UserInitial`), so no birth can squat one.

This module is the one construction; each family is a `Spec` (its role type,
role codec and customization strings). Two families' coordinates are distinct
unless cSHAKE256 collides on two preimages that differ in their customization
string, a collision bound, not a check.
-/
import Compiler.PolicyRecordCodec
import Theory.ResourceBirth
import Theory.AssertAxioms

namespace Minidregg.Kernel.ProtectedCell

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- One protected family: its roles and its domain-separation strings. -/
structure Spec where
  Role : Type
  [roleDecEq : DecidableEq Role]
  roleStream : StreamCodec Role
  /-- The cSHAKE customization of the coordinate. -/
  idCustomization : List UInt8
  /-- The cSHAKE customization of the cell root. -/
  rootCustomization : List UInt8
  /-- The frame of the cell's store bytes. -/
  wireFrame : List UInt8
  wireVersion : Nat

attribute [instance] Spec.roleDecEq

variable (spec : Spec)

/-- One protected cell: its role, the preimage of its coordinate, and the family's bytes. -/
structure Payload where
  role : spec.Role
  key : List UInt8
  body : List UInt8
  deriving DecidableEq

def payloadStream : StreamCodec (Payload spec) :=
  StreamCodec.xmap (StreamCodec.product spec.roleStream (StreamCodec.product bytesStream bytesStream))
    (fun payload => (payload.role, payload.key, payload.body))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro payload; cases payload; rfl)

/-- The protected coordinate space: every protected cell id is at or above
`2^256`; every id a resource birth may choose is below it. -/
def reservedBase : Nat := 2 ^ 256

/-- The cell a role/key pair lives at, in one deployment. -/
def coordinate (domain : Digest) (role : spec.Role) (key : List UInt8) : Nat :=
  reservedBase + (Sp800185Cshake256.hash spec.idCustomization
    ((StreamCodec.product digestStream (StreamCodec.product spec.roleStream bytesStream)).encode
      (domain, role, key))).digest.value

/-- Every coordinate is in the protected space. -/
theorem coordinate_reserved (domain : Digest) (role : spec.Role) (key : List UInt8) :
    reservedBase ≤ coordinate spec domain role key := Nat.le_add_right _ _

/-! ## The cell: one RAM address -/

abbrev layout : Store.Layout.{0, 0, 0} where
  Namespace := Unit
  Key := fun _ => Unit
  Value := fun _ => Payload spec
  discipline := fun _ => .ram

def payloadAddress : Address (layout spec) := ⟨(), ()⟩

def stateOfOption : Option (Payload spec) → Store (layout spec)
  | none => 0
  | some payload => (0 : Store (layout spec)).set (payloadAddress spec) (some payload)

def payloadAt (state : Store (layout spec)) : Option (Payload spec) := state (payloadAddress spec)

@[simp] theorem payloadAt_stateOfOption (payload : Option (Payload spec)) :
    payloadAt spec (stateOfOption spec payload) = payload := by
  cases payload <;> simp [payloadAt, stateOfOption]

theorem state_ext (state : Store (layout spec)) : state = stateOfOption spec (payloadAt spec state) := by
  apply DFinsupp.ext
  rintro ⟨⟨⟩, ⟨⟩⟩
  cases present : state (payloadAddress spec) with
  | none => simp [payloadAt, stateOfOption, present]
  | some payload => simp [payloadAt, stateOfOption, present]

def wirePayloadStream := StreamCodec.product StreamCodec.nat (StreamCodec.option (payloadStream spec))

def encode (state : Store (layout spec)) : List UInt8 :=
  spec.wireFrame ++ (wirePayloadStream spec).encode (spec.wireVersion, payloadAt spec state)

def decodeRaw (bytes : List UInt8) : Option (Store (layout spec)) :=
  if bytes.take spec.wireFrame.length = spec.wireFrame then do
    let (version, payload) ← (wirePayloadStream spec).toLawful.decode (bytes.drop spec.wireFrame.length)
    if version = spec.wireVersion then some (stateOfOption spec payload) else none
  else none

@[simp] theorem decodeRaw_encode (state : Store (layout spec)) :
    decodeRaw spec (encode spec state) = some state := by
  have decoded := (wirePayloadStream spec).toLawful.decode_encode (spec.wireVersion, payloadAt spec state)
  change (wirePayloadStream spec).toLawful.decode
    ((wirePayloadStream spec).encode (spec.wireVersion, payloadAt spec state)) =
      some (spec.wireVersion, payloadAt spec state) at decoded
  simp [decodeRaw, encode, decoded, ← state_ext spec state]

def decode (bytes : List UInt8) : Option (Store (layout spec)) := do
  let state ← decodeRaw spec bytes
  if encode spec state = bytes then some state else none

@[simp] theorem decode_encode (state : Store (layout spec)) : decode spec (encode spec state) = some state := by
  simp [decode]

theorem decode_canonical {bytes : List UInt8} {state : Store (layout spec)}
    (accepted : decode spec bytes = some state) : encode spec state = bytes := by
  unfold decode at accepted
  cases raw : decodeRaw spec bytes with
  | none => simp [raw] at accepted
  | some selected =>
      simp only [raw, bind, Option.bind] at accepted
      split at accepted
      next canonical =>
        cases Option.some.inj accepted
        exact canonical
      next => contradiction

def stateCodec : LawfulCodec (Store (layout spec)) where
  encode := encode spec
  decode := decode spec
  decode_encode := decode_encode spec

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash spec.rootCustomization bytes).digest

def materializer : Materializer (layout spec) Digest where
  codec := stateCodec spec
  rootBytes := rootBytes spec

/-- The loaded/final law: a protected cell sits at its coordinate. -/
def CellValid (domain : Digest) (cellId : Nat) (payload : Payload spec) : Prop :=
  cellId = coordinate spec domain payload.role payload.key

instance cellValidDecidable (domain : Digest) (cellId : Nat) (payload : Payload spec) :
    Decidable (CellValid spec domain cellId payload) := by
  unfold CellValid; infer_instance

/-- The materialized cell holding one payload. -/
def cellOf (payload : Payload spec) : Materialized (materializer spec) :=
  materialize (materializer spec) (stateOfOption spec (some payload))

@[simp] theorem payloadAt_cellOf (payload : Payload spec) :
    payloadAt spec (cellOf spec payload).logical = some payload := by
  simp [cellOf, materialize]

/-- A payload at its own coordinate is valid there. -/
theorem cellValid_coordinate (domain : Digest) (payload : Payload spec) :
    CellValid spec domain (coordinate spec domain payload.role payload.key) payload := rfl

#assert_axioms payloadAt_stateOfOption
#assert_axioms state_ext
#assert_axioms decodeRaw_encode
#assert_axioms decode_encode
#assert_axioms decode_canonical
#assert_axioms payloadAt_cellOf
#assert_axioms cellValid_coordinate
#assert_axioms coordinate_reserved
end Minidregg.Kernel.ProtectedCell
