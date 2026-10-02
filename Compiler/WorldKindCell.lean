/- Fixed physical carriers for source-interpreted kind definitions/instances.
The inner store is typed by its retained descriptor. The outer instance patch
can only be obtained by running that typed patch, never from a replacement blob.
-/
import Kernel.WorldKindInstance

namespace Minidregg.Compiler.WorldKindCell

open Minidregg.Theory.Store
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.WorldKindDescriptor
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

structure Definition where
  descriptor : Descriptor
  /-- Canonical inner StoreCodec bytes; initial values may include ROM fields. -/
  defaults : List UInt8
  deriving DecidableEq, Repr

def definitionStream : StreamCodec Definition :=
  StreamCodec.xmap (StreamCodec.product descriptorStream bytesStream)
    (fun definition => (definition.descriptor, definition.defaults))
    (fun pair => ⟨pair.1, pair.2⟩) (by intro definition; cases definition; rfl)

def definitionLayout : Layout.{0, 0, 0} where
  Namespace := Unit
  Key := fun _ => Unit
  Value := fun _ => Definition
  discipline := fun _ => .ram

def definitionAddress : Address definitionLayout := ⟨(), ()⟩

def definitionWire : StoreCodec.Wire definitionLayout where
  name := "minidregg/world-kind/definition/v1"
  namespaces := [()]
  namespaces_complete := by intro space; cases space; simp
  namespaceStream := StoreCodec.unitStream
  keyStream := fun _ => StoreCodec.unitStream
  valueStream := fun _ => definitionStream
  keyCodecId := fun _ => "unit/v1"
  valueCodecId := fun _ => "world-kind-definition/v1"

def definitionMaterializer := StoreCodec.materializer definitionWire

def Definition.instantiate (definition : Definition) : Option Kernel.WorldKindInstance.Instance := do
  if valid : definition.descriptor.Valid then
    let store ← StoreCodec.decode (wire definition.descriptor) definition.defaults
    some ⟨definition.descriptor, valid, store⟩
  else none

def Definition.Valid (cell : Nat) (definition : Definition) : Prop :=
  definition.descriptor.kind = cell ∧ definition.instantiate.isSome = true

instance definitionValidDecidable (cell : Nat) (definition : Definition) :
    Decidable (definition.Valid cell) := by unfold Definition.Valid; infer_instance

def definitionLaw (cell : Nat) (store : Store definitionLayout) : Prop :=
  ∃ definition, store definitionAddress = some definition ∧ definition.Valid cell

instance definitionLawDecidable (cell : Nat) (store : Store definitionLayout) :
    Decidable (definitionLaw cell store) := by
  unfold definitionLaw
  cases store definitionAddress with
  | none => simp; infer_instance
  | some definition => simp; infer_instance

inductive InstanceSpace where
  | descriptor
  | payload
  deriving DecidableEq, Repr

def InstanceSpace.Value : InstanceSpace → Type
  | .descriptor => Descriptor
  | .payload => List UInt8

instance instanceValueDecidable (space : InstanceSpace) : DecidableEq space.Value := by
  cases space <;> unfold InstanceSpace.Value <;> infer_instance

def instanceLayout : Layout.{0, 0, 0} where
  Namespace := InstanceSpace
  Key := fun _ => Unit
  Value := InstanceSpace.Value
  discipline
    | .descriptor => .rom
    | .payload => .ram

def descriptorAddress : Address instanceLayout := ⟨.descriptor, ()⟩
def payloadAddress : Address instanceLayout := ⟨.payload, ()⟩

def instanceSpaceStream : StreamCodec InstanceSpace where
  encode | .descriptor => [0] | .payload => [1]
  decodePrefix
    | 0 :: rest => some (.descriptor, rest)
    | 1 :: rest => some (.payload, rest)
    | _ => none
  decodePrefix_encode := by intro space suffix; cases space <;> rfl

def instanceWire : StoreCodec.Wire instanceLayout where
  name := "minidregg/world-kind/instance-carrier/v1"
  namespaces := [.descriptor, .payload]
  namespaces_complete := by intro space; cases space <;> simp
  namespaceStream := instanceSpaceStream
  keyStream := fun _ => StoreCodec.unitStream
  valueStream
    | .descriptor => descriptorStream
    | .payload => bytesStream
  keyCodecId := fun _ => "unit/v1"
  valueCodecId
    | .descriptor => "world-kind-descriptor/v1"
    | .payload => "world-kind-inner-store/v1"

def instanceMaterializer := StoreCodec.materializer instanceWire

def instanceOf (value : Kernel.WorldKindInstance.Instance) : Store instanceLayout :=
  ((0 : Store instanceLayout).set descriptorAddress (some value.descriptor)).set
    payloadAddress (some (StoreCodec.encode (wire value.descriptor) value.store))

def instanceAt (store : Store instanceLayout) : Option Kernel.WorldKindInstance.Instance := do
  let descriptor ← store descriptorAddress
  if valid : descriptor.Valid then
    let payload ← store payloadAddress
    let inner ← StoreCodec.decode (wire descriptor) payload
    some ⟨descriptor, valid, inner⟩
  else none

def instanceLaw (store : Store instanceLayout) : Prop := (instanceAt store).isSome = true

instance instanceLawDecidable (store : Store instanceLayout) : Decidable (instanceLaw store) := by
  unfold instanceLaw; infer_instance

/-- Both source roles use the same typed store as existing registry roles. -/
theorem instance_carrier_roundtrip (store : Store instanceLayout) :
    StoreCodec.decode instanceWire (StoreCodec.encode instanceWire store) = some store :=
  StoreCodec.decode_encode instanceWire store

theorem binding_immutable (store : Store instanceLayout) (patch : Patch instanceLayout)
    (valid : Patch.ValidFrom store patch) :
    Patch.run store patch descriptorAddress = store descriptorAddress :=
  Patch.rom_preserved store patch descriptorAddress valid rfl

/-- A receiver uses this one computation for both its post and its patch.
An invalid inner operation cannot turn into a valid outer replacement. -/
def preparePatch (store : Store instanceLayout) (actions : List Kernel.WorldKindInstance.Action) :
    Option (Patch instanceLayout) := do
  let value ← instanceAt store
  let prepared ← Kernel.WorldKindInstance.prepare value actions
  let oldBytes ← store payloadAddress
  let newBytes := StoreCodec.encode (wire value.descriptor) prepared.post.store
  some [.write .payload () oldBytes newBytes]

end Minidregg.Compiler.WorldKindCell
