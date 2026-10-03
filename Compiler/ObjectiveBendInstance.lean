/- Stateful Objective Bend instances reuse the ACTUAL world-kind carrier and
its typed heterogeneous store. The behavior pin is an immutable bytes namespace
with an explicit semantic meaning; no separate object heap or numeric method
implementation is introduced. Native registration and the shared source-call
input/signature ABI remain integration joins, not properties of this codec. -/
import Compiler.WorldKindCell
import Compiler.ObjectiveBendPrototype
import Compiler.ObjectiveBendElaboration
import Theory.AssertAxioms

namespace Minidregg.Compiler.ObjectiveBendInstance
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open WorldKindDescriptor
open Tower256ConcreteBackend
open ObjectiveBendComposition
set_option autoImplicit false

/-- The whole immutable behavior closure and exact admitted composed core are
pinned together. Parent partials precede their children; source package/import
bytes are inside each partial artifact. -/
structure Pin where
  prototypes : List ObjectiveBendPrototype.Partial
  core : List UInt8
  deriving DecidableEq, Repr

def pinStream : StreamCodec Pin :=
  StreamCodec.xmap (StreamCodec.product
    (StreamCodec.list ObjectiveBendPrototype.partialStream) bytesStream)
    (fun pin => (pin.prototypes, pin.core))
    (fun pair => ⟨pair.1, pair.2⟩) (by intro pin; cases pin; rfl)
def frame : List UInt8 := "DREGG/OBJECTIVE-BEND/INSTANCE-PIN/v1".toUTF8.toList
def encode (pin : Pin) : List UInt8 := frame ++ pinStream.encode pin
def decode (bytes : List UInt8) : Option Pin :=
  NockProgramCodec.framedDecode frame pinStream bytes

def rootId (pin : Pin) : Option Nat :=
  pin.prototypes.getLast?.map ObjectiveBendPrototype.identity

def pinIdentity (pin : Pin) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.INSTANCE-PIN/v1".toUTF8.toList
    (encode pin)).digest

/-- A loader must actually reflect the complete pinned closure, construct its
methods, check the composed Book and match its exact canonical core bytes.
A decoded Pin alone is not an executable prototype. -/
structure Loaded (pin : Pin) where
  construction : ObjectiveBendElaboration.Construction
  reflected : pin.prototypes.mapM ObjectiveBendPrototype.reflect = .ok construction.layers
  rootExact : rootId pin = some construction.root.id
  coreExact : pin.core = construction.core.bytes

/-- Exact semantic meaning is independent of the member's display name and
field coordinate. Descriptor uniqueness is enforced by the existing source. -/
def pinMeaning : String := "dregg/objective-bend/prototype-pin/v1"

structure PinSpace (descriptor : Descriptor) where
  space : Fin descriptor.fields.length
  bytes : (descriptor.fields.get space).codec = .bytes
  immutable : (descriptor.fields.get space).discipline = .rom
  meaning : (descriptor.fields.get space).meaning = pinMeaning

def bytesValue {descriptor : Descriptor} (space : PinSpace descriptor)
    (bytes : List UInt8) : (layout descriptor).Value space.space :=
  Eq.mpr (by
    change (descriptor.fields.get space.space).codec.Value = List UInt8
    rw [space.bytes]
    rfl) bytes

def valueBytes {descriptor : Descriptor} (space : PinSpace descriptor)
    (value : (layout descriptor).Value space.space) : List UInt8 :=
  Eq.mp (by
    change (descriptor.fields.get space.space).codec.Value = List UInt8
    rw [space.bytes]
    rfl) value

def pinAt (value : Kernel.WorldKindInstance.Instance) (space : PinSpace value.descriptor) : Option Pin :=
  (value.store ⟨space.space, (0 : Nat)⟩).bind fun bytes => decode (valueBytes space bytes)

/-- Birth initializes the pin at key zero alongside any member-authored state.
It does not grant creation authority or bypass the kind's birth law. The ordinary
WorldKindCell.instanceOf supplies the immutable descriptor/kind-root binding. -/
def initialState (descriptor : Descriptor) (valid : descriptor.Valid)
    (state : Store (layout descriptor)) (space : PinSpace descriptor) (pin : Pin) :
    Kernel.WorldKindInstance.Instance :=
  ⟨descriptor, valid, state.set ⟨space.space, (0 : Nat)⟩ (some (bytesValue space (encode pin)))⟩

/-- Per-object construction retains the actual object, decoded pin and full
source construction evidence. Its state is the existing typed store. -/
structure Instance where
  value : Kernel.WorldKindInstance.Instance
  space : PinSpace value.descriptor
  pin : Pin
  pinned : pinAt value space = some pin
  source : Loaded pin

def Instance.native (object : Instance) (kindRoot : Digest) :=
  WorldKindCell.instanceOf kindRoot object.value

/-- A prepared native state mutation cannot replace the behavior pin. This
follows from Store's ROM theorem for ALL well-formed heterogeneous descriptors,
not from checking a particular generated object. -/
theorem prepared_pin_preserved (value : Kernel.WorldKindInstance.Instance)
    (space : PinSpace value.descriptor) (prepared : Kernel.WorldKindInstance.Prepared value) :
    pinAt prepared.post space = pinAt value space := by
  exact congrArg
    (fun entry : Option ((layout value.descriptor).Value space.space) =>
      entry.bind fun bytes => decode (valueBytes space bytes))
    (Kernel.WorldKindInstance.prepared_preserves_rom prepared
      ⟨space.space, (0 : Nat)⟩ space.immutable)

def Instance.after (object : Instance)
    (prepared : Kernel.WorldKindInstance.Prepared object.value) : Instance :=
  { value := prepared.post, space := object.space, pin := object.pin
    pinned := (prepared_pin_preserved object.value object.space prepared).trans object.pinned
    source := object.source }

theorem after_same_prototype (object : Instance)
    (prepared : Kernel.WorldKindInstance.Prepared object.value) :
    (object.after prepared).pin = object.pin := rfl

theorem roundtrip (pin : Pin) : decode (encode pin) = some pin :=
  NockProgramCodec.framedDecode_encode frame pinStream pin

theorem canonical {bytes : List UInt8} {pin : Pin}
    (decoded : decode bytes = some pin) : encode pin = bytes :=
  NockProgramCodec.framedDecode_canonical decoded

#assert_axioms prepared_pin_preserved
#assert_axioms after_same_prototype
#assert_axioms roundtrip
#assert_axioms canonical
end Minidregg.Compiler.ObjectiveBendInstance
