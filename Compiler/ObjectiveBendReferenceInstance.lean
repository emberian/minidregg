/- Persistent instances contain only exact governed source references. Complete
partial packages and composed core remain transient authenticated source input.
Heterogeneous state, descriptor binding and ROM remain the actual native Store. -/
import Compiler.ObjectiveBendReference
import Compiler.ObjectiveBendInstance
namespace Minidregg.Compiler.ObjectiveBendReferenceInstance
open Minidregg.Theory.Store
open WorldKindDescriptor
open ObjectiveBendInstance (PinSpace valueBytes bytesValue)
set_option autoImplicit false

def pinAt (value : Kernel.WorldKindInstance.Instance) (space : PinSpace value.descriptor) :
    Option ObjectiveBendReference.Pin :=
  (value.store ⟨space.space, (0 : Nat)⟩).bind fun bytes => ObjectiveBendReference.decode (valueBytes space bytes)

structure Instance where
  value : Kernel.WorldKindInstance.Instance
  space : PinSpace value.descriptor
  pin : ObjectiveBendReference.Pin
  pinned : pinAt value space = some pin
  closure : ObjectiveBendInstance.Pin
  source : ObjectiveBendInstance.Loaded closure
  core : ObjectiveBendReference.Core
  coreExact : core.book = closure.core
  identities : ObjectiveBendReference.Matches pin closure.prototypes core

/-- This creates a native initial state with a compact immutable reference pin;
ordinary birth receiving still judges creator, kind, defaults, fees and law. -/
def initialState (descriptor : Descriptor) (valid : descriptor.Valid)
    (state : Store (layout descriptor)) (space : PinSpace descriptor) (pin : ObjectiveBendReference.Pin) :
    Kernel.WorldKindInstance.Instance :=
  ⟨descriptor, valid, state.set ⟨space.space, (0 : Nat)⟩
    (some (bytesValue space (ObjectiveBendReference.encode pin)))⟩

def Instance.native (object : Instance) (kindRoot : Minidregg.Theory.TypedAuthorization.Digest) :=
  WorldKindCell.instanceOf kindRoot object.value

theorem prepared_pin_preserved (value : Kernel.WorldKindInstance.Instance)
    (space : PinSpace value.descriptor) (prepared : Kernel.WorldKindInstance.Prepared value) :
    pinAt prepared.post space = pinAt value space := by
  exact congrArg
    (fun entry : Option ((layout value.descriptor).Value space.space) =>
      entry.bind fun bytes => ObjectiveBendReference.decode (valueBytes space bytes))
    (Kernel.WorldKindInstance.prepared_preserves_rom prepared
      ⟨space.space, (0 : Nat)⟩ space.immutable)

def Instance.after (object : Instance) (prepared : Kernel.WorldKindInstance.Prepared object.value) : Instance :=
  { value := prepared.post, space := object.space, pin := object.pin
    pinned := (prepared_pin_preserved object.value object.space prepared).trans object.pinned
    closure := object.closure, source := object.source, core := object.core
    coreExact := object.coreExact, identities := object.identities }

#assert_axioms prepared_pin_preserved
end Minidregg.Compiler.ObjectiveBendReferenceInstance
