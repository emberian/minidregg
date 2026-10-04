/- An object's declared state, as its state cell holds it: the value and a
write version.

Every committed write of an object's declared state stores the next version
(creation stores version 1). An activity is resumed with the state AND its
version, read in the resuming turn (`Kernel.ObjectiveActivity`, resume with
view); the version is what the activity, a card or a later turn can name to say
which state it saw. The version is a counter of writes, distinct from the
schema version of the object's declared type. -/
import Kernel.ObjectiveActivityWire

namespace Minidregg.Kernel
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Theory.ObjectiveBendDemandData (Data)
set_option autoImplicit false

structure ObjectState where
  version : Nat
  value : Data
  deriving Repr

namespace ObjectState

def frame : Bytes := "DREGG/OBJECTIVE/OBJECT-STATE/v1".toUTF8.toList

/-- The wire: the version and the value's exact data bytes, framed and strict. -/
def wire := framed frame (StreamCodec.product StreamCodec.nat bytesStream)

def encodeObjectState (state : ObjectState) : Bytes := wire.encode (state.version, dataBytes state.value)

def decodeObjectState (bytes : Bytes) : Option ObjectState := do
  let (version, valueBytes) ← wire.decode bytes
  let value ← decodeDataBytes valueBytes
  pure ⟨version, value⟩

theorem objectState_roundTrip (state : ObjectState) :
    decodeObjectState (encodeObjectState state) = some state := by
  have wired : wire.decode (wire.encode (state.version, dataBytes state.value)) =
      some (state.version, dataBytes state.value) := framed_roundTrip _ _ _
  simp [decodeObjectState, encodeObjectState, wired, decodeDataBytes_dataBytes]

/-- Strict: a decoded state re-encodes to exactly the bytes it came from. -/
theorem decodeObjectState_canonical {bytes : Bytes} {state : ObjectState}
    (decoded : decodeObjectState bytes = some state) : encodeObjectState state = bytes := by
  unfold decodeObjectState at decoded
  cases wired : wire.decode bytes with
  | none => simp [wired] at decoded
  | some pair =>
    obtain ⟨version, valueBytes⟩ := pair
    cases valued : decodeDataBytes valueBytes with
    | none => simp [wired, valued] at decoded
    | some value =>
      simp [wired, valued] at decoded
      subst decoded
      unfold encodeObjectState
      rw [decodeDataBytes_canonical valued]
      exact framed_canonical wired

#assert_axioms objectState_roundTrip
#assert_axioms decodeObjectState_canonical
end ObjectState
end Minidregg.Kernel
