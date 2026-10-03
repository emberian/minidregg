/- Explicit Activity route context. This is signed alongside the complete
application command. Preparation bytes are the exact source action sans its two
signatures; pending admission rederives them, so no nonce carries route meaning. -/
import Compiler.ContentControlFrame
import Compiler.ResourceBirthCodec
namespace Minidregg.Compiler.BendActivityDispatchContext
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
set_option autoImplicit false
structure Context where
  pin : ContentControlFrame.Pin
  generation : Nat
  pendingOrdinal : Nat
  preparationBytes : List UInt8
  homeProjectionBytes : Option (List UInt8)

def stream : StreamCodec Context :=
  StreamCodec.xmap (StreamCodec.product ContentControlFrame.pinStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product bytesStream (StreamCodec.option bytesStream)))))
    (fun c => (c.pin,c.generation,c.pendingOrdinal,c.preparationBytes,c.homeProjectionBytes))
    (fun (p,g,o,b,h) => ⟨p,g,o,b,h⟩) (by intro c; cases c; rfl)
def frame : List UInt8 := "DREGG/BEND/ACTIVITY-DISPATCH-CONTEXT/v2".toUTF8.toList
def rawCodec : LawfulCodec Context where
  encode c := frame ++ stream.encode c
  decode bytes := if bytes.take frame.length = frame then
    stream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro c
    have exact := stream.toLawful.decode_encode c
    change stream.toLawful.decode (stream.encode c) = some c at exact
    simp [exact]
def codec : LawfulCodec Context := ResourceBirthCodec.strictCodec rawCodec
abbrev encode := codec.encode
abbrev decode := codec.decode
@[simp] theorem decode_encode (c : Context) : decode (encode c) = some c := codec.decode_encode c
theorem encode_injective {a b : Context} (h : encode a = encode b) : a = b := by
  have h := congrArg decode h
  simpa only [decode_encode,Option.some.injEq] using h
#assert_axioms decode_encode
#assert_axioms encode_injective
end Minidregg.Compiler.BendActivityDispatchContext
