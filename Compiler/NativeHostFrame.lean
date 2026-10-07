/-
# Compiler.NativeHostFrame — the strict framed codec of host frames

`framed frame stream`: the frame bytes, then the stream, decoded strictly (only
canonical bytes decode, `framed_canonical`). It sits below `Compiler.NativeHostCodec`
so that codecs whose decoders the durable index runs on every append
(`Kernel.FleetTurnCodec`) can be read without the host codec's closure.
-/
import Compiler.ResourceBirthCodec

namespace Minidregg.Compiler.NativeHostCodec

open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

def framedRaw {α : Type} (frame : List UInt8) (stream : StreamCodec α) : LawfulCodec α :=
    { encode value := frame ++ stream.encode value
      decode bytes := if bytes.take frame.length = frame then
        stream.toLawful.decode (bytes.drop frame.length) else none
      decode_encode := by
        intro value
        have exact := stream.toLawful.decode_encode value
        change stream.toLawful.decode (stream.encode value) = some value at exact
        simp [exact] }

def framed {α : Type} (frame : List UInt8) (stream : StreamCodec α) : LawfulCodec α :=
  ResourceBirthCodec.strictCodec (framedRaw frame stream)

theorem framed_canonical {α : Type} (frame : List UInt8) (stream : StreamCodec α)
    {bytes : List UInt8} {value : α}
    (decoded : (framed frame stream).decode bytes = some value) :
    (framed frame stream).encode value = bytes :=
  ResourceBirthCodec.strictCodec_canonical (framedRaw frame stream) decoded

end Minidregg.Compiler.NativeHostCodec
