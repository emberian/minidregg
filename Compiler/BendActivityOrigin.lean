/- Canonical retained source-origin data for persistent Bend activities.
The current source transition, not this codec, authorizes its installation. -/
import Compiler.BendClosureContinuationCodec
import Theory.BendClosureResponse

namespace Minidregg.Compiler.BendActivitySegment
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.BendClosureContinuationCodec
set_option autoImplicit false

/-- A signature is selected from the exact admitted Book, and its complete
canonical type text is retained. Neither a schema nor a digest is a type proof. -/
structure TypePin where
  definition : String
  typeBytes : List UInt8

def typeBytes (type : Term) : List UInt8 := (Term.show type 0).toUTF8.toList

def typePinStream : StreamCodec TypePin :=
  StreamCodec.xmap (StreamCodec.product stringStream bytesStream)
    (fun pin => (pin.definition,pin.typeBytes))
    (fun (name,bytes) => ⟨name,bytes⟩) (by intro pin; cases pin; rfl)

structure ResponseOrigin where
  continuation : Nat
  input : Nat
  bit : Bool
  signature : TypePin

def responseOriginStream : StreamCodec ResponseOrigin :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product boolStream typePinStream)))
    (fun origin => (origin.continuation,origin.input,origin.bit,origin.signature))
    (fun (f,x,b,s) => ⟨f,x,b,s⟩) (by intro origin; cases origin; rfl)

/-- none means the original exact named source entry; some records the source
application created by an admitted external-response transition. -/
abbrev Origin := Option ResponseOrigin

def originStream : StreamCodec Origin := StreamCodec.option responseOriginStream


end Minidregg.Compiler.BendActivitySegment
