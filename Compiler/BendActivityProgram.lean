/- Initial public source profile for persistent activities. An exact canonical
Book and named closed invocation produce both actual source admission and the
actual validated closure compiler result. No caller-supplied heap is accepted.
Source publication/current native permission remains the receiving boundary. -/
import Compiler.BendCoreAdmission
import Compiler.BendClosureCompile
import Compiler.BendInvocationAdmission
import Compiler.BendClosureContinuationCodec

namespace Minidregg.Compiler.BendActivityProgram
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.BendClosureContinuationCodec
set_option autoImplicit false

structure Source where
  coreBytes : List UInt8
  entry : String
  slots : Nat
  wordBits : Nat
  frames : Nat
  arguments : Nat
  checkerTicks : Nat

def sourceStream : StreamCodec Source :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product stringStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))
    (fun s => (s.coreBytes,s.entry,s.slots,s.wordBits,s.frames,s.arguments,s.checkerTicks))
    (fun (b,e,s,w,f,a,t) => ⟨b,e,s,w,f,a,t⟩) (by intro s; cases s; rfl)

def binding (source : Source) : List UInt8 :=
  "DREGG.BEND.ACTIVITY.PUBLIC-SOURCE/v1".toUTF8.toList ++ sourceStream.encode source

structure Prepared (source : Source) where
  core : BendCoreAdmission.Checked
  sourceBytes : core.bytes = source.coreBytes
  entry : BendCoreAdmission.Entry core
  entryName : entry.name = source.entry
  compiled : BendClosureCompile.Compiled core.book (.Ref source.entry)
  admitted : BendInvocationAdmission.Admission core.book (.Ref source.entry) entry.definition.T
  limits : Limits
  bounds : limits.heap.slots = source.slots ∧ limits.heap.wordBits = source.wordBits ∧
    limits.frames = source.frames ∧ limits.arguments = source.arguments

/-- v1 is bounded public source: these are admission caps, not a theorem about
private shape, physical runtime cost, source completeness or whole-machine
simulation. The receiving tariff and its source budgets remain explicit. -/
def prepare (source : Source) : Option (Prepared source) := do
  if source.coreBytes.length > 1048576 || source.slots > 65536 || source.wordBits > 64 ||
      source.frames > 65536 || source.arguments > 65536 || source.checkerTicks > 100000 then none else do
    let .ok core := BendCoreAdmission.admit source.coreBytes | none
    if sourceBytes : core.bytes = source.coreBytes then
      let .ok entry := BendCoreAdmission.entry core source.entry | none
      if entryName : entry.name = source.entry then
        let compiled ← BendClosureCompile.compile core.book (.Ref source.entry)
        let admitted ← BendInvocationAdmission.admit core.book source.checkerTicks
          (.Ref source.entry) entry.definition.T
        if fits : source.slots ≤ 2 ^ source.wordBits then
          some ⟨core,sourceBytes,entry,entryName,compiled,admitted,
            ⟨⟨source.slots,source.wordBits,fits⟩,source.frames,source.arguments⟩,
            rfl,rfl,rfl,rfl⟩
        else none
      else none
    else none

theorem prepared_entry_exact {source : Source} (prepared : Prepared source) :
    CodeDenotes prepared.compiled.library.program prepared.compiled.entry (.Ref source.entry) :=
  prepared.compiled.exactEntry

theorem prepared_invocation_typed {source : Source} (prepared : Prepared source) :
    Typed prepared.core.book [] (.Ref source.entry) prepared.entry.definition.T :=
  prepared.admitted.typed

#assert_axioms prepare
#assert_axioms prepared_entry_exact
#assert_axioms prepared_invocation_typed
end Minidregg.Compiler.BendActivityProgram
