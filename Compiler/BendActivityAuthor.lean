/- Actual event62 proposal authoring for native current-law receiving. The
source Book is checked and compiled; initialization and tick successors use the
real controller. These unsigned proposals grant no admission or dispatch right.
The current native receiver independently rederives the same post and nonce.
-/
import Kernel.BendActivityIngress

namespace Minidregg.Compiler.BendActivityAuthor
open Minidregg.Theory
open BendClosureMachine
open Minidregg.Compiler.BendClosureContinuationCodec
open Minidregg.Kernel
set_option autoImplicit false

inductive Computed {source : BendActivityProgram.Source}
    (program : BendActivityProgram.Prepared source) (pin : ContentControlFrame.Pin)
    (currentBytes : List UInt8) (generation ticks : Nat) (record : BendActivity.Record) : Prop
  | initialized (actual : BendActivity.start (BendActivityProgram.binding source)
      generation program.limits program.compiled.library program.compiled.entry = .ok record)
  | advanced (before : BendActivity.Record)
      (current : BendActivityControl.readRecord pin currentBytes = some before)
      (actual : BendActivity.advance program.limits program.compiled.library ticks before = some record)

structure Proposal (source : BendActivityProgram.Source) (pin : ContentControlFrame.Pin)
    (currentBytes : List UInt8) (generation ticks : Nat) where
  program : BendActivityProgram.Prepared source
  action : BendActivityIngress.Source
  record : BendActivity.Record
  content : ContentResource.Command
  computed : Computed program pin currentBytes generation ticks record
  /-- No signature bytes are created by source computation. -/
  unsigned : action.signedBytes = []

def Proposal.nonce {source : BendActivityProgram.Source} {pin : ContentControlFrame.Pin}
    {currentBytes : List UInt8} {generation ticks : Nat}
    (proposal : Proposal source pin currentBytes generation ticks) : Nat :=
  BendActivityIngress.actionNonce proposal.action

def prepare (source : BendActivityProgram.Source) (pin : ContentControlFrame.Pin)
    (currentBytes : List UInt8) (isInitialization : Bool) (generation ticks : Nat) :
    Option (Proposal source pin currentBytes generation ticks) := do
  let program ← BendActivityProgram.prepare source
  if isInitialization then
    if ticks != 0 || BendActivityControl.phase pin currentBytes != some .bare then none else do
      match actual : BendActivity.start (BendActivityProgram.binding source) generation
          program.limits program.compiled.library program.compiled.entry with
      | .error _ => none
      | .ok record =>
        let content := match ContentControlFrame.editPayload pin currentBytes (BendActivity.encode record) with
          | some edit => edit
          | none => ⟨[.createAtom pin.atom (.inlineObject pin.schema) (BendActivity.encode record)]⟩
        let action : BendActivityIngress.Source := ⟨source,true,generation,0,0,[]⟩
        some ⟨program,action,record,content,.initialized actual,rfl⟩
  else
    match current : BendActivityControl.readRecord pin currentBytes with
    | none => none
    | some before =>
      if before.checkpoint.generation != generation || before.checkpoint.contextBytes !=
          encodeContext (executionContext (BendActivityProgram.binding source) program.limits program.compiled.library) then none else do
        match actual : BendActivity.advance program.limits program.compiled.library ticks before with
        | none => none
        | some record =>
          let content ← ContentControlFrame.editPayload pin currentBytes (BendActivity.encode record)
          let action : BendActivityIngress.Source := ⟨source,false,generation,before.ordinal,ticks,[]⟩
          some ⟨program,action,record,content,.advanced before current actual,rfl⟩

#assert_axioms prepare
end Minidregg.Compiler.BendActivityAuthor
