import Compiler.BendIndexedActivityProgram
import Theory.BendClosureDecode

open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler BendClosureContinuationCodec

private def repeatedValue (depth : Nat) : Term :=
  (List.range depth).foldl (fun value _ => .Tup .Q1 value value) (.Lab "x")

private def repeatedType (depth : Nat) : Term :=
  (List.range depth).foldl (fun type _ => .Sig .Q1 type type) (.Enu ["x"])

private def complete (limits : Limits) (library : Library) (entry : Nat) : IO State := do
  let .ok initial := start limits library entry | throw (IO.userError "machine start refused")
  let result := run limits library 1024 initial
  match result.control with
  | .complete _ => pure result
  | other => throw (IO.userError s!"machine did not complete: {repr other}")

private def resultTerm (library : Library) (state : State) : IO Term := do
  let .complete pointer := state.control | throw (IO.userError "no result pointer")
  let some decoded := decode library.program state.heap 2048 pointer
    | throw (IO.userError "complete result failed exact source decoding")
  pure decoded.term

def main : IO Unit := do
  let book : Book := [{k := "one", T := repeatedType 5, v := repeatedValue 5, o := false}]
  let publicSource : BendActivityProgram.Source :=
    ⟨BendCoreAdmission.encode book, "one", 512, 12, 32, 8, 2048⟩
  let source : BendIndexedActivityProgram.Source :=
    ⟨publicSource, BendClosureCompileIndexed.edition⟩
  let some baseline := BendActivityProgram.prepare publicSource
    | throw (IO.userError "baseline admitted source refused")
  let some indexed := BendIndexedActivityProgram.prepare source
    | throw (IO.userError "indexed admitted source refused")
  let oldResult ← complete baseline.limits baseline.compiled.library baseline.compiled.entry
  let newResult ← complete indexed.actual.limits indexed.actual.compiled.library indexed.actual.compiled.entry
  let oldTerm ← resultTerm baseline.compiled.library oldResult
  let newTerm ← resultTerm indexed.actual.compiled.library newResult
  if oldTerm != repeatedValue 5 || newTerm != oldTerm || oldResult.sourceSteps != newResult.sourceSteps then
    throw (IO.userError "optimized clear machine result or canonical source charge changed")
  let invalid : BendIndexedActivityProgram.Source := ⟨publicSource, "unregistered-compiler"⟩
  if (BendIndexedActivityProgram.prepare invalid).isSome then
    throw (IO.userError "unsupported compiler edition admitted")
  let context := BendIndexedActivityProgram.contextBytes indexed
  let oldContext := encodeContext (executionContext (BendIndexedActivityProgram.binding source)
    indexed.actual.limits indexed.actual.compiled.library)
  let oldCheckpoint : Checkpoint := ⟨oldContext, 7, newResult⟩
  let oldBytes := encode oldCheckpoint
  if (restore oldBytes.length context 7 oldBytes).isSome then
    throw (IO.userError "old compiler context silently resumed under indexed profile")
  let checkpoint : Checkpoint := ⟨context, 7, newResult⟩
  let checkpointBytes := encode checkpoint
  let some restored := restore checkpointBytes.length context 7 checkpointBytes
    | throw (IO.userError "indexed checkpoint failed exact restore")
  if restored != newResult || (restore checkpointBytes.length context 8 checkpointBytes).isSome then
    throw (IO.userError "exact state/generation restoration failed")
  IO.println s!"INDEXED ACTIVITY rows={baseline.compiled.library.program.code.size}→{indexed.actual.compiled.library.program.code.size}; sourceSteps={newResult.sourceSteps}; same exact source result; version/generation refusals and exact restore PASS"
