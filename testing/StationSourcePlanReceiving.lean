/- Actual emitted source Book evaluation and canonical scalar constructor
   decoding. This does not claim any native command was installed. -/
import Compiler.BendScalarPlanAdapter
import Theory.BendLiveMachine
import Theory.BendTTSource

open Minidregg.Compiler
open Minidregg.Compiler.BendScalarPlanAdapter
open Minidregg.Theory
open Minidregg.Theory.BendTT

private def sampleRef (id root : Nat) : Ref := ⟨id, ⟨root⟩⟩
private def expectedTake : PlanResult := .planned ⟨
  [sampleRef 1 11, sampleRef 2 12, sampleRef 3 13],
  [⟨sampleRef 2 12, [⟨1, 0, 1⟩]⟩,
   ⟨sampleRef 3 13, [⟨1, 0, 8⟩, ⟨2, 0, 1⟩]⟩]⟩
private def expectedMove : PlanResult := .planned ⟨
  [sampleRef 1 11, sampleRef 2 12, sampleRef 5 15],
  [⟨sampleRef 2 12, [⟨0, 0, 1⟩, ⟨1, 0, 1⟩]⟩,
   ⟨sampleRef 5 15, [⟨0, 1, 0⟩, ⟨1, 0, 1⟩]⟩]⟩

private def receive (core : BendCoreAdmission.Checked) (abi : ABIBinding core.book)
    (entry : String) (expected : PlanResult) : IO Bool := do
  if (Book.get core.book entry).isNone then
    IO.eprintln s!"STATION SOURCE ENTRY ABSENT {entry}"
    return false
  match BendScalarPlanAdapter.execute core abi 8192 100000 (.Ref entry) with
  | none =>
      IO.eprintln s!"STATION CHECKED SOURCE EXECUTION/DECODE REFUSED {entry}"
      return false
  | some evaluated =>
      if evaluated.output = expected then
        IO.println s!"STATION SOURCE EXECUTED + ABI CONSTRUCTOR DECODE PASS {entry} steps={evaluated.count}"
        return true
      else
        IO.eprintln s!"STATION SOURCE OUTPUT DIFFERS {entry}"
        return false

def main (paths : List String) : IO UInt32 := do
  let [path] := paths | do
    IO.eprintln "one NativeReceiving Book path required"
    return 2
  let text ← IO.FS.readFile path
  let .ok core := BendCoreAdmission.canonicalize text.toUTF8.toList | do
    IO.eprintln "STATION CORE CANONICALIZATION/BOOK CHECK REFUSED"
    return 1
  let some abi := bindABI core | do
    IO.eprintln "STATION EXACT EMITTED ABI REFUSED"
    return 1
  for (entry, expected) in [
      ("NativeReceiving.take_key_plan", expectedTake),
      ("NativeReceiving.held_key_refusal", PlanResult.refused 2),
      ("NativeReceiving.move_plan", expectedMove),
      ("NativeReceiving.exhausted_supply_refusal", PlanResult.refused 5)] do
    unless ← receive core abi entry expected do return 1
  -- Exhaustion retains a checked source prefix, not a candidate effect.
  match BendScalarPlanAdapter.execute core abi 8192 0 (.Ref "NativeReceiving.take_key_plan") with
  | some _ =>
      IO.eprintln "STATION ZERO STEP SOURCE UNEXPECTEDLY COMPLETED"
      return 1
  | none => IO.println "STATION SOURCE EXHAUSTION INERT PASS"
  return 0
