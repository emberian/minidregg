/- Public synthetic controller census and exact mismatch diagnostics. These
fixtures exercise source-machine branches; they are not admitted world calls.
No private state, secret shares, or source count is exported by a private run. -/
import Assurance.BendObliviousFixtures

open Minidregg.Theory.BendClosureMachine
open Minidregg.Compiler
open Minidregg.Assurance.BendObliviousFixtures

def main : IO Unit := do
  match BendObliviousController.network shape library with
  | none => throw (IO.userError "public controller construction refused")
  | some network =>
    IO.println s!"CENSUS {repr network.census}"
    let mut failures := 0
    for (state,index) in cases.zipIdx do
      let got := runNetwork network state
      let expected := step limits library state
      if got != some expected then
        failures := failures + 1
        IO.println s!"MISMATCH {index}: input={repr state.control} got={repr got} expected={repr expected}"
    IO.println s!"CONFORMANCE {cases.length-failures}/{cases.length}"
    IO.println s!"COUNTER-OVERFLOW-REFUSED {sourceCounterRefused}"
    if failures != 0 || !sourceCounterRefused then
      throw (IO.userError "controller conformance failed")
