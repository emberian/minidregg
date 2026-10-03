/- Compare actual fixed-controller circuits for the two translation-validated
representations of identical public source. Census only; no latency claim. -/
import Compiler.BendObliviousExecutionIndexed

open Minidregg.Theory BendTT
open Minidregg.Compiler

def repeated : Nat → Term
  | 0 => .Lab "unit"
  | depth+1 => .Tup .Q1 (repeated depth) (repeated depth)

def main : IO Unit := do
  let source := repeated 5
  let shape : BendObliviousState.Shape := ⟨64,16,8,8,16⟩
  let some original := BendObliviousExecution.prepare [] source shape
    | throw (IO.userError "original producer refused")
  let some indexed := BendObliviousExecutionIndexed.prepare [] source shape
    | throw (IO.userError "indexed producer refused")
  IO.println s!"ORIGINAL-ROM {original.compiled.library.program.code.size}"
  IO.println s!"INDEXED-ROM {indexed.compiled.library.program.code.size}"
  IO.println s!"ORIGINAL-CIRCUIT {repr original.network.census}"
  IO.println s!"INDEXED-CIRCUIT {repr indexed.network.census}"
