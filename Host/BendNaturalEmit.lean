/- Real reusable source consumer and emitter. The expression is recovered
from the actual captured custom method and checked full definition. The world
wrapper is compiler-generated, source-proved, and admitted by actual Book.check.
No numeric graph fixture or independent scalar formula replaces the compiler. -/
import Compiler.BendNaturalArtifact
import Compiler.BendLogicSerialize
import Compiler.BendLogicBFVPlain

namespace Minidregg.Host.BendNaturalEmit
open Minidregg.Compiler
open Minidregg.Compiler.BendNaturalExpression
open Minidregg.Compiler.BendLogicSerialize
open Lean (Json toJson)

def arithmeticEntry : String := "SourceNat.doubleSum"
def entryName : String := "SourceNat.worldDoubleSum"
def candidate (expr : Expr 2) (a b output : Nat) : Nat → BabyBear :=
  let values : Fin 3 → Nat := numbers (fun i => if i.val = 0 then b else a) output
  let initial : Nat → BabyBear := fun index =>
    if h : index < 33 then
      match (packed (n := 2) (k := 10)).symm ⟨index, h⟩ with
      | .inl i => (values i : BabyBear)
      | .inr (i, j) => ((values i / 2 ^ j.val) % 2 : Nat)
    else 0
  let relation := descriptor (F := BabyBear) 8 10 (by decide) expr
  relation.gates.foldl (fun wires gate =>
    let value := gate.op.denote (gate.a.read wires) (gate.b.read wires)
    fun n => if n = gate.out then value else wires n) initial

def artifact (book : Minidregg.Theory.BendTT.Book) (surfaceSource : String)
    (plan : Plan 2) : Json :=
  if fits : plan.inputBits ≤ plan.outputBits then
    BendNaturalArtifact.artifact entryName arithmeticEntry ["b","a"] book surfaceSource plan fits
  else Json.mkObj [("error", toJson "invalid compiler width profile")]

def run : IO Unit := do
  let surface ← IO.FS.readFile "tests/bend-source-representation/NaturalExpressionSource.bend"
  let captured ← IO.FS.readFile "tests/bend-source-representation/NaturalExpressionSource.bendtt"
  let original ← match Minidregg.Theory.BendTT.Book.parse captured with
    | .error why => throw <| IO.userError ("captured custom Book parse refused: " ++ why)
    | .ok book => pure book
  unless Minidregg.Theory.BendTT.Book.check original == .ok () do
    throw <| IO.userError "captured custom source Book checker refused"
  let some plan := compile (n := 2) (p := 2013265921) original arithmeticEntry 128 8 10 1024 1032193
    | throw <| IO.userError "actual custom method source/profile specialization refused"
  let expr := plan.expression
  let book := original ++ [BendSourceRepresentation.listArmsDef,
    BendSourceRepresentation.listDef, worldDefinition entryName expr]
  match Minidregg.Theory.BendTT.Book.check book with
  | .error why => throw <| IO.userError ("actual generated affine native source wrapper Book refused: " ++ why)
  | .ok () => pure ()
  unless decide (Minidregg.Theory.BendTT.Book.get book entryName = some (worldDefinition entryName expr)) do
    throw <| IO.userError "actual selected generated world method differs"
  unless BendLogicNatAdd.bookBinding book do
    throw <| IO.userError "exact Nat family/add Book binding lost on world wrapper"
  unless plan.outputMax == 1020 && plan.reservation == 1024 do
    throw <| IO.userError "captured custom model has unexpected derived range or source count"
  let relation := descriptor (F := BabyBear) 8 10 (by decide) expr
  for pair in [(0,0),(1,2),(2,3),(255,0),(0,255),(255,255)] do
    let a := pair.1; let b := pair.2
    let inputs : Fin 2 → Nat := fun i => if i.val = 0 then b else a
    let result := expr.value inputs
    unless decide (descriptorHolds relation (candidate expr a b result)) do
      throw <| IO.userError "actual emitted numeric relation refused canonical witness"
    if decide (descriptorHolds relation (candidate expr a b (result + 1))) then
      throw <| IO.userError "actual emitted numeric relation admitted changed output"
    if a ≤ 3 && b ≤ 3 then
      let source := worldInvocation entryName inputs [7,8]
      let actual := (Minidregg.Theory.BendLiveMachine.executeChecked book 32768 1024 source).outcome
      unless actual == .complete (BendSourceRepresentation.natTerm result)
          (1 + expr.sourceCount inputs) do
        throw <| IO.userError "actual custom affine source output/semantic count differs"
  let bad : Minidregg.Theory.BendTT.Book :=
    [{k := arithmeticEntry,T := .Typ .Q1,v := lower expr,o := false}] ++ original
  if (compile (n := 2) (p := 2013265921) bad arithmeticEntry 128 8 10 1024 1032193).isSome then
    throw <| IO.userError "changed actual custom method interface admitted"
  if (compile (n := 2) (p := 2013265921) original arithmeticEntry 128 8 10 1023 1032193).isSome then
    throw <| IO.userError "below-uniform-budget profile admitted"
  if (compile (n := 2) (p := 2013265921) original arithmeticEntry 128 8 10 1024 1020).isSome then
    throw <| IO.userError "whole scalar no-wrap bound omitted"
  IO.eprintln "BEND-NATURAL: actual captured custom source, native affine source wrapper, range witnesses/refusals/charge PASS"
  IO.println (artifact book surface plan).compress

end Minidregg.Host.BendNaturalEmit

def main : IO Unit := Minidregg.Host.BendNaturalEmit.run
