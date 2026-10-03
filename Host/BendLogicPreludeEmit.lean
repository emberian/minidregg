/- Consume captured pinned safe_emit author source; bind actual parsed Book,
selected method, Prelude Bool representation and SAME literal Plan compiler.
Captured correspondence is explicit, not an arbitrary surface compiler theorem. -/
import Compiler.BendLogicPreludeCase
import Compiler.BendLogicSerialize

namespace Minidregg.Host.BendLogicPreludeEmit

open Minidregg.Compiler
open Minidregg.Compiler.BendLogicCase
open Minidregg.Compiler.BendLogicSerialize
open Lean (Json toJson)

def entryName : String := "SourceBool.not"

def candidate (d : ConstraintDescriptor BabyBear) (input output : Bool) : Nat → BabyBear :=
  let initial : Nat → BabyBear :=
    fun n => if n = 0 then bit output else if n = 1 then bit input else 0
  d.gates.foldl (fun wires gate =>
    let value := gate.op.denote (gate.a.read wires) (gate.b.read wires)
    fun n => if n = gate.out then value else wires n) initial

def check (p : Plan) (input output : Bool) : Bool :=
  let d := descriptor (F := BabyBear) 0 p
  decide (descriptorHolds d (candidate d input output))

def artifact (bookSource surfaceSource : String) : Json :=
  let p := BendLogicSpecialization.negation
  let d := descriptor (F := BabyBear) 0 p
  let f := flatten (outputExpr (F := BabyBear) p) 0
  let integral := flatten (outputExpr (F := Rat) p) 0
  Json.mkObj
    [("schema", toJson "dregg.bend.prelude-bool-case.v1"),
     ("kernelPin", toJson "947db722640c86247849343657bf2f7ef01cb7f1"),
     ("source", toJson ((BendSourceRepresentation.sourceTerm p).show 0)),
     ("bookSource", toJson bookSource), ("surfaceSource", toJson surfaceSource),
     ("entry", toJson entryName),
     ("frontendCorrespondence", toJson "captured-safe-emit-structure-v1"),
     ("tagEncoding", toJson "bend-prelude-bool-sigma-unit-v1"),
     ("compilerVersion", toJson (1 : Nat)),
     ("onFalse", toJson p.onFalse), ("onTrue", toJson p.onTrue),
     ("signedConstantPolicy", toJson "literal-bool-difference-v1"),
     ("inputWire", toJson (1 : Nat)), ("outputWire", toJson (0 : Nat)),
     ("relation", descriptorToJson d),
     ("constructiveIntegerOutput", Json.mkObj
       [("nVars", toJson (2 : Nat)), ("nWires", toJson (2 + integral.next)),
        ("gates", Json.arr ((integral.gates.map (emitGate Fin.val 2)).map signedGate).toArray),
        ("output", signedWire (emitWire Fin.val 2 integral.out))]),
     ("constructiveOutput", Json.mkObj
       [("nVars", toJson (2 : Nat)), ("nWires", toJson (2 + f.next)),
        ("gates", Json.arr ((f.gates.map (emitGate Fin.val 2)).map dgateToJson).toArray),
        ("output", dwireToJson (emitWire Fin.val 2 f.out))])]

def run : IO Unit := do
  let bookSource ← IO.FS.readFile "tests/bend-source-representation/BoolSource.bendtt"
  let surfaceSource ← IO.FS.readFile "tests/bend-source-representation/BoolSource.bend"
  let book ← match Minidregg.Theory.BendTT.Book.parse bookSource with
    | .error why => throw <| IO.userError ("captured Prelude Book parse refused: " ++ why)
    | .ok parsed => pure parsed
  unless decide (book = BendSourceRepresentation.emittedNegationBook) do
    throw <| IO.userError "captured safe_emit Book differs from exact representation source"
  unless Minidregg.Theory.BendTT.Book.check book == .ok () do
    throw <| IO.userError "captured safe_emit Book checker refused"
  unless (BendLogicPreludeCase.compileEntry (F := BabyBear) 0 book entryName
      BendLogicSpecialization.negation).isSome do
    throw <| IO.userError "selected actual Prelude method failed specialization"
  for input in [false, true] do
    unless check BendLogicSpecialization.negation input (!input) do
      throw <| IO.userError "honest Prelude source output refused"
    if check BendLogicSpecialization.negation input input then
      throw <| IO.userError "wrong Prelude source output accepted"
    let actual := (Minidregg.Theory.BendLiveMachine.executeChecked book 24 1
      (BendLogicPreludeCase.invocation entryName input)).outcome
    unless actual == .complete (BendSourceRepresentation.boolTerm (!input)) 1 do
      throw <| IO.userError "actual Prelude Ref entry source output/count differs"
  let alteredType : Minidregg.Theory.BendTT.Book :=
    [{ k := entryName, T := .Typ .Q1,
       v := BendSourceRepresentation.sourceTerm BendLogicSpecialization.negation, o := false },
      BendSourceRepresentation.armsDef, BendSourceRepresentation.boolDef]
  if (BendLogicPreludeCase.compileEntry (F := BabyBear) 0 alteredType entryName
      BendLogicSpecialization.negation).isSome then
    throw <| IO.userError "wrong Prelude method interface admitted"
  let changedBool : Minidregg.Theory.BendTT.Book :=
    [BendSourceRepresentation.methodDef BendLogicSpecialization.negation,
      BendSourceRepresentation.armsDef,
      { k := "Bool", T := .Typ .Q2, v := .Enu ["False", "True"], o := false }]
  if (BendLogicPreludeCase.compileEntry (F := BabyBear) 0 changedBool entryName
      BendLogicSpecialization.negation).isSome then
    throw <| IO.userError "same Bool name with changed actual type admitted"
  IO.eprintln "BEND-PRELUDE: actual safe_emit Book/check, typed codec, Ref source runner and refusals PASS"
  IO.println (artifact bookSource surfaceSource).compress

end Minidregg.Host.BendLogicPreludeEmit

def main : IO Unit := Minidregg.Host.BendLogicPreludeEmit.run
