/- Actual reusable mux artifact emitter: no supplied output solving, no FHE
implementation in the compiler. Relation nPublic0 matches owner-private result.
Public program/source topology; three changing inputs remain secret to evaluator. -/
import Compiler.BendLogicPreludeMux
import Compiler.BendLogicSerialize

namespace Minidregg.Host.BendLogicPreludeMuxEmit

open Minidregg.Compiler
open Minidregg.Compiler.BendLogicMux
open Minidregg.Compiler.BendLogicSpecialization (label)
open Minidregg.Compiler.BendLogicSerialize
open Lean (Json toJson)

def candidate (d : ConstraintDescriptor BabyBear)
    (selector onTrue onFalse output : Bool) : Nat → BabyBear :=
  let initial : Nat → BabyBear := fun n =>
    BendLogicCase.bit <| if n = 0 then output else if n = 1 then selector else
      if n = 2 then onTrue else if n = 3 then onFalse else false
  d.gates.foldl (fun wires gate =>
    let value := gate.op.denote (gate.a.read wires) (gate.b.read wires)
    fun n => if n = gate.out then value else wires n) initial

def check (selector onTrue onFalse output : Bool) : Bool :=
  let d := descriptor (F := BabyBear) 0
  decide (descriptorHolds d (candidate d selector onTrue onFalse output))

def entryName : String := "SourceBool.choose"

def artifact (bookSource surfaceSource : String) : Json :=
  let d := descriptor (F := BabyBear) 0
  let f := flatten (outputExpr (F := BabyBear)) 0
  let integral := flatten (outputExpr (F := Rat)) 0
  Json.mkObj
    [("schema", toJson "dregg.bend.prelude-bool-mux.v1"),
     ("kernelPin", toJson "947db722640c86247849343657bf2f7ef01cb7f1"),
     ("source", toJson (BendSourceRepresentation.chooseTerm.show 0)),
     ("bookSource", toJson bookSource), ("surfaceSource", toJson surfaceSource),
     ("frontendCorrespondence", toJson "captured-safe-emit-structure-v1"),
     ("tagEncoding", toJson "bend-prelude-bool-sigma-unit-v1"),
     ("entry", toJson entryName),
     ("compilerVersion", toJson (1 : Nat)),
     ("signedConstantPolicy", toJson "dynamic-bool-mux-v1"),
     ("inputWires", toJson ([1,2,3] : List Nat)),
     ("inputOrder", toJson (["selector","trueArm","falseArm"] : List String)),
     ("outputWire", toJson (0 : Nat)),
     ("relation", descriptorToJson d),
     ("constructiveIntegerOutput", Json.mkObj
       [("nVars", toJson (4 : Nat)),
        ("nWires", toJson (4 + integral.next)),
        ("gates", Json.arr ((integral.gates.map (emitGate Fin.val 4)).map signedGate).toArray),
        ("output", signedWire (emitWire Fin.val 4 integral.out))]),
     ("constructiveOutput", Json.mkObj
       [("nVars", toJson (4 : Nat)),
        ("nWires", toJson (4 + f.next)),
        ("gates", Json.arr ((f.gates.map (emitGate Fin.val 4)).map dgateToJson).toArray),
        ("output", dwireToJson (emitWire Fin.val 4 f.out))])]

def run : IO Unit := do
  let bookSource ← IO.FS.readFile "tests/bend-source-representation/BoolChooseSource.bendtt"
  let surfaceSource ← IO.FS.readFile "tests/bend-source-representation/BoolChooseSource.bend"
  let book ← match Minidregg.Theory.BendTT.Book.parse bookSource with
    | .error why => throw <| IO.userError ("Prelude mux Book parse refused: " ++ why)
    | .ok parsed => pure parsed
  unless decide (book = BendSourceRepresentation.emittedChooseBook) do
    throw <| IO.userError "captured safe_emit selector differs from exact source producer"
  unless Minidregg.Theory.BendTT.Book.check book == .ok () do
    throw <| IO.userError "actual Prelude mux Book checker refused"
  unless (BendLogicPreludeMux.compileEntry (F := BabyBear) 0 book entryName).isSome do
    throw <| IO.userError "actual selected Prelude mux entry failed specialization"
  let wrongType : Minidregg.Theory.BendTT.Book :=
    [{ k := entryName, T := .Typ .Q1, v := BendSourceRepresentation.chooseTerm, o := false },
      BendSourceRepresentation.armsDef, BendSourceRepresentation.boolDef]
  if (BendLogicPreludeMux.compileEntry (F := BabyBear) 0 wrongType entryName).isSome then
    throw <| IO.userError "wrong selected Prelude interface admitted"
  let opaqueBook : Minidregg.Theory.BendTT.Book :=
    [{ k := entryName, T := BendSourceRepresentation.chooseType,
       v := BendSourceRepresentation.chooseTerm, o := true },
      BendSourceRepresentation.armsDef, BendSourceRepresentation.boolDef]
  if (BendLogicPreludeMux.compileEntry (F := BabyBear) 0 opaqueBook entryName).isSome then
    throw <| IO.userError "opaque Prelude method admitted"
  let changedBool : Minidregg.Theory.BendTT.Book :=
    [BendSourceRepresentation.chooseDef, BendSourceRepresentation.armsDef,
      { k := "Bool", T := .Typ .Q2, v := .Enu ["False", "True"], o := false }]
  if (BendLogicPreludeMux.compileEntry (F := BabyBear) 0 changedBool entryName).isSome then
    throw <| IO.userError "same Bool name with changed representation admitted"
  if (BendLogicPreludeMux.compileEntry (F := BabyBear) 0 book "absent").isSome then
    throw <| IO.userError "absent selected method admitted"
  for selector in [false, true] do
    for onTrue in [false, true] do
      for onFalse in [false, true] do
        unless check selector onTrue onFalse (result selector onTrue onFalse) do
          throw <| IO.userError "honest Prelude mux output refused"
        if check selector onTrue onFalse (!(result selector onTrue onFalse)) then
          throw <| IO.userError "wrong Prelude mux output accepted"
        let actual := (Minidregg.Theory.BendLiveMachine.executeChecked book 32 1
          (BendLogicPreludeMux.invocation entryName selector onTrue onFalse)).outcome
        unless actual == .complete
            (BendSourceRepresentation.boolTerm (result selector onTrue onFalse)) 1 do
          throw <| IO.userError "actual captured Ref source output/count differs"
  if (BendLogicPreludeMux.compile (F := BabyBear) 5
      BendSourceRepresentation.chooseTerm).isSome then
    throw <| IO.userError "invalid Prelude mux public split admitted"
  if (BendLogicPreludeMux.compile (F := BabyBear) 0 sourceTerm).isSome then
    throw <| IO.userError "old bare enum source admitted as Prelude mux"
  IO.eprintln "BEND-PRELUDE-MUX: captured source, all inputs, exact Ref output/count and refusals PASS"
  IO.println (artifact bookSource surfaceSource).compress

end Minidregg.Host.BendLogicPreludeMuxEmit

def main : IO Unit := Minidregg.Host.BendLogicPreludeMuxEmit.run
