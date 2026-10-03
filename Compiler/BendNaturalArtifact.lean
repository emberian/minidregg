/- Shared constructive artifact producer for arbitrary supported public members.
The selected actual Book is compiled once, then the SAME recovered expression
generates the source wrapper, integer model, range AIR and signed/field graphs.
No fixture name, arity, capacity or output formula is baked into this API. -/
import Compiler.BendNaturalRefinement
import Compiler.BendNaturalCheckedCompiler
import Compiler.BendLogicSerialize
import Compiler.BendLogicBFVPlain

namespace Minidregg.Compiler.BendNaturalArtifact
open Minidregg.Compiler
open Minidregg.Compiler.BendNaturalExpression
open Minidregg.Compiler.BendLogicSerialize
open Minidregg.Theory.BendTT
open Lean (Json toJson)
set_option autoImplicit false

def modelJson {n : Nat} : Expr n → Json
  | .input i => Json.mkObj [("input", toJson i.val)]
  | .literal value => Json.mkObj [("literal", toJson value)]
  | .add left right => Json.mkObj [("add", Json.arr #[modelJson left, modelJson right])]

def bookText (book : Minidregg.Theory.BendTT.Book) : String :=
  String.intercalate "\n\n" (book.map fun d => d.k ++ " : " ++ d.T.show 0 ++
    " = " ++ d.v.show 0) ++ "\n"

def artifact {n : Nat} (entryName arithmeticEntry : String) (inputOrder : List String)
    (book : Minidregg.Theory.BendTT.Book) (surfaceSource : String)
    (plan : Plan n) (fits : plan.inputBits ≤ plan.outputBits) : Json :=
  let expr := plan.expression
  let relation := descriptor (F := BabyBear) plan.inputBits plan.outputBits fits expr
  let tree := expr.air (F := BabyBear) (fun i => i.succ : Fin n → Fin (n + 1))
  let signedTree := expr.air (F := Rat) (fun i => i.succ : Fin n → Fin (n + 1))
  let flat := flatten tree 0
  let integral := flatten signedTree 0
  Json.mkObj
    [("schema", toJson "dregg.bend.public-natural-expression.v1"),
     ("kernelPin", toJson "947db722640c86247849343657bf2f7ef01cb7f1"),
     ("entry", toJson entryName), ("arithmeticEntry", toJson arithmeticEntry),
     ("source", toJson ((worldBody expr).show 0)),
     ("sourceType", toJson (worldType.show 0)), ("bookSource", toJson (bookText book)),
     ("surfaceSource", toJson surfaceSource),
     ("frontendCorrespondence", toJson "captured-safe-emit-structure-v1"),
     ("wrapperCorrespondence", toJson "proved-native-affine-byte-list-extractor-v1"),
     ("compilerVersion", toJson (1 : Nat)),
     ("signedConstantPolicy", toJson "bounded-natural-polynomial-v1"),
     ("tagEncoding", toJson "bend-prelude-nat-scalar-v1"),
     ("inputWires", toJson ((List.range n).map Nat.succ)),
     ("inputOrder", toJson inputOrder),
     ("inputCaps", toJson (List.replicate n plan.inputCap)),
     ("inputBits", toJson plan.inputBits), ("outputBits", toJson plan.outputBits),
     ("plaintextModulus", toJson plan.plaintextModulus),
     ("outputWire", toJson (0 : Nat)), ("outputMax", toJson plan.outputMax),
     ("expression", modelJson expr),
     ("sourceChargePolicy", toJson "bend-live-eval-natural-expression-v1"),
     ("chargeReservation", toJson plan.reservation),
     ("sourceBudget", toJson plan.sourceBudget),
     ("relation", descriptorToJson relation),
     ("constructiveIntegerOutput", Json.mkObj
       [("nVars", toJson (n + 1)), ("nWires", toJson (n + 1 + integral.next)),
        ("gates", Json.arr ((integral.gates.map (emitGate Fin.val (n + 1))).map signedGate).toArray),
        ("output", signedWire (emitWire Fin.val (n + 1) integral.out))]),
     ("constructiveOutput", Json.mkObj
       [("nVars", toJson (n + 1)), ("nWires", toJson (n + 1 + flat.next)),
        ("gates", Json.arr ((flat.gates.map (emitGate Fin.val (n + 1))).map dgateToJson).toArray),
        ("output", dwireToJson (emitWire Fin.val (n + 1) flat.out))])]


/-- Produce a real member artifact from captured core Book bytes. Errors are
stage-specific diagnostics suitable for a source editor; unsupported members
remain source-native and are not silently compiled as a different expression. -/
def produce (arity : Nat) (captured surface : String) (entry worldEntry : String)
    (inputOrder : List String) (fuel inputBits outputBits sourceBudget plaintextModulus : Nat) :
    Except String Json := do
  if inputOrder.length != arity then throw "input order does not match source arity"
  if entry.isEmpty || worldEntry.isEmpty then throw "empty selected source entry"
  let core ← BendCoreAdmission.canonicalize captured.toUTF8.toList
  let original := core.book
  let plan ← match compileChecked (n := arity) (p := 2013265921) core entry fuel
      inputBits outputBits sourceBudget plaintextModulus with
    | none => throw "unsupported member, interface, Nat family or numeric/resource profile"
    | some plan => pure plan
  if h : plan.inputBits ≤ plan.outputBits then
    let book := original ++ [BendSourceRepresentation.listArmsDef,
      BendSourceRepresentation.listDef, worldDefinition worldEntry plan.expression]
    match Book.check book with
    | .error why => throw ("native source wrapper type check: " ++ why)
    | .ok () => pure ()
    if decide (Book.get book worldEntry = some (worldDefinition worldEntry plan.expression)) then
      pure (artifact worldEntry entry inputOrder book surface plan h)
    else throw "selected native source wrapper differs from generated definition"
  else throw "input width exceeds output range width"

end Minidregg.Compiler.BendNaturalArtifact
