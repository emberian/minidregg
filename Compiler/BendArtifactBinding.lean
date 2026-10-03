/- Compiler artifact to native source identity. This is executable source/DAG
binding, separate from deployment SHA, ciphertext validity and receiving authority.
Bare core artifacts without a checked Book/entry cannot be registered here. -/
import Compiler.BendNaturalArtifact
import Compiler.BendLogicPreludeCase
import Compiler.BendLogicPreludeMux
import Kernel.BendNativeRun
import Lean.Data.Json

namespace Minidregg.Compiler.BendArtifactBinding
open Lean (Json toJson)
open Minidregg.Compiler
open Minidregg.Compiler.BendLogicSerialize
open Minidregg.Compiler.BendNaturalExpression
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
set_option autoImplicit false

def planId (compilerBytes : List UInt8) : TypedAuthorization.Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.CONSTRUCTIVE-PLAN/v1".toUTF8.toList compilerBytes).digest

def entryParams (entry : String) : List UInt8 :=
  "DREGG/BEND/ENTRY/v1".toUTF8.toList ++ PolicyRecordCodec.stringStream.encode entry

def string (json : Json) (key : String) : Except String String := do
  (← json.getObjVal? key).getStr?
def natural (json : Json) (key : String) : Except String Nat := do
  (← json.getObjVal? key).getNat?
def boolean (json : Json) (key : String) : Except String Bool := do
  (← json.getObjVal? key).getBool?
def strings (json : Json) (key : String) : Except String (List String) := do
  (← (← json.getObjVal? key).getArr?).toList.mapM Json.getStr?

def requireFields (json : Json) (expected : List (String × Json)) : Except String Unit := do
  for (key,value) in expected do
    if (← json.getObjVal? key) != value then throw ("compiler projection differs: " ++ key)

def graphs {n : Nat} (field : Term (AirSig BabyBear (Fin n)))
    (integer : Term (AirSig Rat (Fin n))) : List (String × Json) :=
  let f := flatten field 0
  let integral := flatten integer 0
  [("constructiveIntegerOutput",Json.mkObj
    [("nVars",toJson n),("nWires",toJson (n+integral.next)),
     ("gates",Json.arr ((integral.gates.map (emitGate Fin.val n)).map signedGate).toArray),
     ("output",signedWire (emitWire Fin.val n integral.out))]),
   ("constructiveOutput",Json.mkObj
    [("nVars",toJson n),("nWires",toJson (n+f.next)),
     ("gates",Json.arr ((f.gates.map (emitGate Fin.val n)).map dgateToJson).toArray),
     ("output",dwireToJson (emitWire Fin.val n f.out))])]

/-- Re-run the same source compiler and canonical constructive projections.
No supplied output/witness or caller-selected arithmetic graph is trusted. -/
def verifySource (json : Json) (core : BendCoreAdmission.Checked) (entry : String) (sourceFuel : Nat) :
    Except String Unit := do
  requireFields json [("kernelPin",toJson BendWorldSource.upstreamPin),
    ("compilerVersion",toJson (1 : Nat)),("entry",toJson entry),
    ("outputWire",toJson (0 : Nat)),
    ("frontendCorrespondence",toJson "captured-safe-emit-structure-v1")]
  let schema ← string json "schema"
  if schema == "dregg.bend.prelude-bool-case.v1" then
    if sourceFuel < 1 then throw "source fuel cannot complete admitted Prelude entry"
    let p : BendLogicCase.Plan := ⟨← boolean json "onFalse", ← boolean json "onTrue"⟩
    if !(BendCheckedPrelude.unary (F := BabyBear) core entry 0 p).isSome then
      throw "actual Prelude case Book/entry/interface refused"
    requireFields json ([("source",toJson ((BendSourceRepresentation.sourceTerm p).show 0)),
      ("tagEncoding",toJson "bend-prelude-bool-sigma-unit-v1"),
      ("signedConstantPolicy",toJson "literal-bool-difference-v1"),
      ("inputWire",toJson (1 : Nat)),
      ("relation",descriptorToJson (BendLogicCase.descriptor (F := BabyBear) 0 p))] ++
      graphs (BendLogicCase.outputExpr (F := BabyBear) p) (BendLogicCase.outputExpr (F := Rat) p))
  else if schema == "dregg.bend.prelude-bool-mux.v1" then
    if sourceFuel < 1 then throw "source fuel cannot complete admitted Prelude entry"
    if !(BendCheckedPrelude.mux (F := BabyBear) core entry 0).isSome then
      throw "actual Prelude mux Book/entry/interface refused"
    requireFields json ([("source",toJson (BendSourceRepresentation.chooseTerm.show 0)),
      ("tagEncoding",toJson "bend-prelude-bool-sigma-unit-v1"),
      ("signedConstantPolicy",toJson "dynamic-bool-mux-v1"),
      ("inputWires",toJson ([1,2,3] : List Nat)),
      ("inputOrder",toJson (["selector","trueArm","falseArm"] : List String)),
      ("relation",descriptorToJson (BendLogicMux.descriptor (F := BabyBear) 0))] ++
      graphs (BendLogicMux.outputExpr (F := BabyBear)) (BendLogicMux.outputExpr (F := Rat)))
  else if schema == "dregg.bend.public-natural-expression.v1" then
    let order ← strings json "inputOrder"
    let arithmeticEntry ← string json "arithmeticEntry"
    let inputBits ← natural json "inputBits"
    let outputBits ← natural json "outputBits"
    let sourceBudget ← natural json "sourceBudget"
    if sourceFuel < sourceBudget then throw "native source fuel below admitted compiler reservation"
    let plaintextModulus ← natural json "plaintextModulus"
    let some plan := compileChecked (n := order.length) (p := 2013265921) core arithmeticEntry
        128 inputBits outputBits sourceBudget plaintextModulus
      | throw "actual natural source member/interface/profile refused"
    if decide (BendTT.Book.get core.book entry = some (worldDefinition entry plan.expression)) then
      if fits : plan.inputBits ≤ plan.outputBits then
        let expected := BendNaturalArtifact.artifact entry arithmeticEntry order core.book
          (← string json "surfaceSource") plan fits
        if expected == json then pure () else throw "natural source/model/circuit projection differs"
      else throw "invalid natural range width"
    else throw "native source wrapper differs from generated actual definition"
  else throw "compiler schema has no checked native source adapter"

/-- Every field here is checked by the executable mapping; it grants no release,
current state, key custody or encrypted input range authority. -/
structure Checked (artifact : BendWorldProgramCodec.Artifact) (compilerBytes : List UInt8) where
  json : Json
  formed : BendWorldProgramCodec.wellFormed artifact = true
  raw : String
  decoded : String.fromUTF8? ⟨compilerBytes.toArray⟩ = some raw
  compilerParsed : Json.parse raw = .ok json
  core : BendCoreAdmission.Checked
  surfaceExact : (artifact.source.modules[artifact.source.entryModule]?).map (fun m => m.bytes) =
    some (((string json "surfaceSource").toOption.getD "").toUTF8.toList)
  nativeCore : artifact.book = core.bytes
  nativeEntry : artifact.entry = (string json "entry").toOption.getD ""
  sourceVerified : verifySource json core artifact.entry ((artifact.profile.bounds[7]?).getD 0) = .ok ()
  planExact : artifact.plan = planId compilerBytes
  sourceProfile : artifact.profile.upstream = BendWorldSource.upstreamPin ∧
    artifact.profile.semantics = "bendtt-eval-walk-947db722-v1" ∧
    artifact.profile.arithmetic = "bendtt-structural-nat-exact-v1" ∧
    artifact.profile.evaluator = Minidregg.Kernel.BendNativeRun.evaluatorId ∧
    artifact.profile.charge = Minidregg.Kernel.BendNativeRun.chargeId
  carrier : artifact.program.jam = artifact.book ∧ artifact.program.evaluator = artifact.profile.evaluator ∧
    artifact.program.params = entryParams artifact.entry
  planBackend : artifact.backend = "bfv-public-source-v1"

/-- Source byte identity and regenerated source plan, not an operator-supplied
SHA. Parameters/current registration/disclosure/crypto validity stay receiving gates. -/
def check (artifact : BendWorldProgramCodec.Artifact) (compilerBytes : List UInt8) :
    Except String (Checked artifact compilerBytes) :=
  match decoded : String.fromUTF8? ⟨compilerBytes.toArray⟩ with
  | none => .error "compiler artifact UTF-8 refused"
  | some raw =>
    match compilerParsed : Json.parse raw with
    | .error why => .error why
    | .ok json => do
        if formed : BendWorldProgramCodec.wellFormed artifact = true then
          let core ← BendCoreAdmission.canonicalize (← string json "bookSource").toUTF8.toList
          if surfaceExact : (artifact.source.modules[artifact.source.entryModule]?).map (fun m => m.bytes) =
              some (((string json "surfaceSource").toOption.getD "").toUTF8.toList) then
            if nativeCore : artifact.book = core.bytes then
              if nativeEntry : artifact.entry = (string json "entry").toOption.getD "" then
                if sourceVerified : verifySource json core artifact.entry ((artifact.profile.bounds[7]?).getD 0) = .ok () then
                  if planExact : artifact.plan = planId compilerBytes then
                    if sourceProfile : artifact.profile.upstream = BendWorldSource.upstreamPin ∧
                        artifact.profile.semantics = "bendtt-eval-walk-947db722-v1" ∧
                        artifact.profile.arithmetic = "bendtt-structural-nat-exact-v1" ∧
                        artifact.profile.evaluator = Minidregg.Kernel.BendNativeRun.evaluatorId ∧
                        artifact.profile.charge = Minidregg.Kernel.BendNativeRun.chargeId then
                      if carrier : artifact.program.jam = artifact.book ∧
                          artifact.program.evaluator = artifact.profile.evaluator ∧
                          artifact.program.params = entryParams artifact.entry then
                        if planBackend : artifact.backend = "bfv-public-source-v1" then
                          pure ⟨json,formed,raw,decoded,compilerParsed,core,surfaceExact,nativeCore,nativeEntry,sourceVerified,planExact,
                            sourceProfile,carrier,planBackend⟩
                        else throw "native backend differs"
                      else throw "native source carrier differs"
                    else throw "native source semantic profile differs"
                  else throw "native plan identity differs from exact compiler bytes"
                else throw "source compiler or constructive projection refused"
              else throw "native source entry differs"
            else throw "native canonical Book differs"

          else throw "selected source Package bytes differ from captured source"

        else throw "native artifact/source Package structure refused"

end Minidregg.Compiler.BendArtifactBinding
