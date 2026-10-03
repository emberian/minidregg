/- Receive the exact existing linked Workshop Books. This checks full structural
Card decoding and policy binding after actual source execution; it does not
simulate native install, private custody, payments or governing authority. -/
import Compiler.WorkshopCardReturn
open Minidregg.Compiler
open Minidregg.Compiler.WorkshopCardReturn
open Minidregg.Theory.BendTT

def receiveCase (core : BendCoreAdmission.Checked) (entryName : String)
    (label : List UInt8) (revision : Nat) : IO Unit := do
  let candidate : Candidate := ⟨[1], [2], revision⟩
  let entry ← match BendCoreAdmission.entry core entryName with
    | .error error => throw (IO.userError error)
    | .ok entry => pure entry
  if interfaceExact : entry.definition.T =
      .All .Q2 (.Ref "CatalogReview.Candidate") (.Ref "ReusableWorkshop.Card") then
    let call : Invocation core candidate := ⟨entry, interfaceExact⟩
    let evaluated ← match execute core 100000 4096 call.initial with
      | none => throw (IO.userError "executed source Card did not decode")
      | some evaluated => pure evaluated
    let expected : Card := ⟨candidate, label, ⟨candidate, [4], revision == 1⟩⟩
    if evaluated.card != expected then throw (IO.userError "whole decoded Card changed")
    if matches evaluated.card candidate [4] != true then throw (IO.userError "actual candidate/policy binding refused")
    if matches evaluated.card candidate [5] != false then throw (IO.userError "changed policy silently admitted")
    if matches evaluated.card ⟨[1], [2], revision+1⟩ [4] != false then
      throw (IO.userError "changed Candidate silently admitted")
    if decodePayload (encode evaluated.card) != some expected then
      throw (IO.userError "canonical complete Card payload changed")
    IO.println ("WORKSHOP CARD RECEIVE PASS " ++ entryName ++ " revision=" ++ toString revision ++
      " sourceSteps=" ++ toString evaluated.count)
  else throw (IO.userError "selected source method has wrong actual interface")

def receiveBook (path entry : String) (label : List UInt8) : IO Unit := do
  let raw ← IO.FS.readBinFile path
  let core ← match BendCoreAdmission.admit raw.toList with
    | .error error => throw (IO.userError error)
    | .ok core => pure core
  for revision in [0,1,2] do receiveCase core entry label revision

def main (args : List String) : IO Unit := do
  match args with
  | [complete, alternate] =>
    receiveBook complete "objective.4.3.presentation" [5]
    receiveBook alternate "objective.6.5.presentation" [82,101,118,105,101,119,101,100]
  | _ => throw (IO.userError "usage: RunCardReturn.lean complete.bendtt alternate.bendtt")
