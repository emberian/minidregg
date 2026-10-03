import Compiler.ObjectiveBendWorkshop
import Lean
import Theory.BendLiveMachine
import Compiler.BendClosureCompile
open Minidregg.Compiler
open Minidregg.Compiler.ObjectiveBendComposition
open Minidregg.Compiler.ObjectiveBendElaboration
open Minidregg.Compiler.ObjectiveBendLinker
open Minidregg.Compiler.ObjectiveBendWorkshop

def scopeJson (scope : Scope) : Lean.Json := .str (match scope with | .finalSelf => "finalSelf" | .priorSuper => "priorSuper")
def selectedJson (selected : Selected) : Lean.Json := Lean.Json.mkObj [
  ("owner", Lean.toJson selected.owner), ("provider", Lean.toJson selected.provider),
  ("selector", .str selected.provision.interface.selector),
  ("sourceModuleIndex", Lean.toJson selected.provision.source), ("sourceEntry", .str selected.provision.entry),
  ("coreEntry", .str (coreName selected)),
  ("interfaceType", .str (Minidregg.Theory.BendTT.Term.show selected.provision.interface.type 0))]
def layersJson (layers : List Spec) : Lean.Json :=
  let nodes := (List.finRange layers.length).map fun i =>
    let spec := layers[i]
    let provided := spec.provisions.map fun p => selectedJson ⟨i.val, spec.id, p⟩
    let required := spec.requirements.map fun r => Lean.Json.mkObj [
      ("scope", scopeJson r.scope), ("selector", .str r.interface.selector),
      ("selected", match resolve layers i.val r with | none => .null | some selected => selectedJson selected)]
    Lean.Json.mkObj [
      ("owner", Lean.toJson spec.id), ("parents", Lean.toJson spec.directParents),
      ("order", Lean.toJson spec.order),
      ("provided", .arr provided.toArray), ("required", .arr required.toArray)]
  .arr nodes.toArray

def expectedCard (revision : Nat) (allowed : Bool) (label : List Nat) : Minidregg.Theory.BendTT.Term :=
  let recommendation := pair (.Lab "CatalogReview.Recommendation")
    (pair (candidate revision) (pair (bytes [4])
      (pair (pair (.Lab (if allowed then "True" else "False")) unit) unit)))
  pair (.Lab "ReusableWorkshop.Card")
    (pair (candidate revision) (pair (bytes label) (pair recommendation unit)))

def observeClosure (book : Minidregg.Theory.BendTT.Book)
    (invocation : Minidregg.Theory.BendTT.Term) : Except String Minidregg.Theory.BendTT.Term := do
  let some compiled := BendClosureCompile.compile book invocation | throw "source closure compilation refused"
  let limits : Minidregg.Theory.BendClosureMachine.Limits := ⟨⟨1024,10,by decide⟩,256,256⟩
  let initial ← (Minidregg.Theory.BendClosureMachine.start limits compiled.library compiled.entry).mapError (fun _ => "closure start refused")
  let final := Minidregg.Theory.BendClosureMachine.run limits compiled.library 20000 initial
  match final.control with
  | .complete pointer =>
    let some decoded := Minidregg.Theory.BendClosureDecode.decode compiled.library.program final.heap 20000 pointer | throw "closure decode refused"
    pure decoded.term
  | _ => throw "closure runtime did not complete"

def executeCase (directory label : String) {layers : List Spec} {helpers : Minidregg.Theory.BendTT.Book}
    (linked : Linked helpers layers) (revision : Nat) (expectedLabel : List Nat) : IO Unit := do
  let selected ← match resolve layers 0 ⟨.finalSelf, presentationI⟩ with
    | none => throw (IO.userError "presentation absent")
    | some selected => pure selected
  let invocation : Minidregg.Theory.BendTT.Term := .App .Q2 (.Ref (coreName selected)) (candidate revision)
  match Minidregg.Theory.BendLiveMachine.executeChecked linked.core.book 100000 4096 invocation with
  | .refused _ count _ reason => throw (IO.userError (label ++ ": reference execution refused " ++ reprStr reason ++ " at " ++ toString count))
  | .complete result count _ _ =>
    let closureResult ← match observeClosure linked.core.book invocation with
      | .error reason => throw (IO.userError (label ++ ": " ++ reason))
      | .ok value => pure value
    if decide (closureResult = result) then pure ()
    else throw (IO.userError (label ++ ": closure/source result divergence"))
    if decide (result = expectedCard revision (revision == 1) expectedLabel) then
      let record := Lean.Json.mkObj [("status", .str "complete"), ("revision", Lean.toJson revision),
        ("entry", .str (coreName selected)), ("closureMatchesSource", .bool true), ("sourceEvalSteps", Lean.toJson count),
        ("result", .str (Minidregg.Theory.BendTT.Term.show result 0))]
      IO.FS.writeFile (directory ++ "/" ++ label ++ "-revision" ++ toString revision ++ "-execution.json") record.pretty
      IO.println (label ++ ": exact dynamic Card revision=" ++ toString revision ++ " steps=" ++ toString count)
    else throw (IO.userError (label ++ ": unexpected reference Card " ++ Minidregg.Theory.BendTT.Term.show result 0))

def exportCase (directory label : String) (source : BendCoreAdmission.Checked) (layers : List Spec) : IO Unit := do
  IO.FS.writeFile (directory ++ "/" ++ label ++ "-providers.json") (layersJson layers).pretty
  match linkSource source layers with
  | .error (.incompleteMethod owner requirement) =>
    let diagnostic := Lean.Json.mkObj [("status", .str "incomplete"),
      ("owner", Lean.toJson owner), ("scope", scopeJson requirement.scope),
      ("selector", .str requirement.interface.selector)]
    IO.FS.writeFile (directory ++ "/" ++ label ++ "-diagnostic.json") diagnostic.pretty
  | .error error => throw (IO.userError (reprStr error))
  | .ok linked =>
    IO.FS.writeBinFile (directory ++ "/" ++ label ++ ".bendtt") ⟨linked.core.bytes.toArray⟩
    let status := Lean.Json.mkObj [("status", .str "linked"),
      ("definitions", Lean.toJson linked.core.book.length)]
    IO.FS.writeFile (directory ++ "/" ++ label ++ "-diagnostic.json") status.pretty
    let expectedLabel := if label == "alternate" then [82,101,118,105,101,119,101,100] else [5]
    executeCase directory label linked 0 expectedLabel
    executeCase directory label linked 1 expectedLabel
    executeCase directory label linked 2 expectedLabel

def main (args : List String) : IO Unit := do
  match args with
  | [path, directory] =>
    IO.FS.createDirAll directory
    let raw ← IO.FS.readBinFile path
    let source ← match BendCoreAdmission.canonicalize raw.toList with
      | .error e => throw (IO.userError e)
      | .ok source => pure source
    let layers ← match specs source with
      | .error e => throw (IO.userError e)
      | .ok layers => pure layers
    exportCase directory "incomplete" source (layers.take 4)
    exportCase directory "complete" source (layers.take 5)
    exportCase directory "alternate" source layers
    IO.println "EXPORTED exact source-linked core Books, provider resolution, focused diagnostics"
  | _ => throw (IO.userError "expected emitted Book path + output directory")
