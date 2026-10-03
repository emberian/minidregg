/- Explicit ordinary-member Partial declarations become the actual canonical
prototype codec. Package loading binds the actual captured module/import bytes;
the open wrapper Book supplies exact requirements/provisions. Complete linking,
surface-emission correspondence, current authority and native execution remain
separate gates. This producer never substitutes a workshop fixture for a draft. -/
import Host.BendPackageInput
import Compiler.ObjectiveBendPrototype
import Lean.Data.Json

namespace Minidregg.Host.ObjectiveBendPartialAuthor
open Minidregg.Compiler
open ObjectiveBendComposition
set_option autoImplicit false

private def strings (value : Lean.Json) : Except String (List String) := do
  let values ← value.getArr?
  values.toList.mapM fun value => value.getStr?

private def naturals (value : Lean.Json) : Except String (List Nat) := do
  (← strings value).mapM fun text => do
    let some value := text.toNat? | throw "parent identity must be decimal"
    if toString value != text then throw "parent identity must be canonical decimal"
    pure value

private def requirement (value : Lean.Json) : Except String ObjectiveBendPrototype.RequirementRef := do
  let scope ← match ← BendPackage.string value "scope" with
    | "finalSelf" => pure Scope.finalSelf
    | "priorSuper" => pure Scope.priorSuper
    | _ => throw "requirement scope must be finalSelf or priorSuper"
  pure ⟨scope, ← BendPackage.string value "selector", ← BendPackage.string value "typeEntry"⟩

private def provision (value : Lean.Json) : Except String ObjectiveBendPrototype.ProvisionRef := do
  pure ⟨← BendPackage.string value "selector", ← BendPackage.string value "entry",
    ← strings (← BendPackage.field value "captures")⟩

private def parse (value : Lean.Json) :
    Except String (Lean.Json × String × List Nat × List Nat ×
      List ObjectiveBendPrototype.RequirementRef × List ObjectiveBendPrototype.ProvisionRef) := do
  if (← BendPackage.string value "schema") != "dregg.objective-bend.partial-input.v1" then
    throw "unsupported Partial authoring schema"
  pure (← BendPackage.field value "package", ← BendPackage.string value "partialCorePath",
    ← naturals (← BendPackage.field value "directParents"),
    ← naturals (← BendPackage.field value "ancestorOrder"),
    ← (← BendPackage.array value "required").toList.mapM requirement,
    ← (← BendPackage.array value "provided").toList.mapM provision)

private def checkedIO {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

def produce (request : Lean.Json) (output : String) : IO Lean.Json := do
  try
    let (packageInput, corePath, parents, ancestors, required, provided) ← checkedIO (parse request)
    let source ← checkedIO (← BendPackage.load packageInput)
    let raw ← IO.FS.readBinFile corePath
    let some text := String.fromUTF8? raw | throw (IO.userError "invalid Partial Book UTF-8")
    let book ← checkedIO (Minidregg.Theory.BendTT.Book.parse text)
    let canonical := BendCoreAdmission.encode book
    if canonical != raw.toList then throw (IO.userError "Partial Book must be canonical")
    let artifact : ObjectiveBendPrototype.Partial :=
      ⟨source, parents, ancestors, canonical, required, provided⟩
    let reflected ← checkedIO (ObjectiveBendPrototype.reflect artifact)
    IO.FS.createDirAll output
    IO.FS.writeBinFile (output ++ "/partial.bin") ⟨(ObjectiveBendPrototype.encode artifact).toArray⟩
    let requirements := reflected.requirements.map fun r => Lean.Json.mkObj [
      ("scope", .str (match r.scope with | .finalSelf => "finalSelf" | .priorSuper => "priorSuper")),
      ("selector", .str r.interface.selector),
      ("interfaceType", .str (Minidregg.Theory.BendTT.Term.show r.interface.type 0))]
    let provisions := reflected.provisions.map fun p => Lean.Json.mkObj [
      ("selector", .str p.interface.selector), ("entry", .str p.entry),
      ("interfaceType", .str (Minidregg.Theory.BendTT.Term.show p.interface.type 0)),
      ("capturedDataEntries", Lean.toJson p.captured.length)]
    return .mkObj [
      ("schema", .str "dregg.objective-bend.partial-result.v1"),
      ("status", .str "reflected-partial"),
      ("partialIdentity", .str (toString reflected.id)),
      ("packageIdentity", .str (toString (BendWorldSource.packageId source).value)),
      ("partialPath", .str (output ++ "/partial.bin")),
      ("directParents", .arr (parents.map (fun id => Lean.Json.str (toString id))).toArray),
      ("ancestorOrder", .arr (ancestors.map (fun id => Lean.Json.str (toString id))).toArray),
      ("required", .arr requirements.toArray), ("provided", .arr provisions.toArray),
      ("qualification", .str "actual captured Package + canonical open Book + exact Partial reflection; completion, surface wrapper correspondence, current publication/birth/invocation authority remain separate")]
  catch error => return .mkObj [
    ("schema", .str "dregg.objective-bend.partial-result.v1"),
    ("status", .str "refused"), ("diagnostic", .str error.toString)]

end Minidregg.Host.ObjectiveBendPartialAuthor

def main (args : List String) : IO UInt32 := do
  let [requestPath, directory, reportPath] := args | do
    IO.eprintln "usage: objective-bend-partial-author REQUEST_JSON OUTPUT_DIRECTORY REPORT_JSON"
    return 2
  let raw ← IO.FS.readFile requestPath
  let request ← match Lean.Json.parse raw with
    | .ok request => pure request
    | .error error => throw (IO.userError error)
  let report ← Minidregg.Host.ObjectiveBendPartialAuthor.produce request directory
  IO.FS.writeFile reportPath report.pretty
  pure 0
