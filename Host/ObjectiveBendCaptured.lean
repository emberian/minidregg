/- Generic captured-package composition/export. Explicit authored Partial bytes
supply composition meaning; no workshop fixture is substituted for a draft. -/
import Host.BendPackage
import Compiler.ObjectiveBendConstruction
import Compiler.ObjectiveBendPrototype
import Lean.Data.Json
namespace Minidregg.Host.ObjectiveBendCaptured
open Minidregg.Compiler
open ObjectiveBendComposition ObjectiveBendElaboration
set_option autoImplicit false

def produce (request : Lean.Json) (directory : String) : IO Lean.Json := do
  try
    let config : Except String (Lean.Json × String × Array Lean.Json) := do
      if (← BendPackage.string request "schema") != "dregg.objective-bend.capture-input.v1" then
        throw "unsupported captured composition schema"
      pure (← BendPackage.field request "package", ← BendPackage.string request "corePath",
        ← BendPackage.array request "partials")
    let .ok (packageInput, corePath, partialInputs) := config | throw (IO.userError "invalid captured composition request")
    let package ← match ← BendPackage.load packageInput with
      | .error error => throw (IO.userError error)
      | .ok package => pure package
    let raw ← IO.FS.readBinFile corePath
    let core ← match BendCoreAdmission.canonicalize raw.toList with
      | .error error => throw (IO.userError error)
      | .ok core => pure core
    if partialInputs.isEmpty then throw (IO.userError "no authored Partial artifacts: source entry alone does not declare composition interfaces")
    let mut layers : List Spec := []
    let mut artifacts : List ObjectiveBendPrototype.Partial := []
    for input in partialInputs do
      let .ok path := input.getStr? | throw (IO.userError "Partial path must be string")
      let bytes ← IO.FS.readBinFile path
      let some artifact := ObjectiveBendPrototype.decode bytes.toList | throw (IO.userError "noncanonical Partial artifact")
      if artifact.source != package then throw (IO.userError "Partial source Package differs from actual captured Package")
      let spec ← match ObjectiveBendPrototype.reflect artifact with
        | .error error => throw (IO.userError error)
        | .ok spec => pure spec
      artifacts := artifacts ++ [artifact]
      layers := layers ++ [spec]
    let some root := layers.getLast? | throw (IO.userError "no composed root")
    let construction ← match ObjectiveBendConstruction.construct core.book root layers with
      | .error error => throw (IO.userError (reprStr error))
      | .ok construction => pure construction
    IO.FS.createDirAll directory
    IO.FS.writeBinFile (directory ++ "/source.package.bin") ⟨(BendWorldSource.encode package).toArray⟩
    IO.FS.writeBinFile (directory ++ "/composed.bendtt") ⟨construction.core.bytes.toArray⟩
    let mut providers : List Lean.Json := []
    for i in List.finRange layers.length do
      for provision in layers[i].provisions do
        let selected : Selected := ⟨i.val, layers[i].id, provision⟩
        providers := providers ++ [Lean.Json.mkObj [
          ("owner", Lean.toJson selected.owner), ("provider", Lean.toJson selected.provider),
          ("selector", .str provision.interface.selector), ("sourceEntry", .str provision.entry),
          ("coreEntry", .str (coreName selected)), ("partialIdentity", Lean.toJson provision.source)]]
    return Lean.Json.mkObj [("schema", .str "dregg.objective-bend.capture-result.v1"),
      ("status", .str "checked-composition"),
      ("packageIdentity", Lean.toJson (BendWorldSource.packageId package).value),
      ("root", Lean.toJson root.id), ("partialIdentities", Lean.toJson (layers.map Spec.id)),
      ("providers", .arr providers.toArray),
      ("sourceCoreIdentity", Lean.toJson (BendWorldSource.sourceId core.bytes).value),
      ("composedCoreIdentity", Lean.toJson (BendWorldSource.sourceId construction.core.bytes).value),
      ("corePath", .str (directory ++ "/composed.bendtt")),
      ("qualification", .str "actual Package binding, canonical Partial reflection, lawful complete composition and checked exact method definitions; surface emission transcript/native wrapper qualification separate")]
  catch error => return Lean.Json.mkObj [("schema", .str "dregg.objective-bend.capture-result.v1"),
    ("status", .str "refused"), ("diagnostic", .str error.toString)]
end Minidregg.Host.ObjectiveBendCaptured

def main (args : List String) : IO UInt32 := do
  let [requestPath, directory, reportPath] := args | do
    IO.eprintln "usage: objective-bend-captured REQUEST_JSON OUTPUT_DIRECTORY REPORT_JSON"
    return 2
  let raw ← IO.FS.readFile requestPath
  let .ok request := Lean.Json.parse raw | do
    IO.eprintln "invalid request JSON"
    return 2
  let report ← Minidregg.Host.ObjectiveBendCaptured.produce request directory
  IO.FS.writeFile reportPath report.pretty
  pure 0
