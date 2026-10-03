/- Sealed source-package producer. Reads only the explicitly listed files and
computes Mini cSHAKE import identities from their exact bytes. SHA transcript
pins are not relabeled as Mini IDs. No import resolution or source execution.
Input schema dregg.bend.package-input.v1; all integer fields decimal strings.
-/
import Compiler.BendWorldSource
import Lean.Data.Json

open Minidregg.Compiler
open Minidregg.Compiler.BendWorldSource

namespace Minidregg.Host.BendPackage
set_option autoImplicit false

def field (json : Lean.Json) (name : String) : Except String Lean.Json :=
  json.getObjVal? name
def string (json : Lean.Json) (name : String) : Except String String := do
  (← field json name).getStr?
def natural (json : Lean.Json) (name : String) : Except String Nat := do
  let value ← string json name
  let some result := value.toNat? | throw s!"{name}: expected decimal natural"
  if toString result = value then pure result else throw s!"{name}: noncanonical natural"
def array (json : Lean.Json) (name : String) : Except String (Array Lean.Json) := do
  (← field json name).getArr?

def load (json : Lean.Json) : IO (Except String Package) := do
  try
    let parsed : Except String (Array Lean.Json × Nat × String) := do
      if (← string json "schema") != "dregg.bend.package-input.v1" then
        throw "unknown sealed package input schema"
      pure (← array json "modules", ← natural json "entryModule", ← string json "entryDefinition")
    let .ok (sources, entryModule, entryDefinition) := parsed
      | return parsed.map (fun _ => ⟨[], 0, ""⟩)
    if sources.size > 256 then return .error "sealed module bound exceeded"
    let mut modules : List Module := []
    let mut totalBytes := 0
    for source in sources do
      let details : Except String (String × String × Array Lean.Json) := do
        pure (← string source "name", ← string source "sourcePath", ← array source "imports")
      let .ok (name, path, rawImports) := details
        | return details.map (fun _ => ⟨[], 0, ""⟩)
      let raw ← IO.FS.readBinFile path
      totalBytes := totalBytes + raw.size
      if totalBytes > 4194304 then return .error "sealed source byte bound exceeded"
      let imports : Except String (List Import) := do
        rawImports.toList.mapM fun edge => do
          let index ← natural edge "module"
          let some dependency := modules[index]? | throw "import must name an earlier sealed module"
          pure ⟨← string edge "alias", index, sourceId dependency.bytes⟩
      let .ok imported := imports | return imports.map (fun _ => ⟨[], 0, ""⟩)
      modules := modules ++ [⟨name, raw.toList, imported⟩]
    let package : Package := ⟨modules, entryModule, entryDefinition⟩
    if wellFormed package then return .ok package else return .error "malformed sealed source manifest"
  catch error => return .error error.toString

end Minidregg.Host.BendPackage

