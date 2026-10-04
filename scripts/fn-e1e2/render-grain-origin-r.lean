/-
Render a fresh fn R source from an accepted Mini grain publication. Mini's
existing export-evidence command first selects the exact accepted signed call;
this script independently re-admits its package, checks the named source
coordinates, and authors only the strict application MIME source. fn still
owns hybrid signing, Store admission, peering, and source identity.
The source bytes are `Host.GrainOriginSource.render`'s (with
`ArticleContext.application`), the one renderer; this script adds only the IO.

Usage under the pinned Mini tree:
  lake env lean --run scripts/fn-e1e2/render-grain-origin-r.lean \
    HOST CONFIG.json PACKAGE.bin GRAIN-TASK PARENT-TASK PUBLICATION-TARGET GROUP RFC-DATE R.source
-/
import Host.GrainOriginSource
import Lean.Data.Json

open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Host.GrainOriginSource

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [hostPath, configPath, packagePath, grainText, parentText,
       targetText, group, date, outputPath] := args
    | throw (IO.userError
        "usage: render-grain-origin-r.lean HOST CONFIG.json PACKAGE.bin GRAIN-TASK PARENT-TASK PUBLICATION-TARGET GROUP RFC-DATE R.source")
  let some grainTask := grainText.toNat?
    | throw (IO.userError "grain task must be decimal")
  let some parentTask := parentText.toNat?
    | throw (IO.userError "parent task must be decimal")
  let some publicationTarget := targetText.toNat?
    | throw (IO.userError "publication target must be decimal")
  let output := System.FilePath.mk outputPath
  require (!(← output.pathExists)) "refusing to replace an existing R source"
  let verificationPath := outputPath ++ ".verified.json"
  require (!(← (System.FilePath.mk verificationPath).pathExists))
    "refusing to replace an existing Mini verification result"
  let packageBytes := (← IO.FS.readBinFile packagePath).toList
  let .ok package := FnEvidenceCodec.decodeChecked packageBytes
    | throw (IO.userError "Mini evidence package is noncanonical or exceeds its profile")
  let result ← IO.Process.output { cmd := hostPath, args := #[configPath, "verify-evidence", packagePath, verificationPath] }
  require (result.exitCode == 0) "Mini host did not re-admit the original accepted package"
  let receipt := package.originalReceipt
  let verification ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile verificationPath))
  require (verification.getObjValAs? String "type" == .ok "verified-mini-native-prefix-v1" &&
    verification.getObjValAs? String "transactionId" == .ok (toString receipt.transactionId.value) &&
    verification.getObjValAs? String "eventId" == .ok (toString receipt.eventId.value) &&
    verification.getObjValAs? String "acceptedCount" == .ok (toString receipt.acceptedCount))
    "Mini verification result differs from package receipt"
  let rendered ← IO.ofExcept (render packageBytes receipt
    (ArticleContext.application group date) ⟨grainTask, parentTask, publicationTarget⟩)
  IO.FS.writeBinFile output rendered.source.toByteArray
  IO.println s!"R source: {rendered.messageId}; Mini accepted={receipt.acceptedCount}; publication target={publicationTarget}"
