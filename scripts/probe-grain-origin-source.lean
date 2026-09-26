/-
Check reusable Mini grain-origin source construction against an already
exported, independently verified original package and its recorded R bytes.
The receipt below is read from the package only for this source-byte probe;
production callers pass the result of native `verify-evidence` instead.

Usage: lake env lean --run scripts/probe-grain-origin-source.lean \
  PACKAGE.bin EXPECTED-R.source GRAIN-TASK PARENT-TASK PUBLICATION-TARGET GROUP RFC-DATE
-/
import Host.GrainOriginSource

open Minidregg.Compiler
open Minidregg.Host.GrainOriginSource

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def main (args : List String) : IO Unit := do
  let [packagePath, expectedPath, grainText, parentText, publicationText, group, date] := args
    | throw (IO.userError "usage: probe-grain-origin-source PACKAGE EXPECTED GRAIN PARENT PUBLICATION GROUP DATE")
  let some grainTask := grainText.toNat?
    | throw (IO.userError "grain task must be decimal")
  let some parentTask := parentText.toNat?
    | throw (IO.userError "parent task must be decimal")
  let some publicationTarget := publicationText.toNat?
    | throw (IO.userError "publication target must be decimal")
  let packageBytes := (← IO.FS.readBinFile packagePath).toList
  let expectedBytes := (← IO.FS.readBinFile expectedPath).toList
  let .ok package := FnEvidenceCodec.decodeChecked packageBytes
    | throw (IO.userError "probe package does not decode under selected profile")
  let context := ArticleContext.application group date
  let selection : Selection := ⟨grainTask, parentTask, publicationTarget⟩
  let .ok rendered := render packageBytes package.originalReceipt context selection
    | throw (IO.userError "valid accepted grain publication did not render")
  unless ResourceBirthCodec.bytesEqual rendered.source expectedBytes do
    throw (IO.userError "reusable renderer changed exact recorded R source bytes")
  unless rejected (render packageBytes { package.originalReceipt with
      acceptedCount := package.originalReceipt.acceptedCount + 1 } context selection) do
    throw (IO.userError "renderer accepted a mismatched independent receipt")
  unless rejected (render packageBytes package.originalReceipt
      { context with subject := "bad\r\nInjected: yes" } selection) do
    throw (IO.userError "renderer accepted CRLF header injection")
  unless rejected (render packageBytes package.originalReceipt context
      { selection with publicationTarget := publicationTarget + 1 }) do
    throw (IO.userError "renderer accepted absent named publication target")
  IO.println s!"PASS grain origin source: {rendered.source.length} exact bytes; receipt, header, and target negatives rejected"
