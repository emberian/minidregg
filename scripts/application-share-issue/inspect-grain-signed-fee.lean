/- Read the exact Book fee from a canonical event-22 grain-backed share Plan.
The joint grain source carries a finalized ordinary birth descriptor; no
shell-side tariff formula or binary codec is used by the acceptance fixture. -/
import Kernel.ApplicationShareIssueGrainAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Theory.ResourceBirth
open Minidregg.Kernel.ApplicationShareIssueGrainAuthoring

def main (args : List String) : IO Unit := do
  let [path] := args
    | throw (IO.userError "usage: inspect-grain-signed-fee PLAN.bin")
  let bytes ← IO.FS.readBinFile path
  let some plan := planCodec.decode bytes.toList
    | throw (IO.userError "noncanonical grain-backed share Plan")
  let finalized ← match plan.birth.finalizedDraft with
    | .birth bytes _ => pure bytes
    | _ => throw (IO.userError "grain-backed share Plan is not a birth")
  let some draft := GrainResourceBirthHostCodec.finalizedCodec.decode finalized
    | throw (IO.userError "noncanonical finalized grain birth")
  let some source := GrainResourceBirthHostCodec.sourceCodec.decode draft.sourceBytes
    | throw (IO.userError "noncanonical finalized grain source")
  IO.println source.birth.fee.amount
