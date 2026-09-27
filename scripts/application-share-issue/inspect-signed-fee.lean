/- Source-owned read-only inspection of the exact finalized birth descriptor
inside a canonical share-issue signing plan. The native fixture compares this
signed fee with the payer's observed Book delta; no shell binary decoder or
second fee formula is involved. -/
import Kernel.ApplicationShareIssueAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Theory.ResourceBirth
open Minidregg.Kernel.ApplicationShareIssueAuthoring

def main (args : List String) : IO Unit := do
  let [path] := args
    | throw (IO.userError "usage: inspect-signed-fee PLAN.bin")
  let bytes ← IO.FS.readBinFile path
  let some plan := planCodec.decode bytes.toList
    | throw (IO.userError "noncanonical share-issue plan")
  let descriptorBytes ← match plan.birth.finalizedDraft with
    | .birth source _ => pure source
    | _ => throw (IO.userError "share-issue plan has no finalized birth")
  let some descriptor :=
      (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).decode
        descriptorBytes
    | throw (IO.userError "noncanonical finalized birth descriptor")
  IO.println descriptor.fee.amount
