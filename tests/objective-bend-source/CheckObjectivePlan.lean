import Compiler.ObjectiveBendPlanAdapter
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Compiler.ObjectiveBendPlanAdapter
open Minidregg.Compiler.ObjectiveNativeScalarBinding
private def hex (bytes : List UInt8) : String := String.ofList (bytes.flatMap fun byte =>
  let chars := "0123456789abcdef".toList
  [chars[byte.toNat/16]!,chars[byte.toNat%16]!])
private def root := hex (rootCodec.encode ⟨11⟩)
private def ref : Term := .record [("resource",.nat 1),("root",.label root)]
private def source : Term := .app (.lam (.record [
  ("reads",.record [("0",ref)]),
  ("effects",.record [("0",.record [("ref",ref),("field",.nat 0),
    ("before",.bound 0),("after",.binary .add (.bound 0) (.nat 1))])])])) (.nat 7)
def main : IO Unit := do
  IO.println s!"CANONICAL SAMPLE ROOT {root}"
  let .ok executed := execute ⟨4096,1024⟩ ⟨4096,4096,65536⟩ source
    | throw (IO.userError "actual full source Plan extraction refused")
  let extracted := executed.extraction
  let some plan := decode extracted.result.value | throw (IO.userError "actual computed scalar Plan decode refused")
  let [effect] := plan.effects | throw (IO.userError "computed effects missing")
  let [write] := effect.writes | throw (IO.userError "computed write missing")
  if write.before != 7 || write.after != 8 || effect.ref.root.value != 11 then
    throw (IO.userError "source computation lost in native scalar Plan")
  let .record fields := extracted.result.value | throw (IO.userError "nonrecord output")
  if (decode (.record (fields++[("returns",.record [])]))).isSome then
    throw (IO.userError "unsupported return field silently ignored")
  let .record [("reads",reads),("effects",.record [("0",effectData)])] := extracted.result.value
    | throw (IO.userError "unexpected source shape")
  if (decode (.record [("reads",reads),("effects",.record [("1",effectData)])])).isSome then
    throw (IO.userError "noncontiguous effect order ignored")
  if (reference (.record [("resource",.natural 1),("root",.label root.toUpper)])).isSome then
    throw (IO.userError "noncanonical root accepted")
  IO.println "CORE4 COMPUTED AFTER=BEFORE+1 FULL DATA TO NATIVE SCALAR PLAN PASS; UNKNOWN RETURN/ORDINAL/ROOT REFUSERS PASS; NOT NATIVE ADMISSION"
