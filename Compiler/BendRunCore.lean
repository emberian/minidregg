/- Pure source-run evidence below the native resource transaction dependency.
The native receiver constructs initial from its independently admitted input,
selects the exact immutable Book/entry and output ABI, then consumes this witness
when checking complete native effects and current policy. This module has no
native Payload import and cannot authorize an effect or invent a funding token.
-/
import Compiler.BendCoreAdmission
import Compiler.BendInvocationAdmission
import Theory.BendLiveMachine
import Compiler.BendSourceByteCodec

namespace Minidregg.Compiler.BendRunCore
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.BendTT
set_option autoImplicit false

/-- All limits are public invocation/profile bounds. Source count remains an
internal witness; it is not copied into public fees or refund metadata. -/
structure Limits where
  checkerTicks : Nat
  classificationTicks : Nat
  sourceSteps : Nat
  outputTermSize : Nat
  deriving DecidableEq, Repr

/-- This source evidence is created by the actual source checker and execution.
The native binding additionally proves `initial` is derived from current
admitted observations/typed args, and `result` lowers through the selected ABI. -/
structure Checked (core : BendCoreAdmission.Checked) (initial outputType : BendTT.Term)
    (limits : Limits) where
  private mk ::
  admission : BendInvocationAdmission.Admission core.book initial outputType
  result : BendTT.Term
  sourceCount : Nat
  trace : BendLiveMachine.Trace core.book sourceCount initial result
  value : Value core.book result
  countBound : sourceCount ≤ limits.sourceSteps
  outputBound : Term.size result ≤ limits.outputTermSize

inductive Refusal where
  | invocationAdmission
  | executionCapacity
  | executionDiagnostic
  | outputCapacity
  deriving DecidableEq, Repr

/-- Admission and trace stay attached. A source checker or execution diagnostic
is a pre-admission refusal, never a proof that the typed term has no value.
Capacity exhaustion never switches to another privacy/backend profile. -/
def check (core : BendCoreAdmission.Checked) (initial outputType : BendTT.Term)
    (limits : Limits) : Except Refusal (Checked core initial outputType limits) := do
  let some admission := BendInvocationAdmission.admit core.book limits.checkerTicks initial outputType
    | throw .invocationAdmission
  match BendLiveMachine.executeChecked core.book limits.classificationTicks limits.sourceSteps initial with
  | .refused _ _ _ reason =>
      match reason with
      | .ticks => throw .executionCapacity
      | _ => throw .executionDiagnostic
  | .complete result count trace value =>
      if bounded : count ≤ limits.sourceSteps then
        if output : Term.size result ≤ limits.outputTermSize then
          pure ⟨admission, result, count, trace, value, bounded, output⟩
        else throw .outputCapacity
      else throw .executionCapacity

/-- The complete exact result, including live rewrite evidence, reaches the
native decoder. No optimized compiler erased value is substituted here. -/
theorem exact_source_result {core : BendCoreAdmission.Checked} {initial outputType : BendTT.Term}
    {limits : Limits} (checked : Checked core initial outputType limits) :
    BendLiveMachine.Trace core.book checked.sourceCount initial checked.result := checked.trace

theorem actual_invocation_type {core : BendCoreAdmission.Checked} {initial outputType : BendTT.Term}
    {limits : Limits} (checked : Checked core initial outputType limits) :
    Typed core.book [] initial outputType := checked.admission.typed

theorem source_bound {core : BendCoreAdmission.Checked} {initial outputType : BendTT.Term}
    {limits : Limits} (checked : Checked core initial outputType limits) :
    checked.sourceCount ≤ limits.sourceSteps := checked.countBound

/-- Byte-return profiles decode the whole exact typed source value. Structured
Plan/Surface/Card profiles instead use their independently bound source-shape
lowerer on `checked.result`; neither is a caller-provided effect certificate. -/
def resultBytes {core : BendCoreAdmission.Checked} {initial outputType : BendTT.Term}
    {limits : Limits} (checked : Checked core initial outputType limits) : Option (List UInt8) :=
  BendSourceRepresentation.decodeBytes checked.result

end Minidregg.Compiler.BendRunCore
