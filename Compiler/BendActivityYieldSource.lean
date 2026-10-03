/- Join the actual heap yield to existing exact source-run evidence. This is
per-invocation translation validation, not a claimed whole-controller simulation.
Current Activity receiving must bind the checked initial term to its retained
segment origin, source publication and input observations before granting effects.
-/
import Compiler.BendActivityYield
import Compiler.BendRunCore
import Theory.BendClosureResponse

namespace Minidregg.Compiler.BendActivityYieldSource
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

structure Bound {core : BendCoreAdmission.Checked} {initial outputType : Term}
    {limits : BendRunCore.Limits}
    (checked : BendRunCore.Checked core initial outputType limits)
    (program : Program) (state : State) where
  yielded : BendActivityYield.Extracted program state
  resultExact : checked.result = .Tup .Q1 yielded.planSource yielded.continuationSource
  countExact : checked.sourceCount = state.sourceSteps

/-- Refuse unless both the complete source value and source-step count agree
with the actual controller checkpoint. Source-run evidence was produced by the
existing checked source evaluator; the heap is not used as an output oracle. -/
def bind {core : BendCoreAdmission.Checked} {initial outputType : Term}
    {limits : BendRunCore.Limits}
    (checked : BendRunCore.Checked core initial outputType limits)
    (program : Program) (state : State) (decodeTicks : Nat) :
    Option (Bound checked program state) := do
  let yielded ← BendActivityYield.extract program decodeTicks state
  if resultExact : checked.result = .Tup .Q1 yielded.planSource yielded.continuationSource then
    if countExact : checked.sourceCount = state.sourceSteps then
      some ⟨yielded,resultExact,countExact⟩
    else none
  else none

theorem source_trace {core : BendCoreAdmission.Checked} {initial outputType : Term}
    {limits : BendRunCore.Limits} {checked : BendRunCore.Checked core initial outputType limits}
    {program : Program} {state : State} (bound : Bound checked program state) :
    BendLiveMachine.Trace core.book state.sourceSteps initial
      (.Tup .Q1 bound.yielded.planSource bound.yielded.continuationSource) := by
  rw [← bound.resultExact, ← bound.countExact]
  exact checked.trace

theorem continuation_value {core : BendCoreAdmission.Checked} {initial outputType : Term}
    {limits : BendRunCore.Limits} {checked : BendRunCore.Checked core initial outputType limits}
    {program : Program} {state : State} (bound : Bound checked program state) :
    Value core.book bound.yielded.continuationSource := by
  have value := checked.value
  rw [bound.resultExact] at value
  cases value with
  | tup _ second => exact second

/-- This actual source checker ties the exact captured closure to the finite
response input type and a requested result type. The native request must retain
that result type/ABI, not replace it with a schema digest or an untyped callback. -/
def checkContinuation {core : BendCoreAdmission.Checked} {initial outputType : Term}
    {limits : BendRunCore.Limits} {checked : BendRunCore.Checked core initial outputType limits}
    {program : Program} {state : State} (bound : Bound checked program state)
    (checkerTicks : Nat) (resultType : Term) :
    Option (BendInvocationAdmission.Admission core.book bound.yielded.continuationSource
      (.All .Q1 BendClosureResponse.responseType resultType)) :=
  BendInvocationAdmission.admit core.book checkerTicks bound.yielded.continuationSource
    (.All .Q1 BendClosureResponse.responseType resultType)

#assert_axioms bind
#assert_axioms source_trace
#assert_axioms continuation_value
#assert_axioms checkContinuation
end Minidregg.Compiler.BendActivityYieldSource
