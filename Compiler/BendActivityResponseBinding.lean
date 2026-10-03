/- Concrete source-typed response preparation for a completed persistent yield.
Every finite response has an actual machine successor and exact new source
origin. Native receiving still has to consume the current pending phase and
validate the current signed outcome; this pure producer cannot dispatch tools.
-/
import Compiler.BendActivityYieldSource
import Compiler.BendActivitySegment
import Theory.BendClosureResponseReady
import Theory.BendClosureResponseTyping

namespace Minidregg.Compiler.BendActivityResponseBinding
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

structure Prepared {core : BendCoreAdmission.Checked} {initial outputType : Term}
    {sourceLimits : BendRunCore.Limits}
    {checked : BendRunCore.Checked core initial outputType sourceLimits}
    {program : Program} {state : State}
    (bound : BendActivityYieldSource.Bound checked program state)
    (limits : Limits) (abi : BendClosureResponse.ABI)
    (pin : BendActivitySegment.TypePin) where
  signature : BendActivitySegment.Signature core pin
  continuationPointer : abi.continuation = bound.yielded.continuationPointer
  admitted : BendInvocationAdmission.Admission core.book bound.yielded.continuationSource
    (.All .Q1 BendClosureResponse.responseType signature.resultFamily)
  ready : BendClosureResponse.Ready limits program abi state

/-- Check the exact captured continuation, exact declared dependent signature,
and actual allocation/code readiness for both Bool outcomes before publishing
an external request. Refusal leaves the completed Activity unconsumed. -/
def prepare {core : BendCoreAdmission.Checked} {initial outputType : Term}
    {sourceLimits : BendRunCore.Limits}
    {checked : BendRunCore.Checked core initial outputType sourceLimits}
    {program : Program} {state : State}
    (bound : BendActivityYieldSource.Bound checked program state)
    (limits : Limits) (abi : BendClosureResponse.ABI)
    (pin : BendActivitySegment.TypePin) (checkerTicks : Nat) :
    Option (Prepared bound limits abi pin) := do
  let signature ← BendActivitySegment.signature core pin
  if pointer : abi.continuation = bound.yielded.continuationPointer then
    let admitted ← BendInvocationAdmission.admit core.book checkerTicks bound.yielded.continuationSource
      (.All .Q1 BendClosureResponse.responseType signature.resultFamily)
    let .ok ready := BendClosureResponse.prepare limits program abi state | none
    some ⟨signature,pointer,admitted,ready⟩
  else none

def Prepared.origin {core : BendCoreAdmission.Checked} {initial outputType : Term}
    {sourceLimits : BendRunCore.Limits}
    {checked : BendRunCore.Checked core initial outputType sourceLimits}
    {program : Program} {state : State}
    {bound : BendActivityYieldSource.Bound checked program state}
    {limits : Limits} {abi : BendClosureResponse.ABI} {pin : BendActivitySegment.TypePin}
    (prepared : Prepared bound limits abi pin) (bit : Bool) : BendActivitySegment.ResponseOrigin :=
  ⟨abi.continuation,(prepared.ready.response bit).inputPointer,bit,pin⟩

/-- The origin uses the exact pointer returned by the actual response allocator,
not a pointer convention. Immutable captured heap data retains its exact source. -/
def Prepared.originSource {core : BendCoreAdmission.Checked} {initial outputType : Term}
    {sourceLimits : BendRunCore.Limits}
    {checked : BendRunCore.Checked core initial outputType sourceLimits}
    {program : Program} {state : State}
    {bound : BendActivityYieldSource.Bound checked program state}
    {limits : Limits} {abi : BendClosureResponse.ABI} {pin : BendActivitySegment.TypePin}
    (prepared : Prepared bound limits abi pin) (bit : Bool) :
    BendActivitySegment.ResponseSource program (prepared.ready.response bit).state.heap
      (prepared.origin bit) := by
  have retained : Denotes program state.heap abi.continuation bound.yielded.continuationSource := by
    rw [prepared.continuationPointer]
    exact bound.yielded.continuationExact
  exact ⟨bound.yielded.continuationSource,
    BendClosureResponse.continuation_retained (prepared.ready.response bit) retained,
    (prepared.ready.response bit).inputExact⟩

/-- General over every declared response. This is the actual source application
and its dependent output type, plus zero source steps in the new segment. It is
not an Eval transition from the preceding completed Plan/continuation pair. -/
theorem Prepared.response_typed {core : BendCoreAdmission.Checked} {initial outputType : Term}
    {sourceLimits : BendRunCore.Limits}
    {checked : BendRunCore.Checked core initial outputType sourceLimits}
    {program : Program} {state : State}
    {bound : BendActivityYieldSource.Bound checked program state}
    {limits : Limits} {abi : BendClosureResponse.ABI} {pin : BendActivitySegment.TypePin}
    (prepared : Prepared bound limits abi pin) (bit : Bool) :
    BendClosureSimulation.StateDenotes core.book program (prepared.ready.response bit).state
      (prepared.originSource bit).initial ∧
    Typed core.book [] (prepared.originSource bit).initial
      (Term.inst prepared.signature.resultFamily (BendClosureResponse.responseTerm bit)) ∧
    (prepared.ready.response bit).state.sourceSteps = 0 := by
  have retained : Denotes program state.heap abi.continuation bound.yielded.continuationSource := by
    rw [prepared.continuationPointer]
    exact bound.yielded.continuationExact
  have typed := BendClosureResponse.resume_source_typed limits program abi state bit
    (prepared.ready.response bit) (prepared.ready.response_exact bit)
    bound.yielded.continuationSource prepared.signature.resultFamily retained
    (BendActivityYieldSource.continuation_value bound) prepared.admitted.typed
  exact ⟨typed.1,typed.2,(prepared.ready.response bit).newSegment⟩

#assert_axioms prepare
#assert_axioms Prepared.originSource
#assert_axioms Prepared.response_typed
end Minidregg.Compiler.BendActivityResponseBinding
