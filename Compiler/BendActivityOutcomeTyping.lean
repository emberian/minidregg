/- Exact native outcome-to-source response join. This consumes the retained
pending checkpoint and the actual response allocator equation. Publication true
means native application publication, not external provider success. -/
import Kernel.BendActivityOutcome
import Compiler.BendActivityResponseBinding

namespace Minidregg.Compiler.BendActivityOutcomeTyping
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

private def responseState (limits : Limits) (program : Program)
    (abi : BendClosureResponse.ABI) (before : State) (bit : Bool) :
    Except BendClosureResponse.Reject State :=
  (BendClosureResponse.resume limits program abi before bit).map (fun result => result.state)

theorem response_bit {config : Config} {opened : Opened config}
    {action : BendActivityOutcome.Action}
    {origin : BendActivityDispatch.Origin config opened action.dispatch}
    (admitted : BendActivityOutcome.Admitted origin) :
    admitted.resumed.bit = admitted.resolution.bit := by
  have decoded := admitted.resumed.responseExact
  cases bitEq : admitted.resolution.bit <;>
    simp [BendActivityOutcome.outcome, bitEq, BendClosureResponse.decodeResponse] at decoded <;>
    exact decoded.symm

/-- Actual native resumption is the prequalified response for the same retained
request. Equality is of whole machine states, including heap, cache and count. -/
theorem resumed_state {config : Config} {opened : Opened config}
    {action : BendActivityOutcome.Action}
    {origin : BendActivityDispatch.Origin config opened action.dispatch}
    (admitted : BendActivityOutcome.Admitted origin) :
    admitted.resumed.record.checkpoint.state =
      (origin.pending.prepared.responses.ready.response admitted.resolution.bit).state := by
  have pendingEq := admitted.resumed.pendingExact
  rw [origin.pending.pending.pendingExact] at pendingEq
  have pending := Option.some.inj pendingEq
  have actual :
      responseState origin.pending.program.limits origin.pending.program.compiled.library.program
        admitted.resumed.pending.response origin.pending.pending.record.checkpoint.state
        admitted.resumed.bit = .ok admitted.resumed.resumed.state := by
    simp [responseState, admitted.resumed.ran]
  have retained := congrArg (fun checkpoint => checkpoint.state) origin.pending.pending.retained
  rw [← pending, retained, response_bit admitted] at actual
  have expected :
      responseState origin.pending.program.limits origin.pending.program.compiled.library.program
        origin.pending.action.response origin.pending.before.checkpoint.state
        admitted.resolution.bit =
      .ok (origin.pending.prepared.responses.ready.response admitted.resolution.bit).state := by
    simp [responseState, origin.pending.prepared.responses.ready.response_exact]
  rw [expected] at actual
  exact admitted.resumed.stateExact.trans (Except.ok.inj actual).symm

/-- The actual resumed native record has the request-indexed dependent source
type and starts a new pure segment at zero source steps. This is not an Eval
edge from the previous completed Plan/continuation pair. -/
theorem resumed_source_typed {config : Config} {opened : Opened config}
    {action : BendActivityOutcome.Action}
    {origin : BendActivityDispatch.Origin config opened action.dispatch}
    (admitted : BendActivityOutcome.Admitted origin) :
    BendClosureSimulation.StateDenotes origin.pending.program.core.book
      origin.pending.program.compiled.library.program admitted.resumed.record.checkpoint.state
      (origin.pending.prepared.responses.originSource admitted.resolution.bit).initial ∧
    Typed origin.pending.program.core.book []
      (origin.pending.prepared.responses.originSource admitted.resolution.bit).initial
      (Term.inst origin.pending.prepared.responses.signature.resultFamily
        (BendClosureResponse.responseTerm admitted.resolution.bit)) ∧
    admitted.resumed.record.checkpoint.state.sourceSteps = 0 := by
  rw [resumed_state admitted]
  exact origin.pending.prepared.responses.response_typed admitted.resolution.bit

#assert_axioms response_bit
#assert_axioms resumed_state
#assert_axioms resumed_source_typed
end Minidregg.Compiler.BendActivityOutcomeTyping
