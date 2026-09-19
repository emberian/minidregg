/- Kernel-computed accepting/refusing witnesses over the same source predicate
installed by AgentGrain. These do not claim physical stop or durable receiving
integration: those require the native host acceptance tests. -/
import Kernel.AgentGrain

namespace Minidregg.Kernel.AgentGrain
open Minidregg.Pred
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def running : State := ⟨8, 1, 100, 0⟩
private def pending : State := reserve running 40

theorem initial_attach_accepted : accepts ⟨0,0,100,0⟩ ⟨1,1,100,0⟩ = true := by decide
theorem reservation_accepted : accepts running pending = true := by decide
theorem overspend_refused : accepts running (reserve running 101) = false := by decide
theorem negative_reservation_refused : accepts running (reserve running (-1)) = false := by decide
theorem second_reservation_refused : accepts pending (reserve pending 1) = false := by decide
theorem settlement_accepted : accepts pending (settle pending 30) = true := by decide
theorem excess_refund_refused : accepts pending (settle pending (-1)) = false := by decide
theorem unreserved_charge_refused : accepts pending (settle pending 41) = false := by decide
theorem hard_trip_accepted : accepts pending (trip pending) = true := by decide
theorem fence_without_generation_refused : accepts pending { pending with status := 5 } = false := by decide
theorem reconnect_before_reconcile_refused :
    accepts (trip pending) ⟨10,1,60,40⟩ = false := by decide
theorem late_result_reconciliation_accepted :
    accepts (trip pending) (settle (trip pending) 30) = true := by decide
theorem stale_generation_after_trip_refused :
    accepts (trip pending) ⟨8,1,70,0⟩ = false := by decide
theorem soft_detach_preserves_authority : accepts ⟨8,2,100,0⟩ ⟨8,2,100,0⟩ = true := by decide
theorem soft_detach_does_not_reset_budget : accepts ⟨8,2,60,0⟩ ⟨8,2,100,0⟩ = false := by decide
theorem soft_pending_detach_accepted : accepts ⟨8,4,60,40⟩ ⟨8,4,60,40⟩ = true := by decide
theorem cancellation_accepted : accepts pending ⟨9,7,60,40⟩ = true := by decide
theorem cancelled_revival_refused : accepts ⟨9,6,60,0⟩ ⟨10,1,60,0⟩ = false := by decide
theorem management_locked :
    eval policy ⟨[]⟩ ⟨[("request/verb",4)]⟩ = false := by decide
theorem revocation_management_locked :
    eval policy ⟨[]⟩ ⟨[("request/verb",5)]⟩ = false := by decide
theorem explicitly_governed_revocation_management :
    eval (policy (.eq "request/subject" 7)) ⟨[]⟩
      ⟨[("request/verb",5),("request/subject",7)]⟩ = true := by decide
theorem missing_state_refused : eval transitionPolicy ⟨[]⟩ ⟨[]⟩ = false := by decide

theorem stale_worker_refused :
    eval (executionCaveat 8) ⟨[]⟩
      ⟨("request/verb",2) :: slots ⟨10,1,60,0⟩ ⟨10,3,50,10⟩⟩ = false := by decide

theorem worker_cannot_select_soft_mode :
    eval (executionCaveat 8) ⟨[]⟩
      ⟨("request/verb",2) :: slots ⟨8,1,60,0⟩ ⟨8,2,60,0⟩⟩ = false := by decide

theorem controller_input_accepted : accepts running (Operation.input.after running) = true := by decide

theorem paused_input_refused :
    accepts ⟨8,0,100,0⟩ (Operation.input.after ⟨8,0,100,0⟩) = false := by decide

theorem hard_pending_input_refused : accepts pending (Operation.input.after pending) = false := by decide

theorem worker_cannot_submit_input :
    eval (executionCaveat 8) ⟨[]⟩
      ⟨("request/verb",2) :: slots running (Operation.input.after running)⟩ = false := by decide

/-- info: 'Minidregg.Kernel.AgentGrain.accepted_budget_nonincrease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_budget_nonincrease
/-- info: 'Minidregg.Kernel.AgentGrain.accepted_generation_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_generation_monotone
/-- info: 'Minidregg.Kernel.AgentGrain.worker_generation_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms worker_generation_exact

/-- info: 'Minidregg.Kernel.AgentGrain.reservation_accepted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms reservation_accepted
/-- info: 'Minidregg.Kernel.AgentGrain.overspend_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms overspend_refused
/-- info: 'Minidregg.Kernel.AgentGrain.reconnect_before_reconcile_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms reconnect_before_reconcile_refused
/-- info: 'Minidregg.Kernel.AgentGrain.hard_trip_invalidates_generation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hard_trip_invalidates_generation

/-- info: 'Minidregg.Kernel.AgentGrain.operation_target_actions_exact' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms operation_target_actions_exact
/-- info: 'Minidregg.Kernel.AgentGrain.operation_command_retains_publications' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms operation_command_retains_publications
end Minidregg.Kernel.AgentGrain
