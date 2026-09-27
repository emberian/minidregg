/- Named executable instances of the general one-shot application law. -/
import Kernel.ApplicationGrainLaws

namespace Minidregg.Kernel.ApplicationLifecycleClaimPolicyCheck

open Minidregg.Kernel.ApplicationGrain
open Minidregg.Pred

private def startPending : ApplicationGrain.State := ⟨4, 3, 2, 1⟩
private def startClaimed : ApplicationGrain.State := ⟨4, 9, 2, 1⟩
private def serving : ApplicationGrain.State := ⟨4, 4, 2, 1⟩

theorem pending_start_claims_once :
    eval claimTransitionPolicy ⟨[]⟩ ⟨slots startPending startClaimed⟩ = true := by
  decide

theorem claimed_start_cannot_claim_again :
    eval claimTransitionPolicy ⟨[]⟩ ⟨slots startClaimed startClaimed⟩ = false := by
  decide

theorem direct_pending_start_completion_refused :
    eval (transitionPolicy 102 103) ⟨[]⟩
      ⟨slots startPending serving ++ [(completionSlot, 1)]⟩ = false := by
  decide

theorem claimed_start_completion_requires_checked_gate :
    eval (transitionPolicy 102 103) ⟨[]⟩
      ⟨slots startClaimed serving⟩ = false := by
  decide

theorem claimed_start_checked_completion :
    eval (transitionPolicy 102 103) ⟨[]⟩
      ⟨slots startClaimed serving ++ [(completionSlot, 1)]⟩ = true := by
  decide

end Minidregg.Kernel.ApplicationLifecycleClaimPolicyCheck
