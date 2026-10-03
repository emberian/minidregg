import Kernel.GenericSimplexGlobalVoteOrigin
import Kernel.GenericSimplexGlobalPositive
import Kernel.GenericSimplexGlobalEmission

namespace Minidregg.Kernel.GenericSimplexActualFaithful
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexGlobalCausal
open Minidregg.Kernel.GenericSimplexGlobalVoteOrigin
open Minidregg.Kernel.GenericSimplexGlobalPositive
open Minidregg.Kernel.GenericSimplexGlobalEmission
set_option autoImplicit false
abbrev FaithfulEvent := Minidregg.Kernel.GenericSimplex.AuditEvent

theorem trace_event_at {net : Network} {time : Nat} {event : FaithfulEvent}
    (nonidle : event ≠ .idle) (output : auditTrace net time = event) :
    net.audit[time]? = some event := by
  cases found : net.audit[time]? with
  | none => simp only [auditTrace, found, Option.getD_none] at output; exact False.elim (nonidle output.symm)
  | some value =>
    have same : value = event := by simpa [auditTrace, found] using output
    simpa only [same] using found

/-- Join of the actual reachable-state field proofs. The indexed quorum-emission
argument is constructed by actual network induction in
GenericSimplexEngineSafety.actual_local_faithful. -/
theorem localFaithful_of_supported {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net)
    (size : c.parties = 3*c.faults+1) (supported : SupportedTrace c faulty net) :
    LocalFaithful (auditTrace net) (Finset.range c.parties) faulty c.faults := by
  have quorum : c.quorum = 2*c.faults+1 := by unfold Config.quorum; omega
  refine ⟨actual_vote_once reachable, ?_, actual_commit_candidate_lock reachable,
    ?_, ?_, ?_, ?_, ?_, actual_vote_origin reachable,
    actual_prepare_positive reachable, actual_commit_positive reachable,
    actual_disable_positive reachable⟩
  · intro time party view block honest sent
    have cause := supported time (.send ⟨party,view,.commit,some block⟩) party
      (trace_event_at (by simp) sent) rfl honest
    simpa only [GlobalEventSupported, quorum] using cause
  · intro time party view block honest sent
    have cause := supported time (.send ⟨party,view,.candidate,some block⟩) party
      (trace_event_at (by simp) sent) rfl honest
    exact cause
  · intro time party view arg honest sent
    have cause := supported time (.send ⟨party,view,.ready,arg⟩) party
      (trace_event_at (by simp) sent) rfl honest
    simpa only [GlobalEventSupported, quorum] using cause
  · intro time party view block honest output
    have cause := supported time (.prepare party view block) party
      (trace_event_at (by simp) output) rfl honest
    simpa only [GlobalEventSupported, quorum] using cause
  · intro time party view honest output
    have cause := supported time (.disable party view) party
      (trace_event_at (by simp) output) rfl honest
    simpa only [GlobalEventSupported, quorum] using cause
  · intro time party view block honest output
    have cause := supported time (.commit party view block) party
      (trace_event_at (by simp) output) rfl honest
    simpa only [GlobalEventSupported, quorum] using cause

#assert_axioms trace_event_at
#assert_axioms localFaithful_of_supported
end Minidregg.Kernel.GenericSimplexActualFaithful
