import Kernel.GenericSimplexStructure
import Kernel.GenericSimplexCausal

namespace Minidregg.Kernel.GenericSimplexGlobalCausal
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplexStructure
set_option autoImplicit false

/-- Actual network induction consumes the executable local closure, not a
hypothesis that participants already obey the consensus safety rules. -/
theorem reachable_causal {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net) :
    ∀ party, CausalInvariant (net.localState party) := by
  induction reachable with
  | initial => intro party; exact start_causal c party time [] []
  | next prior party input allowed ih =>
    intro other
    by_cases same : other = party
    · subst other
      simpa only [advance, if_pos rfl] using step_causal c _ input (ih party)
    · simpa only [advance, if_neg same] using ih other

def EnrolledAudit (c : Config) (net : Network) : Prop :=
  ∀ event ∈ net.audit, ∃ party < c.parties, eventOwner event = some party

theorem initial_enrolled (c : Config) (time : Nat) : EnrolledAudit c (initial c time) := by
  intro event member
  obtain ⟨party, inside, entry⟩ := List.mem_flatMap.mp member
  refine ⟨party, List.mem_range.mp inside, ?_⟩
  simpa only [(structuralAuditLaws c).startSelf] using
    (structuralAuditLaws c).startOwned party time event entry

theorem advance_enrolled {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {net : Network}
    (projected : ProjectedNetwork c faulty net) (enrolled : EnrolledAudit c net)
    (party : Nat) (input : Input) (allowed : AllowedInput c faulty checked net party input) :
    EnrolledAudit c (advance c faulty net party input) := by
  intro event member
  rcases List.mem_append.mp member with oldOrInput | added
  · rcases List.mem_append.mp oldOrInput with old | supplied
    · exact enrolled event old
    · cases input with
      | delivery message | deliveryAt now message =>
        by_cases bad : message.sender ∈ faulty
        · have eq : event = .send message := by simpa [byzantineInputAudit, bad] using supplied
          subst event
          exact ⟨message.sender, allowed.2.2.1, rfl⟩
        · simp [byzantineInputAudit, bad] at supplied
      | tick now | checked block | offer payload | poll =>
        simp [byzantineInputAudit] at supplied
  · have own := (structuralAuditLaws c).stepOwned (net.localState party) input
      (projected.owned party allowed.1 allowed.2.1) event (List.mem_of_mem_drop added)
    refine ⟨party, allowed.1, ?_⟩
    have selfSame := ((structuralAuditLaws c).stepExtension (net.localState party) input).sameSelf
    simpa only [selfSame, projected.identity party allowed.1 allowed.2.1] using own

theorem reachable_enrolled {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net) : EnrolledAudit c net := by
  induction reachable with
  | initial => exact initial_enrolled c time
  | next prior party input allowed ih =>
    exact advance_enrolled (reachable_projected (structuralAuditLaws c) prior)
      ih party input allowed

theorem trace_send_member {net : Network} {time : Nat} {message : Message}
    (sent : auditTrace net time = .send message) : (.send message : Minidregg.Kernel.GenericSimplex.AuditEvent) ∈ net.audit := by
  cases found : net.audit[time]? with
  | none => simp [auditTrace, found] at sent
  | some event =>
    have eq : event = .send message := by simpa [auditTrace, found] using sent
    subst event
    exact List.mem_iff_getElem?.mpr ⟨time, found⟩

theorem honest_send_local {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net) {message : Message}
    (honest : message.sender ∉ faulty) (entry : (.send message : Minidregg.Kernel.GenericSimplex.AuditEvent) ∈ net.audit) :
    message.sender < c.parties ∧
      (.send message : Minidregg.Kernel.GenericSimplex.AuditEvent) ∈ (net.localState message.sender).audit := by
  obtain ⟨party, enrolled, owner⟩ := reachable_enrolled reachable _ entry
  have same : message.sender = party := by simpa [eventOwner] using owner
  have senderMember : message.sender < c.parties := by simpa only [same] using enrolled
  refine ⟨senderMember, ?_⟩
  rw [← (reachable_projected (structuralAuditLaws c) reachable).projection _ senderMember honest]
  exact List.mem_filter.mpr ⟨entry, by simp [eventOwner]⟩

/-- First LocalFaithful field, instantiated on the exact executable global trace. -/
theorem actual_vote_once {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (t u party view : Nat) (first second : Block) (honest : party ∉ faulty)
    (left : Sent (auditTrace net) t party view .vote (some first))
    (right : Sent (auditTrace net) u party view .vote (some second)) : first = second := by
  obtain ⟨member, leftLocal⟩ := honest_send_local reachable honest (trace_send_member left)
  have rightLocal := (honest_send_local reachable honest (trace_send_member right)).2
  have identity := (reachable_projected (structuralAuditLaws c) reachable).identity party member honest
  apply (reachable_causal reachable party).voteOnce view first second
  · simpa only [identity] using leftLocal
  · simpa only [identity] using rightLocal

/-- Both temporal directions of the actual COMMIT/CANDIDATE exclusion, obtained
from the retained local history and the executable per-view flags. -/
theorem actual_commit_candidate_lock {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (t u party view : Nat) (block : Block) (arg : Argument) (honest : party ∉ faulty)
    (commit : Sent (auditTrace net) t party view .commit (some block))
    (candidate : Sent (auditTrace net) u party view .candidate arg) : arg = some block := by
  obtain ⟨member, commitLocal⟩ := honest_send_local reachable honest (trace_send_member commit)
  have candidateLocal := (honest_send_local reachable honest (trace_send_member candidate)).2
  have identity := (reachable_projected (structuralAuditLaws c) reachable).identity party member honest
  have invariant := reachable_causal reachable party
  apply recorded_commit_candidate _ invariant.commitLock invariant.commitRecorded
    invariant.candidateRecorded view block arg
  · simpa only [identity] using commitLocal
  · simpa only [identity] using candidateLocal

#assert_axioms reachable_causal
#assert_axioms reachable_enrolled
#assert_axioms honest_send_local
#assert_axioms actual_vote_once
#assert_axioms actual_commit_candidate_lock
end Minidregg.Kernel.GenericSimplexGlobalCausal
