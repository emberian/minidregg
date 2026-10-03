import Kernel.GenericSimplexVoteOrigin
import Kernel.GenericSimplexChronology
import Kernel.GenericSimplexGlobalCausal

namespace Minidregg.Kernel.GenericSimplexGlobalVoteOrigin
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplexChronology
open Minidregg.Kernel.GenericSimplexGlobalCausal
open Minidregg.Kernel.GenericSimplexVoteOrigin
set_option autoImplicit false

theorem reachable_origin {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net) :
    ∀ party, OriginInvariant (net.localState party) := by
  induction reachable with
  | initial => intro party; exact start_origin c party initialTime [] []
  | next prior party input allowed ih =>
    intro other
    by_cases same : other = party
    · subst other
      simpa only [advance, if_pos rfl] using step_origin c _ input (ih party)
    · simpa only [advance, if_neg same] using ih other

/-- The actual VOTE came from an executable isSafe check or a preparation
already present before that vote, transported at that precise event index. -/
theorem actual_vote_origin {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net)
    (time party view : Nat) (block : Block) (honest : party ∉ faulty)
    (sent : Sent (auditTrace net) time party view .vote (some block)) :
    SafeAt (auditTrace net) time party view block ∨
      ∃ before < time, auditTrace net before = .prepare party view block := by
  have globalEntry := trace_send_member sent
  have enrolled := (honest_send_local reachable honest globalEntry).1
  have projected := reachable_projected (structuralAuditLaws c) reachable
  have atTime : net.audit[time]? = some (.send ⟨party, view, .vote, some block⟩) := by
    cases found : net.audit[time]? with
    | none => simp [Sent, auditTrace, found] at sent
    | some event =>
      have same : event = .send ⟨party, view, .vote, some block⟩ := by
        simpa [Sent, auditTrace, found] using sent
      simpa only [same] using found
  obtain ⟨localEvent, localPrefix⟩ := projected_event_prefix projected party time
    (.send ⟨party, view, .vote, some block⟩) enrolled honest atTime rfl
  obtain ⟨within, atLocal⟩ := List.getElem?_eq_some_iff.mp localEvent
  have cause := (reachable_origin reachable party).2 _ within
  rw [atLocal, localPrefix] at cause
  change SafeAt _ _ party view block ∨
    .prepare party view block ∈ project party (net.audit.take time) at cause
  rcases cause with safe | prepared
  · exact Or.inl (safeAt_transport _ _ time party view block
      (fun event member => projected_prefix_before member) safe)
  · exact Or.inr (projected_prefix_before prepared)

#assert_axioms reachable_origin
#assert_axioms actual_vote_origin
end Minidregg.Kernel.GenericSimplexGlobalVoteOrigin
