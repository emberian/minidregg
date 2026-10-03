import Kernel.GenericSimplexGlobalReceive
import Kernel.GenericSimplexPreparedHistory

namespace Minidregg.Kernel.GenericSimplexChronology
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplexGlobalReceive
open Minidregg.Kernel.GenericSimplexPreparedHistory
set_option autoImplicit false
abbrev Event := Minidregg.Kernel.GenericSimplex.AuditEvent

/-- The exact local prefix before an owned event is the projection of the exact
global prefix before that event; multiple emissions in one pump stay ordered. -/
theorem project_at_owned (party : Nat) (events : List Event) (time : Nat) (event : Event)
    (atTime : events[time]? = some event) (owner : eventOwner event = some party) :
    project party events = project party (events.take time) ++
      event :: project party (events.drop (time + 1)) := by
  obtain ⟨within, exactEvent⟩ := List.getElem?_eq_some_iff.mp atTime
  have splitEvents : events = events.take time ++ event :: events.drop (time + 1) := by
    calc events = events.take time ++ events.drop time := (List.take_append_drop ..).symm
         _ = _ := by rw [List.drop_eq_getElem_cons within, exactEvent]
  conv_lhs => rw [splitEvents]
  simp only [project_append, project, List.filter_append, List.filter_cons, owner, beq_self_eq_true, ↓reduceIte]

theorem projected_event_prefix {c : Config} {faulty : Finset Nat} {net : Network}
    (projected : ProjectedNetwork c faulty net) (party time : Nat) (event : Event)
    (enrolled : party < c.parties) (honest : party ∉ faulty)
    (atTime : net.audit[time]? = some event) (owner : eventOwner event = some party) :
    let before := project party (net.audit.take time)
    (net.localState party).audit[before.length]? = some event ∧
    (net.localState party).audit.take before.length = before := by
  have splitLocal : (net.localState party).audit = project party (net.audit.take time) ++
      event :: project party (net.audit.drop (time + 1)) := by
    rw [← projected.projection party enrolled honest]
    exact project_at_owned party net.audit time event atTime owner
  simp [splitLocal]

theorem event_in_prefix_before {net : Network} {time : Nat} {event : Event}
    (member : event ∈ net.audit.take time) :
    ∃ earlier < time, auditTrace net earlier = event := by
  obtain ⟨earlier, atTime⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp atTime
  have bound : earlier < time := by simp only [List.length_take] at within; omega
  rw [List.getElem?_take_of_lt bound] at atTime
  exact ⟨earlier, bound, by simp [auditTrace, atTime]⟩

theorem projected_prefix_before {net : Network} {party time : Nat} {event : Event}
    (member : event ∈ project party (net.audit.take time)) :
    ∃ earlier < time, auditTrace net earlier = event :=
  event_in_prefix_before (List.mem_filter.mp member).1

/-- Causal transport uses only the source prefix, never membership in a final
history containing sends that might have happened later. -/
theorem safeAt_transport (history : List Event) (tr : Trace) (time party view : Nat) (block : Block)
    (earlier : ∀ event ∈ history, ∃ before < time, tr before = event)
    (safe : SafeAt (localTrace history) history.length party view block) :
    SafeAt tr time party view block := by
  obtain ⟨nonempty, previous, older, prepared, disabled⟩ := safe
  refine ⟨nonempty, previous, older, ?_, ?_⟩
  · rcases prepared with genesis | ⟨before, within, prepared⟩
    · exact Or.inl genesis
    · apply Or.inr
      apply earlier (.prepare party previous block.dropLast)
      have atTime : history[before]? = some (.prepare party previous block.dropLast) := by
        simpa [localTrace, List.getElem?_eq_getElem within] using prepared
      exact List.mem_iff_getElem?.mpr ⟨before, atTime⟩
  · intro skipped afterPrevious beforeView
    obtain ⟨before, within, output⟩ := disabled skipped afterPrevious beforeView
    apply earlier (.disable party skipped)
    have atTime : history[before]? = some (.disable party skipped) := by
      simpa [localTrace, List.getElem?_eq_getElem within] using output
    exact List.mem_iff_getElem?.mpr ⟨before, atTime⟩

theorem reachable_history {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net) :
    ∀ party, HistoryInvariant (net.localState party) := by
  induction reachable with
  | initial => intro party; exact start_history c party initialTime [] []
  | next prior party input allowed ih =>
    intro other
    by_cases same : other = party
    · subst other
      simpa only [advance, if_pos rfl] using step_history c _ input (ih party)
    · simpa only [advance, if_neg same] using ih other

theorem actual_isSafe_now {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net)
    (party : Nat) (enrolled : party < c.parties) (honest : party ∉ faulty) (block : Block)
    (safe : isSafe (net.localState party) block = true) :
    SafeAt (auditTrace net) net.audit.length party (net.localState party).current block := by
  have projected := reachable_projected (structuralAuditLaws c) reachable
  have localSafe := isSafe_safeAt _ block (reachable_history reachable party) safe
  have mapped := safeAt_transport (net.localState party).audit (auditTrace net) net.audit.length
    (net.localState party).self (net.localState party).current block ?_ localSafe
  · simpa only [projected.identity party enrolled honest] using mapped
  · intro event member
    have globalEntry := local_audit_in_global projected enrolled honest member
    obtain ⟨before, atTime⟩ := List.mem_iff_getElem?.mp globalEntry
    obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp atTime
    exact ⟨before, within, by simp [auditTrace, atTime]⟩

#assert_axioms project_at_owned
#assert_axioms projected_event_prefix
#assert_axioms projected_prefix_before
#assert_axioms safeAt_transport
#assert_axioms reachable_history
#assert_axioms actual_isSafe_now
end Minidregg.Kernel.GenericSimplexChronology
