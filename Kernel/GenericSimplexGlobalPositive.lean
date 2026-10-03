import Kernel.GenericSimplexPositive
import Kernel.GenericSimplexGlobalCausal

namespace Minidregg.Kernel.GenericSimplexGlobalPositive
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplexGlobalCausal
open Minidregg.Kernel.GenericSimplexPositive
set_option autoImplicit false
abbrev PositiveEvent := Minidregg.Kernel.GenericSimplex.AuditEvent

theorem reachable_positive {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net) :
    ∀ party, Positive (net.localState party) := by
  induction reachable with
  | initial => intro party; exact start_positive c party initialTime [] []
  | next prior party input allowed ih =>
    intro other
    by_cases same : other = party
    · subst other
      simpa only [advance, if_pos rfl] using step_positive c _ input (ih party)
    · simpa only [advance, if_neg same] using ih other

theorem actual_event_positive {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net)
    (party : Nat) (event : PositiveEvent) (honest : party ∉ faulty)
    (owner : eventOwner event = some party) (member : event ∈ net.audit) : EventPositive event := by
  obtain ⟨sender, enrolled, ownership⟩ := reachable_enrolled reachable event member
  have same : sender = party := by rw [owner] at ownership; exact (Option.some.inj ownership).symm
  subst sender
  have projected := reachable_projected (structuralAuditLaws c) reachable
  have localEntry : event ∈ (net.localState party).audit := by
    rw [← projected.projection party enrolled honest]
    exact List.mem_filter.mpr ⟨member, by simp [owner]⟩
  exact (reachable_positive reachable party).2.2 event localEntry

theorem trace_output_member {net : Network} {time : Nat} {event : PositiveEvent}
    (nonidle : event ≠ .idle) (output : auditTrace net time = event) : event ∈ net.audit := by
  cases found : net.audit[time]? with
  | none => simp only [auditTrace, found, Option.getD_none] at output; exact False.elim (nonidle output.symm)
  | some value =>
    have same : value = event := by simpa [auditTrace, found] using output
    subst value
    exact List.mem_iff_getElem?.mpr ⟨time, found⟩

theorem actual_prepare_positive {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net)
    (time party view : Nat) (block : Block) (honest : party ∉ faulty)
    (output : auditTrace net time = .prepare party view block) : 0 < view :=
  actual_event_positive reachable party _ honest rfl (trace_output_member (by simp) output)

theorem actual_disable_positive {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net)
    (time party view : Nat) (honest : party ∉ faulty)
    (output : auditTrace net time = .disable party view) : 0 < view :=
  actual_event_positive reachable party _ honest rfl (trace_output_member (by simp) output)

theorem actual_commit_positive {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net)
    (time party view : Nat) (block : Block) (honest : party ∉ faulty)
    (output : auditTrace net time = .commit party view block) : 0 < view :=
  actual_event_positive reachable party _ honest rfl (trace_output_member (by simp) output)

#assert_axioms reachable_positive
#assert_axioms actual_event_positive
#assert_axioms actual_prepare_positive
#assert_axioms actual_disable_positive
#assert_axioms actual_commit_positive
end Minidregg.Kernel.GenericSimplexGlobalPositive
