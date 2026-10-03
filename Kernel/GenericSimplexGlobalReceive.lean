import Kernel.GenericSimplexStructure
import Kernel.GenericSimplexReceiveStructure

namespace Minidregg.Kernel.GenericSimplexGlobalReceive
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplexReceiveProvenance
open Minidregg.Kernel.GenericSimplexReceiveStructure
set_option autoImplicit false

/-- Actual stored messages are backed by actual sends in this exact global
history. This does not yet assert the causal guard for each past output event. -/
def GlobalBacked (c : Config) (faulty : Finset Nat) (net : Network) : Prop :=
  ∀ party, party < c.parties → party ∉ faulty →
    ∀ view ∈ (net.localState party).views, ∀ message ∈ view.received,
      (.send message : AuditEvent) ∈ net.audit

theorem local_audit_in_global {c : Config} {faulty : Finset Nat} {net : Network}
    (projected : ProjectedNetwork c faulty net) {party : Nat}
    (member : party < c.parties) (honest : party ∉ faulty) {event : AuditEvent}
    (localEntry : event ∈ (net.localState party).audit) : event ∈ net.audit := by
  rw [← projected.projection party member honest] at localEntry
  exact (List.mem_filter.mp localEntry).1

theorem initial_globalBacked (c : Config) (faulty : Finset Nat) (time : Nat) :
    GlobalBacked c faulty (initial c time) := by
  intro party member honest view inside message received
  have origin := start_backed c party time view inside message received
  rcases origin with impossible | sent
  · exact False.elim impossible
  · exact local_audit_in_global
      (initial_projected c faulty time (structuralAuditLaws c)) member honest sent

theorem allowed_input_backed {c : Config} {faulty : Finset Nat}
    {sourceChecked : Network → Nat → Block → Prop} {net : Network}
    (projected : ProjectedNetwork c faulty net) (party : Nat) (input : Input)
    (allowed : AllowedInput c faulty sourceChecked net party input) :
    InputBacked (fun message => (.send message : AuditEvent) ∈
      net.audit ++ byzantineInputAudit faulty input) input := by
  cases input with
  | delivery message | deliveryAt time message =>
    have authenticated := allowed.2.2
    by_cases bad : message.sender ∈ faulty
    · simp [InputBacked, byzantineInputAudit, bad]
    · have sent := authentic_honest_send_in_audit projected authenticated bad
      exact List.mem_append.mpr (Or.inl sent)
  | tick time | checked block | offer payload | poll => trivial

theorem advance_globalBacked {c : Config} {faulty : Finset Nat}
    {sourceChecked : Network → Nat → Block → Prop} {net : Network}
    (projected : ProjectedNetwork c faulty net) (backed : GlobalBacked c faulty net)
    (party : Nat) (input : Input)
    (allowed : AllowedInput c faulty sourceChecked net party input) :
    GlobalBacked c faulty (advance c faulty net party input) := by
  have advancedProjection := advance_projected (structuralAuditLaws c) projected party input allowed
  let external : Message → Prop := fun message =>
    (.send message : AuditEvent) ∈ net.audit ++ byzantineInputAudit faulty input
  have old : Backed external (net.localState party) := by
    intro view member message received
    exact Or.inl (List.mem_append.mpr (Or.inl
      (backed party allowed.1 allowed.2.1 view member message received)))
  have stepped := step_backed c (net.localState party) input old
    (allowed_input_backed projected party input allowed)
  intro other member honest view inside message received
  by_cases same : other = party
  · subst other
    have source := stepped view (by simpa only [advance, if_pos rfl] using inside) message received
    rcases source with oldSend | ownSend
    · exact List.mem_append.mpr (Or.inl oldSend)
    · apply local_audit_in_global advancedProjection member honest
      simpa only [advance, if_pos rfl] using ownSend
  · have oldInside : view ∈ (net.localState other).views := by
      simpa only [advance, if_neg same] using inside
    have sent := backed other member honest view oldInside message received
    exact (advance_audit_prefix c faulty net party input).subset sent

theorem actual_reachable_globalBacked {c : Config} {faulty : Finset Nat}
    {sourceChecked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty sourceChecked initialTime net) : GlobalBacked c faulty net := by
  induction reachable with
  | initial => exact initial_globalBacked c faulty initialTime
  | next prior party input allowed ih =>
    exact advance_globalBacked (reachable_projected (structuralAuditLaws c) prior) ih party input allowed

#assert_axioms initial_globalBacked
#assert_axioms advance_globalBacked
#assert_axioms actual_reachable_globalBacked
end Minidregg.Kernel.GenericSimplexGlobalReceive
