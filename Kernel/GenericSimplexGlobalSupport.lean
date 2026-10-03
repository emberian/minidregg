import Kernel.GenericSimplexScopeStructure
import Kernel.GenericSimplexGlobalReceive
import Kernel.GenericSimplexCountSupport

namespace Minidregg.Kernel.GenericSimplexGlobalSupport
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplexReceiveProvenance
open Minidregg.Kernel.GenericSimplexReceiveScope
open Minidregg.Kernel.GenericSimplexScopeStructure
open Minidregg.Kernel.GenericSimplexGlobalReceive
open Minidregg.Kernel.GenericSimplexCountSupport
set_option autoImplicit false

theorem reachable_scoped {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net) :
    ∀ party, party < c.parties → Scoped c (net.localState party) := by
  induction reachable with
  | initial => intro party member; exact start_scoped c party time member
  | next prior party input allowed ih =>
    intro other member
    by_cases same : other = party
    · subst other
      simpa only [advance, if_pos rfl] using step_scoped c _ input (ih party member)
    · simpa only [advance, if_neg same] using ih other member

/-- The executable count at an actual network state yields a finite distinct
quorum whose sends are strictly before the next global event. This does not yet
identify which historic output used that count; that is the emission join. -/
theorem actual_count_support_now {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (party number : Nat) (member : party < c.parties) (honest : party ∉ faulty)
    (kind : Kind) (arg : Argument) (threshold : Nat)
    (enough : threshold ≤ count (viewAt (net.localState party) number) kind arg) :
    Support (auditTrace net) (Finset.range c.parties) net.audit.length number kind arg threshold := by
  have scopeOK := reachable_scoped reachable party member
  have backed := actual_reachable_globalBacked reachable
  have projected := reachable_projected (structuralAuditLaws c) reachable
  have stored : Backed (fun message =>
      (.send message : Minidregg.Kernel.GenericSimplex.AuditEvent) ∈ net.audit)
      (net.localState party) := by
    intro view inside message received
    exact Or.inl (backed party member honest view inside message received)
  have support := actual_count_support (tr := auditTrace net)
    (roster := Finset.range c.parties) (v := viewAt (net.localState party) number)
    (time := net.audit.length) (threshold := threshold) (kind := kind) (arg := arg)
  rw [← viewAt_number (net.localState party) number]
  apply support
  · intro message received
    have data := viewAt_scoped scopeOK number message received
    have source := viewAt_backed stored number message received
    have globalSend : (.send message : Minidregg.Kernel.GenericSimplex.AuditEvent) ∈ net.audit := by
      rcases source with globalEntry | localEntry
      · exact globalEntry
      · exact local_audit_in_global projected member honest localEntry
    obtain ⟨sentTime, atTime⟩ := List.mem_iff_getElem?.mp globalSend
    obtain ⟨before, _⟩ := List.getElem?_eq_some_iff.mp atTime
    refine ⟨Finset.mem_range.mpr data.1, ?_, sentTime, before, ?_⟩
    · simpa only [viewAt_number] using data.2
    · simp [auditTrace, atTime]
  · exact enough

#assert_axioms reachable_scoped
#assert_axioms actual_count_support_now
end Minidregg.Kernel.GenericSimplexGlobalSupport
