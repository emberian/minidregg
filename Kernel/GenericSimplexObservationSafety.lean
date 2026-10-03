import Kernel.GenericSimplexEngineSafety
import Kernel.GenericSimplexOutputHistory

namespace Minidregg.Kernel.GenericSimplexObservationSafety
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplexGlobalReceive
open Minidregg.Kernel.GenericSimplexEngineSafety
open Minidregg.Kernel.GenericSimplexOutputHistory
set_option autoImplicit false

theorem reachable_output_history {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net) :
    ∀ party, OutputHistory (net.localState party) := by
  induction reachable with
  | initial => intro party; exact start_output c party time [] []
  | next prior party input allowed ih =>
    intro other
    by_cases same : other = party
    · subst other
      simpa only [advance, if_pos rfl] using step_output c _ input (ih party)
    · simpa only [advance, if_neg same] using ih other

theorem local_commit_is_committed {c : Config} {faulty : Finset Nat} {net : Network}
    (projected : ProjectedNetwork c faulty net) {party view : Nat} {block : Block}
    (enrolled : party < c.parties) (honest : party ∉ faulty)
    (output : (.commit (net.localState party).self view block : Minidregg.Kernel.GenericSimplex.AuditEvent)
      ∈ (net.localState party).audit) :
    CommittedAt (auditTrace net) faulty view block := by
  have globalOutput := local_audit_in_global projected enrolled honest output
  rw [projected.identity party enrolled honest] at globalOutput
  obtain ⟨index, atIndex⟩ := List.mem_iff_getElem?.mp globalOutput
  exact Or.inr ⟨index, party, honest, by simp only [auditTrace, atIndex, Option.getD_some]⟩

/-- The actual executable observation join: both per-view committed flags and
returned delivered blocks are backed by retained commit outputs on the same
reachable global trace. No output-provenance premise is supplied by the caller. -/
theorem actual_audit_refinement {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3*c.faults+1) : AuditRefinement c faulty net := by
  have projected := reachable_projected (structuralAuditLaws c) reachable
  refine ⟨actual_local_faithful reachable size, ?_, ?_⟩
  · intro party view block enrolled honest committed
    exact local_commit_is_committed projected enrolled honest
      ((reachable_output_history reachable party).committed view block committed)
  · intro party block enrolled honest delivered
    obtain ⟨view, output⟩ := (reachable_output_history reachable party).delivered block delivered
    exact ⟨view, local_commit_is_committed projected enrolled honest output⟩

theorem actual_state_commits_compatible {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3*c.faults+1) (faultBound : faulty.card ≤ c.faults)
    {p q v w : Nat} {a b : Block}
    (pm : p<c.parties) (qm : q<c.parties) (ph : p∉faulty) (qh : q∉faulty)
    (left : (viewAt (net.localState p) v).committed = some a)
    (right : (viewAt (net.localState q) w).committed = some b) :
    a.IsPrefix b ∨ b.IsPrefix a :=
  refined_engine_commits_compatible (actual_audit_refinement reachable size) size faultBound pm qm ph qh left right

theorem actual_delivered_blocks_compatible {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3*c.faults+1) (faultBound : faulty.card ≤ c.faults)
    {p q : Nat} {a b : Block}
    (pm : p<c.parties) (qm : q<c.parties) (ph : p∉faulty) (qh : q∉faulty)
    (left : a∈(net.localState p).delivered) (right : b∈(net.localState q).delivered) :
    a.IsPrefix b ∨ b.IsPrefix a := by
  have audit := actual_audit_refinement reachable size
  obtain ⟨v, committedA⟩ := audit.delivered p a pm ph left
  obtain ⟨w, committedB⟩ := audit.delivered q b qm qh right
  exact actual_committed_prefix_consistency reachable size faultBound committedA committedB

#assert_axioms reachable_output_history
#assert_axioms actual_audit_refinement
#assert_axioms actual_state_commits_compatible
#assert_axioms actual_delivered_blocks_compatible
end Minidregg.Kernel.GenericSimplexObservationSafety
