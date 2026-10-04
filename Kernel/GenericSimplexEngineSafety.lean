import Kernel.GenericSimplexNetworkEmission
import Kernel.GenericSimplexActualFaithful
import Kernel.GenericSimplexGlobalSupport
import Kernel.GenericSimplexCertificateSafety
import Kernel.GenericSimplexWitnesses

namespace Minidregg.Kernel.GenericSimplexEngineSafety
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplexReceiveProvenance
open Minidregg.Kernel.GenericSimplexReceiveStructure
open Minidregg.Kernel.GenericSimplexGlobalReceive
open Minidregg.Kernel.GenericSimplexGlobalSupport
open Minidregg.Kernel.GenericSimplexEmissionSupport
open Minidregg.Kernel.GenericSimplexGlobalEmission
open Minidregg.Kernel.GenericSimplexNetworkEmission
open Minidregg.Kernel.GenericSimplexActualFaithful
open Minidregg.Kernel.GenericSimplexCertificateSafety
set_option autoImplicit false

/-- Induction over the actual authenticated executable start/step network.
Every local and global emission cause is constructed; none is a safety premise. -/
theorem reachable_emission_invariants {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3*c.faults+1) :
    NetworkJustified c faulty net ∧ SupportedTrace c faulty net := by
  induction reachable with
  | initial =>
    exact ⟨initial_network_justified c faulty time (fun p => start_emission c p time [] []),
      initial_supported_from_local c faulty time (fun p => start_emission c p time [] [])⟩
  | @next before prior party input allowed ih =>
    let external := ExternalAt (before.audit ++ byzantineInputAudit faulty input)
    have projected := reachable_projected (structuralAuditLaws c) prior
    have backed : Backed external (before.localState party) := by
      intro view stored message received
      exact Or.inl (List.mem_append.mpr (Or.inl
        (actual_reachable_globalBacked prior party allowed.1 allowed.2.1 view stored message received)))
    have old := emission_weaken (ih.1 party allowed.1 allowed.2.1)
      (next := external) (fun _ entry => List.mem_append.mpr (Or.inl entry))
    have available : InputAvailable external input := by
      have supported := allowed_input_backed projected party input allowed
      cases input <;> exact supported
    have nextJustified := step_emission c external (before.localState party) input size
      (reachable_scoped prior party allowed.1) backed old available
    exact ⟨advance_network_justified ih.1 party input nextJustified,
      advance_supported_from_local prior ih.2 party input allowed nextJustified⟩

/-- The previously abstract local protocol contract is derived from actual
executable reachability. Authentication is in AllowedInput; no synchrony or
fault bound is needed for local fidelity. -/
theorem actual_local_faithful {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3*c.faults+1) :
    LocalFaithful (auditTrace net) (Finset.range c.parties) faulty c.faults :=
  localFaithful_of_supported reachable size (reachable_emission_invariants reachable size).2

theorem actual_committed_prefix_consistency {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    {v w : Nat} {a b : Block} (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3*c.faults+1) (faultBound : faulty.card ≤ c.faults)
    (left : CommittedAt (auditTrace net) faulty v a)
    (right : CommittedAt (auditTrace net) faulty w b) :
    a.IsPrefix b ∨ b.IsPrefix a :=
  committed_prefix_consistency (actual_local_faithful reachable size)
    (by simpa using size) faultBound left right

theorem actual_certificates_prefix_consistent {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    {v w : Nat} {a b : Block} (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3*c.faults+1) (faultBound : faulty.card ≤ c.faults)
    (left : AttributedCommitSends (auditTrace net) (Finset.range c.parties) faulty c.faults v a)
    (right : AttributedCommitSends (auditTrace net) (Finset.range c.parties) faulty c.faults w b) :
    a.IsPrefix b ∨ b.IsPrefix a :=
  attributed_commit_sends_prefix_consistent (actual_local_faithful reachable size)
    (by simpa using size) faultBound left right

/-- Exact receiver catch-up: two original full descendant certificates cannot
cover different next records after the same installed source prefix. -/
theorem actual_certified_next_record_unique {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    {v w : Nat} {a b sourcePrefix : Block} {left right : Bytes}
    (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3*c.faults+1) (faultBound : faulty.card ≤ c.faults)
    (certA : AttributedCommitSends (auditTrace net) (Finset.range c.parties) faulty c.faults v a)
    (certB : AttributedCommitSends (auditTrace net) (Finset.range c.parties) faulty c.faults w b)
    (coveredA : (sourcePrefix ++ [left]).IsPrefix (sourceHistory a))
    (coveredB : (sourcePrefix ++ [right]).IsPrefix (sourceHistory b)) : left = right :=
  certified_next_record_unique (actual_local_faithful reachable size)
    (by simpa using size) faultBound certA certB coveredA coveredB

open Minidregg.Kernel.GenericSimplexWitnesses
/-- A real four-party execution with a silent faulty participant inhabits the
contract and commits. The concrete schedule is kernel evaluated. -/
theorem honest_execution_faithful :
    LocalFaithful (auditTrace honestRun) (Finset.range config.parties) honestFaulty config.faults :=
  actual_local_faithful honest_run_reachable (by decide)

/-- Fidelity does not hide the fault bound. The same executable engine remains
locally faithful in the checked f+1-fault execution with conflicting commits. -/
theorem overfault_execution_faithful :
    LocalFaithful (auditTrace hostileRun) (Finset.range config.parties) excessFaulty config.faults :=
  actual_local_faithful hostile_run_reachable (by decide)

/-- The timeout-backoff departure (fix C) is confined to the view deadline.
With `backoffCap = 0` the timer is the paper's fixed `timeout`; otherwise it
lies between `timeout` and `timeout · 2^backoffCap`. The safety theorems above
quantify over this same executable `step`, deadline included. -/
theorem viewTimeout_fixed_of_cap_zero (c : Config) (s : State) (number : Nat)
    (fixed : c.backoffCap = 0) : viewTimeout c s number = c.timeout := by
  simp [viewTimeout, fixed]

theorem viewTimeout_bounds (c : Config) (s : State) (number : Nat) :
    c.timeout ≤ viewTimeout c s number ∧ viewTimeout c s number ≤ c.timeout * 2 ^ c.backoffCap := by
  unfold viewTimeout
  constructor
  · exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _))

/-- The backoff exponent restarts after a local commit: the view right after
the highest locally committed view runs on the fixed timer. -/
theorem viewTimeout_after_commit (c : Config) (s : State) :
    viewTimeout c s (lastCommittedView s + 1) = c.timeout := by
  simp [viewTimeout]

#assert_axioms reachable_emission_invariants
#assert_axioms actual_local_faithful
#assert_axioms actual_committed_prefix_consistency
#assert_axioms actual_certificates_prefix_consistent
#assert_axioms actual_certified_next_record_unique
#assert_axioms honest_execution_faithful
#assert_axioms overfault_execution_faithful
#assert_axioms viewTimeout_fixed_of_cap_zero
#assert_axioms viewTimeout_bounds
#assert_axioms viewTimeout_after_commit
end Minidregg.Kernel.GenericSimplexEngineSafety
