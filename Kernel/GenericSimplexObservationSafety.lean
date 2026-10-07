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

/-! ## Named poles for the hypothesis ledger

`AuditRefinement`, `LocalFaithful`, `LocalCommitOutputAttestations` and `AuditExtension`
are premises of the refinement chain.  The satisfying instances below are at the REAL
engine (`start`/`step`/`initial`, `n = 3f+1` with `f = 1`) and are obtained from the
general reachability theorems, not hand-built; the refuting instances are concrete
networks and traces that violate exactly one field each. -/

/-- The smallest real committee: four parties, one fault. -/
def poleConfig : Config := { parties := 4, faults := 1, timeout := 1 }

theorem poleConfig_size : poleConfig.parties = 3 * poleConfig.faults + 1 := by decide

theorem poleConfig_wellFormed : poleConfig.wellFormed = true := by decide

/-- Source checking never succeeds: reachability holds for this one as for any other. -/
def poleChecked : Network → Nat → Block → Prop := fun _ _ _ => False

theorem poleInitial_reachable :
    Reachable poleConfig ∅ poleChecked 0 (initial poleConfig 0) := .initial

/-- The actual engine step extends the retained audit, at a real started replica. -/
theorem auditExtension_real_step :
    AuditExtension (start poleConfig 0 0) (step poleConfig (start poleConfig 0 0) (.tick 1)) :=
  (structuralAuditLaws poleConfig).stepExtension _ _

/-- `AuditRefinement` holds at the real initial network of the real engine. -/
theorem auditRefinement_initial : AuditRefinement poleConfig ∅ (initial poleConfig 0) :=
  actual_audit_refinement poleInitial_reachable poleConfig_size

/-- `LocalFaithful` holds on the real initial audit trace. -/
theorem localFaithful_initial :
    LocalFaithful (auditTrace (initial poleConfig 0)) (Finset.range poleConfig.parties) ∅
      poleConfig.faults :=
  actual_local_faithful poleInitial_reachable poleConfig_size

/-- A replica that reports a commit in view 1 while no commit output was ever retained
in the audit: the observation clause of `AuditRefinement` fails. -/
def poleForgedState : State :=
  { self := 0, deadline := 0, views := [{ number := 1, committed := some [] }] }

def poleForged : Network := ⟨fun _ => poleForgedState, []⟩

theorem not_auditRefinement_forged_commit :
    ¬ AuditRefinement poleConfig ∅ poleForged := by
  intro refinement
  have reported : (viewAt (poleForged.localState 0) 1).committed = some [] := by
    first | decide | simp [poleForged, poleForgedState, viewAt]
  have committed := refinement.commits 0 1 [] (by decide) (by simp) reported
  rcases committed with ⟨view, _⟩ | ⟨time, party, _, output⟩
  · simp at view
  · simp [auditTrace, poleForged] at output

/-- Honest party 0 votes for two different blocks in view 1: `voteOnce` fails. -/
def poleEquivocate : Trace := fun time =>
  if time = 0 then .send ⟨0, 1, .vote, some []⟩
  else if time = 1 then .send ⟨0, 1, .vote, some [[]]⟩
  else .idle

theorem not_localFaithful_equivocation :
    ¬ LocalFaithful poleEquivocate (Finset.range 4) ∅ 1 := by
  intro rules
  have same := rules.voteOnce 0 1 0 1 [] [[]] (by simp)
    (by first | exact rfl | simp [Sent, poleEquivocate])
    (by first | exact rfl | simp [Sent, poleEquivocate])
  simp at same

/-- Honest party 0 sends COMMIT in view 1 with no vote quorum behind it:
`commitSend` fails. -/
def poleUnsupportedCommit : Trace := fun time =>
  if time = 0 then .send ⟨0, 1, .commit, some []⟩ else .idle

theorem not_localFaithful_unsupported_commit :
    ¬ LocalFaithful poleUnsupportedCommit (Finset.range 4) ∅ 1 := by
  intro rules
  obtain ⟨voters, _, count, sends⟩ := rules.commitSend 0 0 1 [] (by simp)
    (by first | exact rfl | simp [Sent, poleUnsupportedCommit])
  obtain ⟨party, member⟩ := Finset.card_pos.mp (by omega : 0 < voters.card)
  obtain ⟨sentTime, early, _⟩ := sends party member
  omega

/-- Commit outputs of the first `n` parties, all for one view and block. -/
def poleCommitTrace (n view : Nat) (block : Block) : Trace := fun time =>
  if time < n then .commit time view block else .idle

/-- Three honest commit outputs (`2f+1` with `f = 1`) attest a block. -/
theorem localCommitAttestations_three_signers :
    LocalCommitOutputAttestations (poleCommitTrace 3 1 [[]]) (Finset.range 4) ∅ 1 1 [[]] := by
  refine ⟨{0, 1, 2}, ?_, ?_, ?_⟩
  · intro party member
    simp at member ⊢
    omega
  · first | decide | simp
  · intro party member _
    have below : party < 3 := by
      simp at member
      omega
    exact ⟨party, by simp [poleCommitTrace, below]⟩

/-- Two honest commit outputs fall short of `2f+1`. -/
theorem not_localCommitAttestations_two_signers :
    ¬ LocalCommitOutputAttestations (poleCommitTrace 2 1 [[]]) (Finset.range 4) ∅ 1 1 [[]] := by
  rintro ⟨signers, _, count, exports⟩
  have inside : signers ⊆ ({0, 1} : Finset Nat) := by
    intro party member
    obtain ⟨time, output⟩ := exports party member (by simp)
    by_cases below : time < 2
    · simp [poleCommitTrace, below] at output
      simp
      omega
    · simp [poleCommitTrace, below] at output
  have bound := Finset.card_le_card inside
  have two : ({0, 1} : Finset Nat).card = 2 := by first | decide | simp
  omega

#assert_axioms poleConfig_size
#assert_axioms poleConfig_wellFormed
#assert_axioms poleInitial_reachable
#assert_axioms auditExtension_real_step
#assert_axioms auditRefinement_initial
#assert_axioms localFaithful_initial
#assert_axioms not_auditRefinement_forged_commit
#assert_axioms not_localFaithful_equivocation
#assert_axioms not_localFaithful_unsupported_commit
#assert_axioms localCommitAttestations_three_signers
#assert_axioms not_localCommitAttestations_two_signers
#assert_axioms reachable_output_history
#assert_axioms actual_audit_refinement
#assert_axioms actual_state_commits_compatible
#assert_axioms actual_delivered_blocks_compatible
end Minidregg.Kernel.GenericSimplexObservationSafety
