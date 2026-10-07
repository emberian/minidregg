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
open Minidregg.Kernel.GenericSimplexLocal (AuditExtension)
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
engine (`start`/`step`/`advance`, `n = 3f+1` with `f = 1`, party 3 faulty and silent) on a
run that commits a block at all three honest replicas, obtained from the general
reachability theorems (not hand-built); the refuting instances are concrete
networks and traces that violate exactly one field each. -/

/-- The smallest real committee: four parties, one fault. -/
def poleConfig : Config := { parties := 4, faults := 1, timeout := 1 }

theorem poleConfig_size : poleConfig.parties = 3 * poleConfig.faults + 1 := by decide

theorem poleConfig_wellFormed : poleConfig.wellFormed = true := by decide

/-- Source checking is unconstrained for the pole run: every block is eligible. -/
def poleChecked : Network → Nat → Block → Prop := fun _ _ _ => True

/-- Party 3 is the one tolerated fault and stays silent; parties 0, 1, 2 run honestly. -/
def poleFaulty : Finset Nat := {3}

theorem poleFaulty_bound : poleFaulty.card ≤ poleConfig.faults := by decide

/-- Executable check of one input against `AllowedInput` (with `poleChecked`). -/
def allowedB (c : Config) (faulty : Finset Nat) (net : Network) (receiver : Nat)
    (input : Input) : Bool :=
  decide (receiver < c.parties) && decide (receiver ∉ faulty) &&
  match input with
  | .delivery m | .deliveryAt _ m =>
      decide (m.sender < c.parties) &&
        (decide (m.sender ∈ faulty) ||
          decide (Minidregg.Kernel.GenericSimplex.AuditEvent.send m ∈
            (net.localState m.sender).audit))
  | .tick _ | .checked _ | .offer _ | .poll => true

theorem allowedB_sound {c : Config} {faulty : Finset Nat} {net : Network} {receiver : Nat}
    {input : Input} (ok : allowedB c faulty net receiver input = true) :
    AllowedInput c faulty poleChecked net receiver input := by
  cases input <;>
    simp_all [allowedB, AllowedInput, authenticDelivery, poleChecked]

/-- Run a schedule of inputs through the REAL `advance`, refusing at the first input
`AllowedInput` would not admit. -/
def runChecked (c : Config) (faulty : Finset Nat) :
    Network → List (Nat × Input) → Option Network
  | net, [] => some net
  | net, (receiver, input) :: rest =>
      if allowedB c faulty net receiver input then
        runChecked c faulty (advance c faulty net receiver input) rest
      else none

theorem runChecked_reachable {c : Config} {faulty : Finset Nat} {time : Nat} :
    ∀ (schedule : List (Nat × Input)) (net result : Network),
      Reachable c faulty poleChecked time net →
      runChecked c faulty net schedule = some result →
      Reachable c faulty poleChecked time result
  | [], net, result, reachable, run => by
      simp only [runChecked, Option.some.injEq] at run
      exact run ▸ reachable
  | (receiver, input) :: rest, net, result, reachable, run => by
      unfold runChecked at run
      split at run
      · next ok =>
        exact runChecked_reachable rest _ result
          (.next reachable receiver input (allowedB_sound ok)) run
      · simp at run

/-- The pole schedule: the leader (party 0) is offered and checks a block, parties 1 and 2
check it; then every honest message is delivered to every other honest party. -/
def dl (receiver sender : Nat) (kind : Kind) : Nat × Input :=
  (receiver, .delivery ⟨sender, 1, kind, some [[1]]⟩)

def poleSchedule : List (Nat × Input) :=
  [(0, .offer [1]), (0, .checked [[1]]), (1, .checked [[1]]), (2, .checked [[1]]),
   dl 1 0 .propose, dl 2 0 .propose, dl 1 0 .vote, dl 2 0 .vote, dl 0 1 .vote,
   dl 2 1 .vote, dl 0 1 .candidate, dl 2 1 .candidate, dl 0 2 .vote, dl 1 2 .vote,
   dl 0 2 .candidate, dl 1 2 .candidate, dl 0 2 .commit, dl 1 2 .commit,
   dl 1 0 .candidate, dl 2 0 .candidate, dl 1 0 .commit, dl 2 0 .commit,
   dl 1 0 .ready, dl 2 0 .ready, dl 0 1 .commit, dl 2 1 .commit, dl 0 1 .ready,
   dl 2 1 .ready, dl 0 2 .ready, dl 1 2 .ready]

/-- The network reached from the real start by the schedule. -/
def poleNet : Network :=
  (runChecked poleConfig poleFaulty (initial poleConfig 0) poleSchedule).getD
    (initial poleConfig 0)

theorem poleRun_admitted :
    (runChecked poleConfig poleFaulty (initial poleConfig 0) poleSchedule).isSome = true := by
  decide +kernel

theorem poleNet_reachable : Reachable poleConfig poleFaulty poleChecked 0 poleNet := by
  unfold poleNet
  rcases hrun : runChecked poleConfig poleFaulty (initial poleConfig 0) poleSchedule with _ | net
  · have admitted := poleRun_admitted
    rw [hrun] at admitted
    simp at admitted
  · exact runChecked_reachable poleSchedule _ net .initial hrun

/-- The run really commits: party 0's view 1 holds a committed block. -/
theorem poleNet_commits :
    (viewAt (poleNet.localState 0) 1).committed = some [[1]] := by
  decide +kernel

theorem poleNet_delivers : [[1]] ∈ (poleNet.localState 0).delivered := by
  decide +kernel

/-- The actual engine step extends the retained audit, at a real started replica. -/
theorem auditExtension_real_step :
    AuditExtension (start poleConfig 0 0) (step poleConfig (start poleConfig 0 0) (.tick 1)) :=
  (structuralAuditLaws poleConfig).stepExtension _ _

/-- `AuditRefinement` holds at a network reached by real `step`s in which a block IS
committed and delivered (so its two observation clauses are exercised, not vacuous). -/
theorem auditRefinement_committed_run : AuditRefinement poleConfig poleFaulty poleNet :=
  actual_audit_refinement poleNet_reachable poleConfig_size

/-- `LocalFaithful` holds on the audit trace of that same run. -/
theorem localFaithful_committed_run :
    LocalFaithful (auditTrace poleNet) (Finset.range poleConfig.parties) poleFaulty
      poleConfig.faults :=
  actual_local_faithful poleNet_reachable poleConfig_size

/-- The refinement's commit clause turns the reported commit into an honest commit
output at view 1 (the genesis disjunct is false there). -/
theorem poleNet_commit_attested : CommittedAt (auditTrace poleNet) poleFaulty 1 [[1]] :=
  auditRefinement_committed_run.commits 0 1 [[1]] (by decide) (by decide) poleNet_commits

/-- A consumer using the satisfying instance: two honest replicas' commits are
prefix-compatible. -/
theorem poleNet_commits_compatible :
    ([[1]] : Block).IsPrefix [[1]] ∨ ([[1]] : Block).IsPrefix [[1]] :=
  refined_engine_commits_compatible auditRefinement_committed_run poleConfig_size
    poleFaulty_bound (p := 0) (q := 0) (v := 1) (w := 1) (by decide) (by decide)
    (by decide) (by decide) poleNet_commits poleNet_commits

/-- `LocalCommitOutputAttestations` on the real trace: honest parties 0, 1, 2 each retain
a commit output for `[[1]]` at view 1 (`2f+1 = 3`). -/
theorem localCommitAttestations_committed_run :
    LocalCommitOutputAttestations (auditTrace poleNet) (Finset.range 4) poleFaulty 1 1
      [[1]] := by
  refine ⟨{0, 1, 2}, ?_, by decide, ?_⟩
  · intro party member
    simp at member ⊢
    omega
  · intro party member _
    have honest : party = 0 ∨ party = 1 ∨ party = 2 := by
      simp at member
      omega
    have mem : Minidregg.Kernel.GenericSimplex.AuditEvent.commit party 1 [[1]] ∈ poleNet.audit := by
      rcases honest with rfl | rfl | rfl <;> decide +kernel
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp mem
    exact ⟨index, by simp [auditTrace, found]⟩

/-- A replica that reports a commit in view 1 while no commit output was ever retained
in the audit: the observation clause of `AuditRefinement` fails. -/
def poleForgedState : State :=
  { self := 0, deadline := 0, views := [{ number := 1, committed := some [] }] }

def poleForged : Network := ⟨fun _ => poleForgedState, []⟩

theorem not_auditRefinement_forged_commit :
    ¬ AuditRefinement poleConfig ∅ poleForged := by
  intro refinement
  have reported : (viewAt (poleForged.localState 0) 1).committed = some [] := by
    decide
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
    rfl
    rfl
  simp at same

/-- Honest party 0 sends COMMIT in view 1 with no vote quorum behind it:
`commitSend` fails. -/
def poleUnsupportedCommit : Trace := fun time =>
  if time = 0 then .send ⟨0, 1, .commit, some []⟩ else .idle

theorem not_localFaithful_unsupported_commit :
    ¬ LocalFaithful poleUnsupportedCommit (Finset.range 4) ∅ 1 := by
  intro rules
  obtain ⟨voters, _, count, sends⟩ := rules.commitSend 0 0 1 [] (by simp)
    rfl
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
  · decide
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
  have two : ({0, 1} : Finset Nat).card = 2 := by decide
  omega

#assert_axioms poleConfig_size
#assert_axioms poleConfig_wellFormed
#assert_axioms poleFaulty_bound
#assert_axioms allowedB_sound
#assert_axioms runChecked_reachable
#assert_axioms poleRun_admitted
#assert_axioms poleNet_reachable
#assert_axioms poleNet_commits
#assert_axioms poleNet_delivers
#assert_axioms poleNet_commit_attested
#assert_axioms poleNet_commits_compatible
#assert_axioms localCommitAttestations_committed_run
#assert_axioms auditExtension_real_step
#assert_axioms auditRefinement_committed_run
#assert_axioms localFaithful_committed_run
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
