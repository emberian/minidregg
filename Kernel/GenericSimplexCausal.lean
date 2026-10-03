import Kernel.GenericSimplexLocal

namespace Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
set_option autoImplicit false

/-- Executable view indices, rather than an assumed per-view map. -/
def ViewsUnique (s : State) : Prop := (s.views.map View.number).Nodup

theorem viewAt_number (s : State) (number : Nat) :
    (viewAt s number).number = number := by
  unfold viewAt
  cases found : s.views.find? (fun v => v.number == number) with
  | none => rfl
  | some v =>
    have test := List.find?_some found
    simpa using test

/-- Replacement keeps every existing index. This matters because flags must
remain attached to their actual view throughout register/broadcast. -/
theorem replacement_numbers (views : List View) (v : View) :
    (views.map (fun old => if old.number == v.number then v else old)).map View.number =
      views.map View.number := by
  induction views with
  | nil => rfl
  | cons old rest ih =>
    simp only [List.map_cons]
    split <;> simp_all

/-- First-match replacement is the supplied view even with duplicate input
indices; uniqueness is needed separately for unambiguous retained history. -/
theorem find_replacement (views : List View) (v : View)
    (existsView : views.any (fun old => old.number == v.number) = true) :
    (views.map (fun old => if old.number == v.number then v else old)).find?
      (fun old => old.number == v.number) = some v := by
  induction views with
  | nil => simp at existsView
  | cons old rest ih =>
    simp only [List.any_cons, Bool.or_eq_true] at existsView
    simp only [List.map_cons, List.find?_cons]
    by_cases same : old.number = v.number
    · simp [same]
    · simp [same]
      exact ih (existsView.resolve_left (by simpa using same))

theorem viewAt_put_same (s : State) (v : View) :
    viewAt (putView s v) v.number = v := by
  unfold putView viewAt
  split
  next present => simp [find_replacement s.views v present]
  next absent =>
    have missing : s.views.find? (fun old => old.number == v.number) = none := by
      apply List.find?_eq_none.mpr
      intro old member
      have tests := List.any_eq_false.mp (Bool.eq_false_iff.mpr absent) old member
      exact tests
    simp [List.find?_append, missing]

/-- An already recorded vote/disable request cannot emit another vote. -/
theorem castVote_guarded (s : State) (number : Nat) (block : Block)
    (guard : (viewAt s number).voted = true ∨
      (viewAt s number).disableRequested = true) :
    castVote s number block = s := by
  rcases guard with voted | disabled
  · simp [castVote, voted]
  · simp [castVote, disabled]

theorem broadcast_voted (s : State) (number : Nat) (kind : Kind) (arg : Argument) :
    (viewAt (broadcast s number kind arg) number).voted = (viewAt s number).voted := by
  unfold broadcast register
  dsimp only
  have numberExact := viewAt_number s number
  simpa only [numberExact] using congrArg View.voted
    (viewAt_put_same s {viewAt s number with received :=
      addUnique (viewAt s number).received ⟨s.self, number, kind, arg⟩})

/-- A successful local VOTE sets the durable per-view guard before broadcast. -/
theorem castVote_sets_guard (s : State) (number : Nat) (block : Block)
    (enabled : (viewAt s number).voted = false)
    (notDisabled : (viewAt s number).disableRequested = false) :
    (viewAt (castVote s number block) number).voted = true := by
  simp only [castVote, enabled, notDisabled, Bool.false_or, Bool.false_eq_true,
    if_false]
  rw [broadcast_voted]
  have numberExact := viewAt_number s number
  simpa only [numberExact] using congrArg View.voted
    (viewAt_put_same s {viewAt s number with voted := true})

/-- The second attempted vote emits nothing, independently of its block. -/
theorem castVote_once (s : State) (number : Nat) (first second : Block) :
    castVote (castVote s number first) number second = castVote s number first := by
  by_cases voted : (viewAt s number).voted = true
  · rw [castVote_guarded s number first (Or.inl voted)]
    exact castVote_guarded s number second (Or.inl voted)
  · by_cases disabled : (viewAt s number).disableRequested = true
    · rw [castVote_guarded s number first (Or.inr disabled)]
      exact castVote_guarded s number second (Or.inr disabled)
    · apply castVote_guarded
      exact Or.inl (castVote_sets_guard s number first
        (Bool.eq_false_iff.mpr voted) (Bool.eq_false_iff.mpr disabled))

/-- Exact emission: the vote guard changes before the one chronological send. -/
theorem castVote_audit_enabled (s : State) (number : Nat) (block : Block)
    (enabled : (viewAt s number).voted = false)
    (notDisabled : (viewAt s number).disableRequested = false) :
    (castVote s number block).audit =
      s.audit ++ [.send ⟨s.self, number, .vote, some block⟩] := by
  simp [castVote, enabled, notDisabled, broadcast, register, putView]

/-- Guard state is connected to actual retained emission, not network outbox.
Outbox draining cannot erase the witness. Composite preservation must establish
this at every reachable local state before extracting trace-level voteOnce. -/
def VoteRecorded (s : State) : Prop := ∀ number,
    (viewAt s number).voted = true ↔
      ∃ block, .send ⟨s.self, number, .vote, some block⟩ ∈ s.audit

def CandidateRecorded (s : State) : Prop := ∀ number arg,
    arg ∈ (viewAt s number).sentCandidates ↔
      .send ⟨s.self, number, .candidate, arg⟩ ∈ s.audit

def CommitRecorded (s : State) : Prop := ∀ number block,
    (viewAt s number).sentCommit = some block ↔
      .send ⟨s.self, number, .commit, some block⟩ ∈ s.audit

/-- Local commit/candidate compatibility applies to candidates before as well
as after the commit send, once flags are joined to the chronological audit. -/
theorem recorded_commit_candidate (s : State)
    (locked : StateLock s) (commits : CommitRecorded s)
    (candidates : CandidateRecorded s) (number : Nat) (block : Block) (arg : Argument)
    (sentCommit : .send ⟨s.self, number, .commit, some block⟩ ∈ s.audit)
    (sentCandidate : .send ⟨s.self, number, .candidate, arg⟩ ∈ s.audit) :
    arg = some block :=
  viewAt_locked s number locked block ((commits number block).mpr sentCommit)
    arg ((candidates number arg).mpr sentCandidate)

/-- At most one block is retained for each actual local VOTE incidence. -/
def VoteOnceAudit (s : State) : Prop := ∀ number first second,
    .send ⟨s.self, number, .vote, some first⟩ ∈ s.audit →
    .send ⟨s.self, number, .vote, some second⟩ ∈ s.audit → first = second

theorem voteOnce_unchanged_audit (before after : State)
    (sameSelf : after.self = before.self) (sameAudit : after.audit = before.audit)
    (once : VoteOnceAudit before) : VoteOnceAudit after := by
  unfold VoteOnceAudit
  simpa only [sameSelf, sameAudit] using once

theorem putView_voteOnce (s : State) (v : View) (once : VoteOnceAudit s) :
    VoteOnceAudit (putView s v) := once

theorem register_voteOnce (s : State) (message : Message) (once : VoteOnceAudit s) :
    VoteOnceAudit (register s message) := once

/-- Non-VOTE emission cannot manufacture a second local vote witness. -/
theorem broadcast_nonvote_voteOnce (s : State) (number : Nat) (kind : Kind)
    (arg : Argument) (notVote : kind ≠ .vote) (once : VoteOnceAudit s) :
    VoteOnceAudit (broadcast s number kind arg) := by
  intro n first second firstSent secondSent
  rw [broadcast_self] at firstSent secondSent
  rw [broadcast_audit] at firstSent secondSent
  have earlier : ∀ block,
      AuditEvent.send ⟨s.self, n, .vote, some block⟩ ∈
        s.audit ++ [.send ⟨s.self, number, kind, arg⟩] →
      AuditEvent.send ⟨s.self, n, .vote, some block⟩ ∈ s.audit := by
    intro block present
    rcases List.mem_append.mp present with old | added
    · exact old
    · have equal : Message.mk s.self n .vote (some block) =
          Message.mk s.self number kind arg := by simpa using added
      have kinds := congrArg Message.kind equal
      exact False.elim (notVote kinds.symm)
  exact once n first second (earlier first firstSent) (earlier second secondSent)

/-- Enabled castVote excludes all earlier votes using the actual flag/audit
join; exact broadcast supplies the unique new incidence. -/
theorem castVote_enabled_voteOnce (s : State) (number : Nat) (block : Block)
    (recorded : VoteRecorded s) (once : VoteOnceAudit s)
    (enabled : (viewAt s number).voted = false)
    (notDisabled : (viewAt s number).disableRequested = false) :
    VoteOnceAudit (castVote s number block) := by
  intro n first second firstSent secondSent
  have selfExact := castVote_self s number block
  rw [selfExact, castVote_audit_enabled s number block enabled notDisabled]
    at firstSent secondSent
  have noPrior : ∀ chosen,
      AuditEvent.send ⟨s.self, number, .vote, some chosen⟩ ∉ s.audit := by
    intro chosen prior
    have voted := (recorded number).mpr ⟨chosen, prior⟩
    simp [enabled] at voted
  rcases List.mem_append.mp firstSent with oldFirst | newFirst
  · rcases List.mem_append.mp secondSent with oldSecond | newSecond
    · exact once n first second oldFirst oldSecond
    · have equal : Message.mk s.self n .vote (some second) =
          Message.mk s.self number .vote (some block) := by simpa using newSecond
      have viewEqual := congrArg Message.view equal
      subst n
      exact False.elim (noPrior first oldFirst)
  · have equal : Message.mk s.self n .vote (some first) =
        Message.mk s.self number .vote (some block) := by simpa using newFirst
    have viewEqual := congrArg Message.view equal
    subst n
    rcases List.mem_append.mp secondSent with oldSecond | newSecond
    · exact False.elim (noPrior second oldSecond)
    · have other : Message.mk s.self number .vote (some second) =
          Message.mk s.self number .vote (some block) := by simpa using newSecond
      exact Option.some.inj ((congrArg Message.value equal).trans
        (congrArg Message.value other).symm)

theorem clear_voteOnce (s : State) (number : Nat) (arg : Argument)
    (once : VoteOnceAudit s) : VoteOnceAudit (clear s number arg) := by
  cases arg <;> unfold clear <;> dsimp only <;> split <;>
    simpa [VoteOnceAudit, putView] using once

theorem doCommit_voteOnce (s : State) (number : Nat) (block : Block)
    (once : VoteOnceAudit s) : VoteOnceAudit (doCommit s number block) := by
  have cleared := clear_voteOnce s number (some block) once
  unfold doCommit
  dsimp only
  split_ifs <;> simp_all [VoteOnceAudit, putView]

theorem sendCandidate_voteOnce (s : State) (number : Nat) (arg : Argument)
    (once : VoteOnceAudit s) : VoteOnceAudit (sendCandidate s number arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact once
  · exact broadcast_nonvote_voteOnce _ number .candidate arg (by decide)
      (putView_voteOnce s _ once)

theorem castVote_voteOnce (s : State) (number : Nat) (block : Block)
    (recorded : VoteRecorded s) (once : VoteOnceAudit s) :
    VoteOnceAudit (castVote s number block) := by
  by_cases voted : (viewAt s number).voted = true
  · rw [castVote_guarded s number block (Or.inl voted)]
    exact once
  · by_cases disabled : (viewAt s number).disableRequested = true
    · rw [castVote_guarded s number block (Or.inr disabled)]
      exact once
    · exact castVote_enabled_voteOnce s number block recorded once
        (Bool.eq_false_iff.mpr voted) (Bool.eq_false_iff.mpr disabled)

#assert_axioms clear_voteOnce
#assert_axioms doCommit_voteOnce
#assert_axioms sendCandidate_voteOnce
#assert_axioms castVote_voteOnce

#assert_axioms voteOnce_unchanged_audit
#assert_axioms putView_voteOnce
#assert_axioms register_voteOnce
#assert_axioms broadcast_nonvote_voteOnce
#assert_axioms castVote_enabled_voteOnce

#assert_axioms castVote_audit_enabled
#assert_axioms recorded_commit_candidate

#assert_axioms broadcast_voted
#assert_axioms castVote_sets_guard
#assert_axioms castVote_once

#assert_axioms viewAt_number
#assert_axioms replacement_numbers
#assert_axioms find_replacement
#assert_axioms viewAt_put_same
#assert_axioms castVote_guarded
end Minidregg.Kernel.GenericSimplexCausal
