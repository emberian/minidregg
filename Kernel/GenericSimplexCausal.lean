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
theorem putView_unique (s : State) (v : View) (unique : ViewsUnique s) :
    ViewsUnique (putView s v) := by
  unfold ViewsUnique putView
  dsimp only
  split
  · rw [replacement_numbers]
    exact unique
  next missing =>
    have absent : v.number ∉ s.views.map View.number := by
      intro member
      obtain ⟨old, inside, equal⟩ := List.mem_map.mp member
      have noMatch := List.any_eq_false.mp (Bool.eq_false_iff.mpr missing) old inside
      exact noMatch (by simpa [equal])
    simpa [List.map_append, absent] using unique

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
    · simp only [show (old.number == v.number) = false by simp [same],
        Bool.false_eq_true, if_false]
      exact ih (existsView.resolve_left (by simpa using same))

theorem viewAt_put_same (s : State) (v : View) :
    viewAt (putView s v) v.number = v := by
  unfold putView viewAt
  split
  next present => rw [find_replacement s.views v present]; rfl
  next absent =>
    have missing : s.views.find? (fun old => old.number == v.number) = none := by
      apply List.find?_eq_none.mpr
      intro old member
      have tests := List.any_eq_false.mp (Bool.eq_false_iff.mpr absent) old member
      exact tests
    simp [List.find?_append, missing]

theorem find_replacement_other (views : List View) (v : View) (number : Nat)
    (different : number ≠ v.number) :
    (views.map (fun old => if old.number == v.number then v else old)).find?
      (fun old => old.number == number) =
        views.find? (fun old => old.number == number) := by
  induction views with
  | nil => rfl
  | cons old rest ih =>
    by_cases replaced : old.number = v.number
    · simp only [List.map_cons, replaced, beq_self_eq_true, if_true, List.find?_cons]
      simp only [show (v.number == number) = false by simp [Ne.symm different], Bool.false_eq_true, if_false]
      exact ih
    · simp only [List.map_cons, show (old.number == v.number) = false by simp [replaced], Bool.false_eq_true, if_false, List.find?_cons]
      rw [ih]

theorem viewAt_put_other (s : State) (v : View) (number : Nat)
    (different : number ≠ v.number) :
    viewAt (putView s v) number = viewAt s number := by
  unfold putView viewAt
  split
  · rw [find_replacement_other s.views v number different]
  · simp [List.find?_append, Ne.symm different]

/-- Actual putView updates preserve the vote flag if their one changed view
retains it. This prevents silently resetting voteOnce through later rules. -/
theorem putView_voted (s : State) (v : View)
    (sameVote : v.voted = (viewAt s v.number).voted) (number : Nat) :
    (viewAt (putView s v) number).voted = (viewAt s number).voted := by
  by_cases same : number = v.number
  · subst number
    rw [viewAt_put_same]
    exact sameVote
  · rw [viewAt_put_other s v number same]

theorem putView_candidates (s : State) (v : View)
    (same : v.sentCandidates = (viewAt s v.number).sentCandidates) (number : Nat) :
    (viewAt (putView s v) number).sentCandidates = (viewAt s number).sentCandidates := by
  by_cases index : number = v.number
  · subst number
    rw [viewAt_put_same]
    exact same
  · rw [viewAt_put_other s v number index]

theorem putView_commit (s : State) (v : View)
    (same : v.sentCommit = (viewAt s v.number).sentCommit) (number : Nat) :
    (viewAt (putView s v) number).sentCommit = (viewAt s number).sentCommit := by
  by_cases index : number = v.number
  · subst number
    rw [viewAt_put_same]
    exact same
  · rw [viewAt_put_other s v number index]

theorem register_voted (s : State) (message : Message) (number : Nat) :
    (viewAt (register s message) number).voted = (viewAt s number).voted := by
  unfold register
  dsimp only
  apply putView_voted
  simp [viewAt_number]

#assert_axioms find_replacement_other
#assert_axioms viewAt_put_other
#assert_axioms putView_voted
#assert_axioms register_voted

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
  exact register_voted s ⟨s.self, number, kind, arg⟩ number

/-- A successful local VOTE sets the durable per-view guard before broadcast. -/
theorem castVote_sets_guard (s : State) (number : Nat) (block : Block)
    (enabled : (viewAt s number).voted = false)
    (notDisabled : (viewAt s number).disableRequested = false) :
    (viewAt (castVote s number block) number).voted = true := by
  simp only [castVote, enabled, notDisabled, Bool.false_or, Bool.false_eq_true,
    if_false]
  rw [broadcast_voted]
  let updated : View := {viewAt s number with voted := true}
  have exactView := viewAt_put_same s updated
  have index : updated.number = number := viewAt_number s number
  rw [index] at exactView
  simpa [updated, notDisabled] using congrArg View.voted exactView

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

theorem putView_voteRecorded (s : State) (v : View)
    (sameVote : v.voted = (viewAt s v.number).voted) (recorded : VoteRecorded s) :
    VoteRecorded (putView s v) := by
  intro number
  rw [putView_voted s v sameVote number]
  exact recorded number

theorem register_voteRecorded (s : State) (message : Message)
    (recorded : VoteRecorded s) : VoteRecorded (register s message) := by
  intro number
  rw [register_voted s message number]
  exact recorded number

def CandidateRecorded (s : State) : Prop := ∀ number arg,
    arg ∈ (viewAt s number).sentCandidates ↔
      .send ⟨s.self, number, .candidate, arg⟩ ∈ s.audit

def CommitRecorded (s : State) : Prop := ∀ number block,
    (viewAt s number).sentCommit = some block ↔
      .send ⟨s.self, number, .commit, some block⟩ ∈ s.audit

theorem putView_candidateRecorded (s : State) (v : View)
    (same : v.sentCandidates = (viewAt s v.number).sentCandidates)
    (recorded : CandidateRecorded s) : CandidateRecorded (putView s v) := by
  intro number arg
  rw [putView_candidates s v same number]
  exact recorded number arg

theorem putView_commitRecorded (s : State) (v : View)
    (same : v.sentCommit = (viewAt s v.number).sentCommit)
    (recorded : CommitRecorded s) : CommitRecorded (putView s v) := by
  intro number block
  rw [putView_commit s v same number]
  exact recorded number block

theorem register_candidateRecorded (s : State) (message : Message)
    (recorded : CandidateRecorded s) : CandidateRecorded (register s message) := by
  unfold register
  dsimp only
  apply putView_candidateRecorded _ _ _ recorded
  simp [viewAt_number]

theorem register_commitRecorded (s : State) (message : Message)
    (recorded : CommitRecorded s) : CommitRecorded (register s message) := by
  unfold register
  dsimp only
  apply putView_commitRecorded _ _ _ recorded
  simp [viewAt_number]

#assert_axioms putView_candidates
#assert_axioms putView_commit
#assert_axioms putView_candidateRecorded
#assert_axioms putView_commitRecorded
#assert_axioms register_candidateRecorded
#assert_axioms register_commitRecorded

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
      have viewEqual : n = number := congrArg Message.view equal
      subst n
      exact False.elim (noPrior first oldFirst)
  · have equal : Message.mk s.self n .vote (some first) =
        Message.mk s.self number .vote (some block) := by simpa using newFirst
    have viewEqual : n = number := congrArg Message.view equal
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
  split_ifs <;> first | simpa [VoteOnceAudit, putView] using once | simpa [VoteOnceAudit, putView] using cleared

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

theorem broadcast_voted_all (s : State) (view : Nat) (kind : Kind)
    (arg : Argument) (number : Nat) :
    (viewAt (broadcast s view kind arg) number).voted = (viewAt s number).voted := by
  exact register_voted s ⟨s.self, view, kind, arg⟩ number

theorem clear_voted (s : State) (view : Nat) (arg : Argument) (number : Nat) :
    (viewAt (clear s view arg) number).voted = (viewAt s number).voted := by
  cases arg <;> unfold clear <;> dsimp only <;> split
  · rfl
  · apply putView_voted
    simp [viewAt_number]
  · apply putView_voted
    simp [viewAt_number]
  · rfl

theorem doCommit_voted (s : State) (view : Nat) (block : Block) (number : Nat) :
    (viewAt (doCommit s view block) number).voted = (viewAt s number).voted := by
  have clearFlag := clear_voted s view (some block) number
  have putFlag := putView_voted (clear s view (some block))
    {viewAt (clear s view (some block)) view with committed := some block}
    (by simp [viewAt_number]) number
  unfold doCommit
  dsimp only
  split_ifs <;> first | rfl | exact clearFlag | exact putFlag.trans clearFlag

/-- A commit output appends no VOTE event and cannot reset the voted guard. -/
theorem doCommit_vote_membership (s : State) (view number : Nat) (block vote : Block) :
    AuditEvent.send ⟨(doCommit s view block).self, number, .vote, some vote⟩ ∈
      (doCommit s view block).audit ↔
    AuditEvent.send ⟨s.self, number, .vote, some vote⟩ ∈ s.audit := by
  unfold doCommit clear
  dsimp only
  split_ifs <;> simp [putView]

theorem clear_vote_membership (s : State) (view number : Nat) (arg : Argument)
    (block : Block) :
    AuditEvent.send ⟨(clear s view arg).self, number, .vote, some block⟩ ∈
      (clear s view arg).audit ↔
    AuditEvent.send ⟨s.self, number, .vote, some block⟩ ∈ s.audit := by
  cases arg <;> unfold clear <;> dsimp only <;> split <;> simp [putView]

theorem clear_voteRecorded (s : State) (view : Nat) (arg : Argument)
    (recorded : VoteRecorded s) : VoteRecorded (clear s view arg) := by
  intro number
  rw [clear_voted]
  simpa only [clear_vote_membership] using recorded number

theorem broadcast_nonvote_voteRecorded (s : State) (view : Nat) (kind : Kind)
    (arg : Argument) (notVote : kind ≠ .vote) (recorded : VoteRecorded s) :
    VoteRecorded (broadcast s view kind arg) := by
  intro number
  rw [broadcast_voted_all]
  have members : ∀ block,
      AuditEvent.send ⟨(broadcast s view kind arg).self, number, .vote, some block⟩ ∈
        (broadcast s view kind arg).audit ↔
      AuditEvent.send ⟨s.self, number, .vote, some block⟩ ∈ s.audit := by
    intro block
    rw [broadcast_self, broadcast_audit]
    simp [Ne.symm notVote]
  simpa only [members] using recorded number

#assert_axioms broadcast_nonvote_voteRecorded

theorem doCommit_voteRecorded (s : State) (view : Nat) (block : Block)
    (recorded : VoteRecorded s) : VoteRecorded (doCommit s view block) := by
  intro number
  rw [doCommit_voted]
  simpa only [doCommit_vote_membership] using recorded number

theorem register_candidates (s : State) (message : Message) (number : Nat) :
    (viewAt (register s message) number).sentCandidates = (viewAt s number).sentCandidates := by
  unfold register
  dsimp only
  apply putView_candidates
  simp [viewAt_number]

theorem register_commit (s : State) (message : Message) (number : Nat) :
    (viewAt (register s message) number).sentCommit = (viewAt s number).sentCommit := by
  unfold register
  dsimp only
  apply putView_commit
  simp [viewAt_number]

theorem broadcast_candidates (s : State) (view : Nat) (kind : Kind)
    (arg : Argument) (number : Nat) :
    (viewAt (broadcast s view kind arg) number).sentCandidates =
      (viewAt s number).sentCandidates :=
  register_candidates s ⟨s.self, view, kind, arg⟩ number

theorem broadcast_commit (s : State) (view : Nat) (kind : Kind)
    (arg : Argument) (number : Nat) :
    (viewAt (broadcast s view kind arg) number).sentCommit = (viewAt s number).sentCommit :=
  register_commit s ⟨s.self, view, kind, arg⟩ number

theorem broadcast_other_candidateRecorded (s : State) (view : Nat) (kind : Kind)
    (arg : Argument) (different : kind ≠ .candidate) (recorded : CandidateRecorded s) :
    CandidateRecorded (broadcast s view kind arg) := by
  intro number candidate
  rw [broadcast_candidates, broadcast_self, broadcast_audit]
  simpa [Ne.symm different] using recorded number candidate

theorem broadcast_other_commitRecorded (s : State) (view : Nat) (kind : Kind)
    (arg : Argument) (different : kind ≠ .commit) (recorded : CommitRecorded s) :
    CommitRecorded (broadcast s view kind arg) := by
  intro number block
  rw [broadcast_commit, broadcast_self, broadcast_audit]
  simpa [Ne.symm different] using recorded number block

#assert_axioms register_candidates
#assert_axioms register_commit
#assert_axioms broadcast_candidates
#assert_axioms broadcast_commit
#assert_axioms broadcast_other_candidateRecorded
#assert_axioms broadcast_other_commitRecorded

theorem sendCandidate_candidateRecorded (s : State) (view : Nat) (arg : Argument)
    (recorded : CandidateRecorded s) : CandidateRecorded (sendCandidate s view arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact recorded
  · intro number candidate
    rw [broadcast_candidates, broadcast_self, broadcast_audit]
    let updated : View := {viewAt s view with
      sentCandidates := (viewAt s view).sentCandidates ++ [arg]}
    have index : updated.number = view := viewAt_number s view
    by_cases same : number = view
    · subst number
      have selected := viewAt_put_same s updated
      rw [index] at selected
      rw [selected]
      simpa [updated, putView] using
        (or_congr (recorded view candidate) (Iff.rfl : candidate = arg ↔ candidate = arg))
    · have other : number ≠ updated.number := by simpa only [index] using same
      rw [viewAt_put_other s updated number other]
      simpa [putView, same] using recorded number candidate

#assert_axioms sendCandidate_candidateRecorded

theorem clear_candidates (s : State) (view : Nat) (arg : Argument) (number : Nat) :
    (viewAt (clear s view arg) number).sentCandidates = (viewAt s number).sentCandidates := by
  cases arg <;> unfold clear <;> dsimp only <;> split
  · rfl
  · apply putView_candidates
    simp [viewAt_number]
  · apply putView_candidates
    simp [viewAt_number]
  · rfl

theorem clear_commit (s : State) (view : Nat) (arg : Argument) (number : Nat) :
    (viewAt (clear s view arg) number).sentCommit = (viewAt s number).sentCommit := by
  cases arg <;> unfold clear <;> dsimp only <;> split
  · rfl
  · apply putView_commit
    simp [viewAt_number]
  · apply putView_commit
    simp [viewAt_number]
  · rfl

theorem clear_candidate_membership (s : State) (view number : Nat) (clearArg : Argument)
    (arg : Argument) :
    AuditEvent.send ⟨(clear s view clearArg).self, number, .candidate, arg⟩ ∈
      (clear s view clearArg).audit ↔
    AuditEvent.send ⟨s.self, number, .candidate, arg⟩ ∈ s.audit := by
  cases clearArg <;> unfold clear <;> dsimp only <;> split <;> simp [putView]

theorem clear_commit_membership (s : State) (view number : Nat) (clearArg : Argument)
    (block : Block) :
    AuditEvent.send ⟨(clear s view clearArg).self, number, .commit, (some block)⟩ ∈
      (clear s view clearArg).audit ↔
    AuditEvent.send ⟨s.self, number, .commit, (some block)⟩ ∈ s.audit := by
  cases clearArg <;> unfold clear <;> dsimp only <;> split <;> simp [putView]

theorem clear_candidateRecorded (s : State) (view : Nat) (arg : Argument)
    (recorded : CandidateRecorded s) : CandidateRecorded (clear s view arg) := by
  intro number value
  rw [clear_candidates]
  simpa only [clear_candidate_membership] using recorded number value

theorem clear_commitRecorded (s : State) (view : Nat) (arg : Argument)
    (recorded : CommitRecorded s) : CommitRecorded (clear s view arg) := by
  intro number value
  rw [clear_commit]
  simpa only [clear_commit_membership] using recorded number value

theorem castVote_voteRecorded (s : State) (view : Nat) (block : Block)
    (recorded : VoteRecorded s) : VoteRecorded (castVote s view block) := by
  unfold castVote
  dsimp only
  split
  · exact recorded
  · intro number
    rw [broadcast_voted_all, broadcast_self, broadcast_audit]
    let updated : View := {viewAt s view with voted := true}
    have index : updated.number = view := viewAt_number s view
    by_cases same : number = view
    · subst number
      have selected := viewAt_put_same s updated
      rw [index] at selected
      rw [selected]
      simp [updated, putView]
    · have other : number ≠ updated.number := by simpa only [index] using same
      rw [viewAt_put_other s updated number other]
      simpa [putView, same] using recorded number

#assert_axioms castVote_voteRecorded

/-- Exact intermediate update and broadcast used by valueRules COMMIT branch. -/
theorem commit_send_recorded (s : State) (view : Nat) (block : Block)
    (recorded : CommitRecorded s) (notSent : (viewAt s view).sentCommit = none) :
    CommitRecorded (broadcast (putView s {viewAt s view with sentCommit := some block})
      view .commit (some block)) := by
  intro number chosen
  rw [broadcast_commit, broadcast_self, broadcast_audit]
  let updated : View := {viewAt s view with sentCommit := some block}
  have index : updated.number = view := viewAt_number s view
  by_cases same : number = view
  · subst number
    have selected := viewAt_put_same s updated
    rw [index] at selected
    rw [selected]
    have absent : AuditEvent.send ⟨s.self, view, .commit, some chosen⟩ ∉ s.audit := by
      intro member
      have impossible := (recorded view chosen).mpr member
      rw [notSent] at impossible
      contradiction
    simp [updated, putView, absent]
  · have other : number ≠ updated.number := by simpa only [index] using same
    rw [viewAt_put_other s updated number other]
    simpa [putView, same] using recorded number chosen

#assert_axioms commit_send_recorded

/-- The exact local bundle consumed by reachable safety extraction. None of
these fields assumes agreement, quorum intersection or a global safety result. -/
structure CausalInvariant (s : State) : Prop where
  viewsUnique : ViewsUnique s
  voteRecorded : VoteRecorded s
  voteOnce : VoteOnceAudit s
  candidateRecorded : CandidateRecorded s
  commitRecorded : CommitRecorded s
  commitLock : StateLock s

theorem putView_causal (s : State) (v : View) (old : CausalInvariant s)
    (vote : v.voted = (viewAt s v.number).voted)
    (candidates : v.sentCandidates = (viewAt s v.number).sentCandidates)
    (commit : v.sentCommit = (viewAt s v.number).sentCommit)
    (lock : ViewLock v) : CausalInvariant (putView s v) where
  viewsUnique := putView_unique s v old.viewsUnique
  voteRecorded := putView_voteRecorded s v vote old.voteRecorded
  voteOnce := putView_voteOnce s v old.voteOnce
  candidateRecorded := putView_candidateRecorded s v candidates old.candidateRecorded
  commitRecorded := putView_commitRecorded s v commit old.commitRecorded
  commitLock := putView_locked s v old.commitLock lock

theorem register_causal (s : State) (message : Message) (old : CausalInvariant s) :
    CausalInvariant (register s message) := by
  unfold register
  dsimp only
  apply putView_causal _ _ old
  · simp [viewAt_number]
  · simp [viewAt_number]
  · simp [viewAt_number]
  · exact viewAt_locked s message.view old.commitLock

#assert_axioms putView_causal
#assert_axioms register_causal
theorem broadcast_other_causal (s : State) (view : Nat) (kind : Kind)
    (arg : Argument) (old : CausalInvariant s)
    (notVote : kind ≠ .vote) (notCandidate : kind ≠ .candidate) (notCommit : kind ≠ .commit) :
    CausalInvariant (broadcast s view kind arg) where
  viewsUnique := (register_causal s ⟨s.self, view, kind, arg⟩ old).viewsUnique
  voteRecorded := broadcast_nonvote_voteRecorded s view kind arg notVote old.voteRecorded
  voteOnce := broadcast_nonvote_voteOnce s view kind arg notVote old.voteOnce
  candidateRecorded := broadcast_other_candidateRecorded s view kind arg notCandidate old.candidateRecorded
  commitRecorded := broadcast_other_commitRecorded s view kind arg notCommit old.commitRecorded
  commitLock := broadcast_locked s view kind arg old.commitLock

#assert_axioms broadcast_other_causal
theorem clear_causal (s : State) (view : Nat) (arg : Argument)
    (old : CausalInvariant s) : CausalInvariant (clear s view arg) := by
  constructor
  · cases arg <;> unfold clear <;> dsimp only <;> split
    · exact old.viewsUnique
    · exact putView_unique _ _ old.viewsUnique
    · exact putView_unique _ _ old.viewsUnique
    · exact old.viewsUnique
  · exact clear_voteRecorded s view arg old.voteRecorded
  · exact clear_voteOnce s view arg old.voteOnce
  · exact clear_candidateRecorded s view arg old.candidateRecorded
  · exact clear_commitRecorded s view arg old.commitRecorded
  · exact clear_locked s view arg old.commitLock

#assert_axioms clear_candidates
#assert_axioms clear_commit
#assert_axioms clear_candidate_membership
#assert_axioms clear_commit_membership
#assert_axioms clear_candidateRecorded
#assert_axioms clear_commitRecorded
#assert_axioms clear_causal

theorem append_commit_causal (s : State) (view : Nat) (block : Block)
    (old : CausalInvariant s) :
    CausalInvariant {s with audit := s.audit ++ [.commit s.self view block]} := by
  constructor
  · exact old.viewsUnique
  · simpa [VoteRecorded] using old.voteRecorded
  · simpa [VoteOnceAudit] using old.voteOnce
  · simpa [CandidateRecorded] using old.candidateRecorded
  · simpa [CommitRecorded] using old.commitRecorded
  · exact old.commitLock

theorem doCommit_causal (s : State) (view : Nat) (block : Block)
    (old : CausalInvariant s) : CausalInvariant (doCommit s view block) := by
  let cleared := clear s view (some block)
  have clearInvariant : CausalInvariant cleared := clear_causal s view (some block) old
  let selected : View := {viewAt cleared view with committed := some block}
  have putInvariant : CausalInvariant (putView cleared selected) := by
    apply putView_causal _ _ clearInvariant
    · simp [selected, viewAt_number]
    · simp [selected, viewAt_number]
    · simp [selected, viewAt_number]
    · exact viewAt_locked cleared view clearInvariant.commitLock
  have appended := append_commit_causal (putView cleared selected) view block putInvariant
  unfold doCommit
  dsimp only
  split_ifs <;> first | exact old | exact clearInvariant | exact appended

#assert_axioms append_commit_causal
#assert_axioms doCommit_causal

theorem register_unique (s : State) (message : Message) (old : ViewsUnique s) :
    ViewsUnique (register s message) := putView_unique s _ old

theorem sendCandidate_causal (s : State) (view : Nat) (arg : Argument)
    (old : CausalInvariant s) : CausalInvariant (sendCandidate s view arg) := by
  have candidate := sendCandidate_candidateRecorded s view arg old.candidateRecorded
  have once := sendCandidate_voteOnce s view arg old.voteOnce
  have locked := sendCandidate_locked s view arg old.commitLock
  unfold sendCandidate
  dsimp only
  split
  · exact old
  · constructor
    · exact register_unique _ _ (putView_unique s _ old.viewsUnique)
    · apply broadcast_nonvote_voteRecorded _ view .candidate arg (by decide)
      apply putView_voteRecorded _ _ _ old.voteRecorded
      simp [viewAt_number]
    · simpa [sendCandidate, *] using once
    · simpa [sendCandidate, *] using candidate
    · apply broadcast_other_commitRecorded _ view .candidate arg (by decide)
      apply putView_commitRecorded _ _ _ old.commitRecorded
      simp [viewAt_number]
    · simpa [sendCandidate, *] using locked

#assert_axioms register_unique
#assert_axioms sendCandidate_causal

theorem castVote_causal (s : State) (view : Nat) (block : Block)
    (old : CausalInvariant s) : CausalInvariant (castVote s view block) := by
  have recorded := castVote_voteRecorded s view block old.voteRecorded
  have once := castVote_voteOnce s view block old.voteRecorded old.voteOnce
  unfold castVote
  dsimp only
  split
  · exact old
  · constructor
    · exact register_unique _ _ (putView_unique s _ old.viewsUnique)
    · simpa [castVote, *] using recorded
    · simpa [castVote, *] using once
    · apply broadcast_other_candidateRecorded _ view .vote (some block) (by decide)
      apply putView_candidateRecorded _ _ _ old.candidateRecorded
      simp [viewAt_number]
    · apply broadcast_other_commitRecorded _ view .vote (some block) (by decide)
      apply putView_commitRecorded _ _ _ old.commitRecorded
      simp [viewAt_number]
    · apply broadcast_locked
      apply putView_locked _ _ old.commitLock
      exact viewAt_locked s view old.commitLock

#assert_axioms castVote_causal

theorem commit_send_causal (s : State) (view : Nat) (block : Block)
    (old : CausalInvariant s) (notSent : (viewAt s view).sentCommit = none)
    (onlyThis : (viewAt s view).sentCandidates.all (fun arg => arg == some block) = true) :
    CausalInvariant (broadcast (putView s {viewAt s view with sentCommit := some block})
      view .commit (some block)) := by
  constructor
  · exact register_unique _ _ (putView_unique s _ old.viewsUnique)
  · apply broadcast_nonvote_voteRecorded _ view .commit (some block) (by decide)
    apply putView_voteRecorded _ _ _ old.voteRecorded
    simp [viewAt_number]
  · apply broadcast_nonvote_voteOnce _ view .commit (some block) (by decide)
    exact putView_voteOnce s _ old.voteOnce
  · apply broadcast_other_candidateRecorded _ view .commit (some block) (by decide)
    apply putView_candidateRecorded _ _ _ old.candidateRecorded
    simp [viewAt_number]
  · exact commit_send_recorded s view block old.commitRecorded notSent
  · apply broadcast_locked
    apply putView_locked _ _ old.commitLock
    exact commit_record_locked (viewAt s view) block onlyThis

#assert_axioms commit_send_causal

/-- The actual executable empty state before enterView/start pumping. -/
theorem initial_causal (self now deadline : Nat) (offers : List Bytes)
    (checked : List Block) :
    CausalInvariant { self := self, now := now, deadline := deadline,
      offers := offers, checked := checked } := by
  constructor
  · simp [ViewsUnique]
  · simp [VoteRecorded, viewAt]
  · simp [VoteOnceAudit]
  · simp [CandidateRecorded, viewAt]
  · simp [CommitRecorded, viewAt]
  · simp [StateLock]

theorem drain_causal (s : State) (invariant : CausalInvariant s) :
    CausalInvariant (drainOutbox s).2 := invariant

#assert_axioms putView_unique
#assert_axioms initial_causal
#assert_axioms drain_causal

#assert_axioms doCommit_voted
#assert_axioms doCommit_vote_membership
#assert_axioms doCommit_voteRecorded

#assert_axioms clear_vote_membership
#assert_axioms clear_voteRecorded

#assert_axioms putView_voteRecorded
#assert_axioms register_voteRecorded
#assert_axioms broadcast_voted_all
#assert_axioms clear_voted

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
