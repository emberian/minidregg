import Kernel.GenericSimplexCausal
import Kernel.GenericSimplexVAInvariant

namespace Minidregg.Kernel.GenericSimplexPreparedHistory
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexVAInvariant
set_option autoImplicit false

def PreparedRecorded (s : State) : Prop := ∀ view block,
  block ∈ (viewAt s view).prepared → .prepare s.self view block ∈ s.audit

def DisabledRecorded (s : State) : Prop := ∀ view,
  (viewAt s view).disabled = true → .disable s.self view ∈ s.audit

structure HistoryInvariant (s : State) : Prop where
  prepared : PreparedRecorded s
  disabled : DisabledRecorded s

def localTrace (audit : List GenericSimplex.AuditEvent) : Trace :=
  fun time => audit[time]?.getD .idle

/-- Membership in the retained chronological audit gives a strict earlier
witness at the prefix length; this is not a future or final-trace assumption. -/
theorem earlier_from_member (audit : List GenericSimplex.AuditEvent)
    (event : GenericSimplex.AuditEvent) (member : event ∈ audit) :
    ∃ time < audit.length, localTrace audit time = event := by
  obtain ⟨time, within, exact⟩ := List.mem_iff_getElem.mp member
  refine ⟨time, within, ?_⟩
  simp [localTrace, List.getElem?_eq_getElem within, exact]

/-- The genesis preparation is executable preparedAt's dedicated view-zero
case. Every other preparation must come from an actual retained local output. -/
theorem preparedAt_witness (s : State) (view : Nat) (block : Block)
    (recorded : PreparedRecorded s) (member : block ∈ preparedAt s view) :
    PreparedBefore (localTrace s.audit) s.audit.length s.self view block := by
  by_cases genesis : view = 0
  · left
    refine ⟨genesis, ?_⟩
    simpa [preparedAt, genesis] using member
  · right
    have actual : block ∈ (viewAt s view).prepared := by
      simpa [preparedAt, genesis] using member
    exact earlier_from_member s.audit _ (recorded view block actual)

theorem disabledAt_witness (s : State) (view : Nat)
    (recorded : DisabledRecorded s) (disabled : disabledAt s view = true) :
    ∃ time < s.audit.length, localTrace s.audit time = .disable s.self view := by
  have actual : (viewAt s view).disabled = true := by
    unfold disabledAt at disabled
    split at disabled
    · contradiction
    · exact disabled
  exact earlier_from_member s.audit _ (recorded view actual)

/-- This extracts SafeAt from the ACTUAL executable Boolean over this local
source prefix. No SafeAt or abstract safe-vote premise is supplied by callers. -/
theorem isSafe_safeAt (s : State) (block : Block) (history : HistoryInvariant s)
    (safe : isSafe s block = true) :
    SafeAt (localTrace s.audit) s.audit.length s.self s.current block := by
  unfold isSafe at safe
  obtain ⟨nonempty, candidates⟩ := Bool.and_eq_true_iff.mp safe
  obtain ⟨previous, inRange, selected⟩ := List.any_eq_true.mp candidates
  obtain ⟨prepared, skipped⟩ := Bool.and_eq_true_iff.mp selected
  refine ⟨?_, previous, List.mem_range.mp inRange, ?_, ?_⟩
  · simpa using nonempty
  · apply preparedAt_witness s previous block.dropLast history.prepared
    simpa using prepared
  · intro view afterPrevious beforeCurrent
    let offset := view - (previous + 1)
    have offsetBound : offset < s.current - (previous + 1) := by
      dsimp [offset]
      omega
    have index : previous + 1 + offset = view := by
      dsimp [offset]
      omega
    have disabled := List.all_eq_true.mp skipped offset (List.mem_range.mpr offsetBound)
    rw [index] at disabled
    exact disabledAt_witness s view history.disabled disabled

theorem putView_prepared (s : State) (v : View)
    (same : v.prepared = (viewAt s v.number).prepared) (number : Nat) :
    (viewAt (putView s v) number).prepared = (viewAt s number).prepared := by
  by_cases index : number = v.number
  · subst number
    rw [viewAt_put_same]
    exact same
  · rw [viewAt_put_other s v number index]

theorem putView_disabled (s : State) (v : View)
    (same : v.disabled = (viewAt s v.number).disabled) (number : Nat) :
    (viewAt (putView s v) number).disabled = (viewAt s number).disabled := by
  by_cases index : number = v.number
  · subst number
    rw [viewAt_put_same]
    exact same
  · rw [viewAt_put_other s v number index]

theorem putView_history (s : State) (v : View) (old : HistoryInvariant s)
    (prepared : v.prepared = (viewAt s v.number).prepared)
    (disabled : v.disabled = (viewAt s v.number).disabled) :
    HistoryInvariant (putView s v) := by
  constructor
  · intro number block member
    rw [putView_prepared s v prepared number] at member
    exact old.prepared number block member
  · intro number flag
    rw [putView_disabled s v disabled number] at flag
    exact old.disabled number flag

theorem register_history (s : State) (message : Message) (old : HistoryInvariant s) :
    HistoryInvariant (register s message) := by
  unfold register
  dsimp only
  apply putView_history _ _ old <;> simp [viewAt_number]

/-- Broadcast adds a SEND; every prior local output remains in its prefix. -/
theorem broadcast_history (s : State) (view : Nat) (kind : Kind) (arg : Argument)
    (old : HistoryInvariant s) : HistoryInvariant (broadcast s view kind arg) := by
  have registered := register_history s ⟨s.self, view, kind, arg⟩ old
  constructor
  · intro number block member
    have previous := registered.prepared number block member
    exact List.mem_append_left _ previous
  · intro number flag
    have previous := registered.disabled number flag
    exact List.mem_append_left _ previous

theorem clear_none_history (s : State) (view : Nat) (old : HistoryInvariant s) :
    HistoryInvariant (clear s view none) := by
  unfold clear
  dsimp only
  split
  · exact old
  · let updated : View := {viewAt s view with disabled := true}
    have index : updated.number = view := viewAt_number s view
    constructor
    · intro number block member
      change block ∈ (viewAt (putView s updated) number).prepared at member
      have same : updated.prepared = (viewAt s updated.number).prepared := by
        simp [updated, viewAt_number]
      rw [putView_prepared s updated same number] at member
      exact List.mem_append_left _ (old.prepared number block member)
    · intro number flag
      change (viewAt (putView s updated) number).disabled = true at flag
      by_cases selectedView : number = view
      · subst number
        exact List.mem_append_right _ (by simp [putView])
      · have different : number ≠ updated.number := by simpa only [index] using selectedView
        rw [viewAt_put_other s updated number different] at flag
        exact List.mem_append_left _ (old.disabled number flag)

theorem clear_some_history (s : State) (view : Nat) (block : Block)
    (old : HistoryInvariant s) : HistoryInvariant (clear s view (some block)) := by
  unfold clear
  dsimp only
  split
  · let updated : View := {viewAt s view with prepared := (viewAt s view).prepared ++ [block]}
    have index : updated.number = view := viewAt_number s view
    constructor
    · intro number chosen member
      change chosen ∈ (viewAt (putView s updated) number).prepared at member
      by_cases selectedView : number = view
      · subst number
        have selected := viewAt_put_same s updated
        rw [index] at selected
        rw [selected] at member
        rcases List.mem_append.mp member with prior | added
        · exact List.mem_append_left _ (old.prepared view chosen prior)
        · have same : chosen = block := by simpa using added
          subst chosen
          exact List.mem_append_right _ (by simp [putView])
      · have different : number ≠ updated.number := by simpa only [index] using selectedView
        rw [viewAt_put_other s updated number different] at member
        exact List.mem_append_left _ (old.prepared number chosen member)
    · intro number flag
      change (viewAt (putView s updated) number).disabled = true at flag
      have same : updated.disabled = (viewAt s updated.number).disabled := by
        simp [updated, viewAt_number]
      rw [putView_disabled s updated same number] at flag
      exact List.mem_append_left _ (old.disabled number flag)
  · exact old

theorem clear_history (s : State) (view : Nat) (arg : Argument)
    (old : HistoryInvariant s) : HistoryInvariant (clear s view arg) := by
  cases arg with
  | none => exact clear_none_history s view old
  | some block => exact clear_some_history s view block old

#assert_axioms clear_none_history
#assert_axioms clear_some_history
#assert_axioms clear_history

theorem initial_history (self now deadline : Nat) (offers : List Bytes)
    (checked : List Block) :
    HistoryInvariant { self := self, now := now, deadline := deadline, offers := offers, checked := checked } := by
  constructor
  · simp [PreparedRecorded, viewAt]
  · simp [DisabledRecorded, viewAt]

theorem history_same_fields (before after : State) (old : HistoryInvariant before)
    (self : after.self = before.self) (views : after.views = before.views)
    (audit : after.audit = before.audit) : HistoryInvariant after := by
  constructor
  · simpa [PreparedRecorded, viewAt, self, views, audit] using old.prepared
  · simpa [DisabledRecorded, viewAt, self, views, audit] using old.disabled

@[simp] theorem history_record (s : State) (current deadline now : Nat)
    (checked : List Block) (offers : List Bytes) (outbox : List Message)
    (delivered : List Block) (tip : Block) (needsPoll failed : Bool) :
    HistoryInvariant { self := s.self, current := current, deadline := deadline, now := now, views := s.views, checked := checked, offers := offers, outbox := outbox, audit := s.audit, delivered := delivered, committedTip := tip, needsPoll := needsPoll, failed := failed } ↔ HistoryInvariant s := by
  constructor <;> intro old <;> rcases old with ⟨prepared, disabled⟩ <;> exact ⟨prepared, disabled⟩

theorem append_history (s : State) (event : GenericSimplex.AuditEvent)
    (old : HistoryInvariant s) : HistoryInvariant {s with audit := s.audit ++ [event]} := by
  constructor
  · intro view block member
    exact List.mem_append_left _ (old.prepared view block member)
  · intro view flag
    exact List.mem_append_left _ (old.disabled view flag)

theorem doCommit_history (s : State) (view : Nat) (block : Block)
    (old : HistoryInvariant s) : HistoryInvariant (doCommit s view block) := by
  let cleared := clear s view (some block)
  have clearInvariant : HistoryInvariant cleared := clear_history s view (some block) old
  let selected : View := {viewAt cleared view with committed := some block}
  have putInvariant : HistoryInvariant (putView cleared selected) := by
    apply putView_history _ _ clearInvariant <;> simp [selected, viewAt_number]
  have appended := append_history (putView cleared selected)
    (.commit (putView cleared selected).self view block) putInvariant
  unfold doCommit
  dsimp only
  split_ifs <;> first | exact old | exact clearInvariant | exact history_same_fields _ _ appended rfl rfl rfl

macro "history_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [history_record]
    | with_reducible apply register_history
    | with_reducible apply broadcast_history
    | with_reducible apply clear_history
    | with_reducible apply doCommit_history
    | with_reducible apply putView_history
    | solve | simp_all [viewAt_number]
    | split)
macro "history_chain" : tactic => `(tactic| repeat' history_step)

theorem sendCandidate_history (s : State) (view : Nat) (arg : Argument)
    (old : HistoryInvariant s) : HistoryInvariant (sendCandidate s view arg) := by
  unfold sendCandidate
  dsimp only
  history_chain

theorem castVote_history (s : State) (view : Nat) (block : Block)
    (old : HistoryInvariant s) : HistoryInvariant (castVote s view block) := by
  unfold castVote
  dsimp only
  history_chain

macro "history_action" : tactic => `(tactic|
  first
    | with_reducible apply sendCandidate_history
    | with_reducible apply castVote_history
    | history_step)
macro "history_actions" : tactic => `(tactic| repeat' history_action)

theorem history_fold {α : Type} (action : State → α → State)
    (each : ∀ state item, HistoryInvariant state → HistoryInvariant (action state item))
    (items : List α) (state : State) (old : HistoryInvariant state) :
    HistoryInvariant (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact old
  | cons item rest ih => exact ih (action state item) (each state item old)

theorem valueRules_history (c : Config) (s : State) (view : Nat) (block : Block)
    (old : HistoryInvariant s) : HistoryInvariant (valueRules c s view block) := by
  simp only [valueRules, Id.run, bind, pure]
  history_actions

theorem argumentRules_history (c : Config) (s : State) (view : Nat) (arg : Argument)
    (old : HistoryInvariant s) : HistoryInvariant (argumentRules c s view arg) := by
  simp only [argumentRules, Id.run, bind, pure]
  history_actions

theorem progressView_history (c : Config) (s : State) (view : Nat)
    (old : HistoryInvariant s) : HistoryInvariant (progressView c s view) := by
  simp only [progressView, Id.run, bind, pure]
  apply history_fold
  · intro state arg prior
    exact argumentRules_history c state view arg prior
  · apply history_fold
    · intro state block prior
      exact valueRules_history c state view block prior
    · exact old

theorem propose_history (s : State) (old : HistoryInvariant s) :
    HistoryInvariant (propose s) := by
  unfold propose
  dsimp only
  history_actions

theorem enterView_history (c : Config) (s : State) (view : Nat)
    (old : HistoryInvariant s) : HistoryInvariant (enterView c s view) := by
  unfold enterView
  dsimp only
  split
  · apply propose_history
    history_actions
  · history_actions

theorem progressOuter_history (c : Config) (s : State) (old : HistoryInvariant s) :
    HistoryInvariant (progressOuter c s) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | with_reducible apply enterView_history
    | history_action

theorem pass_history (c : Config) (s : State) (old : HistoryInvariant s) :
    HistoryInvariant (pass c s) := by
  unfold pass
  apply progressOuter_history
  apply history_fold
  · intro state view prior
    exact progressView_history c state view prior
  · exact old

theorem pump_history (c : Config) (fuel : Nat) (s : State) (old : HistoryInvariant s) :
    HistoryInvariant (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simpa only [pump, history_record] using old
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_history
      simpa only [history_record] using old
    · apply ih
      apply pass_history
      simpa only [history_record] using old

theorem ingest_history (c : Config) (s : State) (message : Message)
    (old : HistoryInvariant s) : HistoryInvariant (ingest c s message) := by
  unfold ingest
  dsimp only
  history_actions

theorem step_history (c : Config) (s : State) (input : Input) (old : HistoryInvariant s) :
    HistoryInvariant (step c s input) := by
  unfold step
  dsimp only
  split
  · history_actions
  · apply pump_history
    cases input with
    | delivery message => exact ingest_history c s message old
    | deliveryAt now message =>
      apply ingest_history
      history_actions
    | checked block => dsimp only; history_actions
    | offer payload => dsimp only; history_actions
    | poll => exact old
    | tick now =>
      dsimp only
      repeat' first
        | with_reducible apply pump_history
        | history_action

theorem start_history (c : Config) (self now : Nat) (offers : List Bytes)
    (checked : List Block) : HistoryInvariant (start c self now offers checked) := by
  unfold start
  split
  · exact history_same_fields _ _ (initial_history self now now [] []) rfl rfl rfl
  · apply pump_history
    apply enterView_history
    exact initial_history self now (now + c.timeout) offers checked

#assert_axioms history_same_fields
#assert_axioms history_record
#assert_axioms append_history
#assert_axioms doCommit_history
#assert_axioms sendCandidate_history
#assert_axioms castVote_history
#assert_axioms history_fold
#assert_axioms valueRules_history
#assert_axioms argumentRules_history
#assert_axioms progressView_history
#assert_axioms propose_history
#assert_axioms enterView_history
#assert_axioms progressOuter_history
#assert_axioms pass_history
#assert_axioms pump_history
#assert_axioms ingest_history
#assert_axioms step_history
#assert_axioms start_history

#assert_axioms putView_prepared
#assert_axioms putView_disabled
#assert_axioms putView_history
#assert_axioms register_history
#assert_axioms broadcast_history
#assert_axioms initial_history

#assert_axioms earlier_from_member
#assert_axioms preparedAt_witness
#assert_axioms disabledAt_witness
#assert_axioms isSafe_safeAt
end Minidregg.Kernel.GenericSimplexPreparedHistory
