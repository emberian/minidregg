import Kernel.GenericSimplexCausal
import Mathlib.Tactic.SplitIfs

namespace Minidregg.Kernel.GenericSimplexOutputHistory
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
set_option autoImplicit false

/-- This records COMMIT outputs, not sent COMMIT messages. -/
def CommittedRecorded (s : State) : Prop :=
  ∀ view block, (viewAt s view).committed = some block →
    AuditEvent.commit s.self view block ∈ s.audit

def DeliveredRecorded (s : State) : Prop :=
  ∀ block ∈ s.delivered, ∃ view, AuditEvent.commit s.self view block ∈ s.audit

structure OutputHistory (s : State) : Prop where
  committed : CommittedRecorded s
  delivered : DeliveredRecorded s

theorem putView_committed (s : State) (v : View)
    (same : v.committed = (viewAt s v.number).committed) (number : Nat) :
    (viewAt (putView s v) number).committed = (viewAt s number).committed := by
  by_cases chosen : number = v.number
  · subst number
    rw [viewAt_put_same]
    exact same
  · rw [viewAt_put_other s v number chosen]

theorem putView_output (s : State) (v : View) (old : OutputHistory s)
    (same : v.committed = (viewAt s v.number).committed) :
    OutputHistory (putView s v) := by
  constructor
  · intro number block flag
    rw [putView_committed s v same number] at flag
    exact old.committed number block flag
  · exact old.delivered

theorem append_output (s : State) (events : List AuditEvent) (old : OutputHistory s) :
    OutputHistory {s with audit := s.audit ++ events} := by
  constructor
  · intro view block flag
    exact List.mem_append_left _ (old.committed view block flag)
  · intro block member
    obtain ⟨view, witness⟩ := old.delivered block member
    exact ⟨view, List.mem_append_left _ witness⟩

@[simp] theorem output_record (s : State) (current deadline now : Nat)
    (checked : List Block) (offers : List Bytes) (outbox : List Message)
    (tip : Block) (needsPoll failed : Bool) :
    OutputHistory {self := s.self, current := current, deadline := deadline, now := now, views := s.views, checked := checked, offers := offers, outbox := outbox, audit := s.audit, delivered := s.delivered, committedTip := tip, needsPoll := needsPoll, failed := failed} ↔ OutputHistory s := by
  constructor <;> intro old <;> rcases old with ⟨committed, delivered⟩ <;>
    exact ⟨committed, delivered⟩

theorem output_same_fields (before after : State) (old : OutputHistory before)
    (self : after.self = before.self) (views : after.views = before.views)
    (audit : after.audit = before.audit) (delivered : after.delivered = before.delivered) :
    OutputHistory after := by
  constructor
  · simpa [CommittedRecorded, viewAt, self, views, audit] using old.committed
  · simpa [DeliveredRecorded, self, audit, delivered] using old.delivered

theorem initial_output (self now deadline : Nat) (offers : List Bytes) (checked : List Block) :
    OutputHistory {self := self, now := now, deadline := deadline, offers := offers, checked := checked} := by
  constructor
  · simp [CommittedRecorded, viewAt]
  · simp [DeliveredRecorded]

theorem register_output (s : State) (message : Message) (old : OutputHistory s) :
    OutputHistory (register s message) := by
  unfold register
  dsimp only
  apply putView_output _ _ old
  simp [viewAt_number]

theorem broadcast_output (s : State) (view : Nat) (kind : Kind) (arg : Argument)
    (old : OutputHistory s) : OutputHistory (broadcast s view kind arg) := by
  have recorded := append_output (register s ⟨s.self, view, kind, arg⟩)
    [AuditEvent.send ⟨s.self, view, kind, arg⟩] (register_output s ⟨s.self, view, kind, arg⟩ old)
  exact output_same_fields _ _ recorded rfl rfl rfl rfl

theorem clear_output (s : State) (view : Nat) (arg : Argument) (old : OutputHistory s) :
    OutputHistory (clear s view arg) := by
  cases arg <;> unfold clear <;> dsimp only <;> split
  · exact old
  · apply append_output
    apply putView_output _ _ old
    simp [viewAt_number]
  · apply append_output
    apply putView_output _ _ old
    simp [viewAt_number]
  · exact old

/-- Exact committed-field update followed by its retained output. -/
theorem commitUpdate_output (s : State) (view : Nat) (block : Block) (old : OutputHistory s) :
    let next := putView s {viewAt s view with committed := some block}
    OutputHistory {next with audit := next.audit ++ [.commit next.self view block]} := by
  let updated : View := {viewAt s view with committed := some block}
  have index : updated.number = view := viewAt_number s view
  constructor
  · intro number chosen flag
    change (viewAt (putView s updated) number).committed = some chosen at flag
    by_cases same : number = view
    · subst number
      have selected := viewAt_put_same s updated
      rw [index] at selected
      rw [selected] at flag
      have equal : block = chosen := Option.some.inj flag
      subst chosen
      exact List.mem_append_right _ (by simp)
    · have other : number ≠ updated.number := by simpa only [index] using same
      rw [viewAt_put_other s updated number other] at flag
      exact List.mem_append_left _ (old.committed number chosen flag)
  · intro chosen member
    obtain ⟨number, witness⟩ := old.delivered chosen member
    exact ⟨number, List.mem_append_left _ witness⟩

theorem deliveredAppend_output (s : State) (block : Block) (old : OutputHistory s)
    (witness : ∃ view, AuditEvent.commit s.self view block ∈ s.audit) :
    OutputHistory {s with delivered := s.delivered ++ [block]} := by
  constructor
  · exact old.committed
  · intro chosen member
    rcases List.mem_append.mp member with prior | added
    · exact old.delivered chosen prior
    · have same : chosen = block := by simpa using added
      subst chosen
      exact witness

theorem doCommit_output (s : State) (view : Nat) (block : Block) (old : OutputHistory s) :
    OutputHistory (doCommit s view block) := by
  let cleared := clear s view (some block)
  have clearedOK := clear_output s view (some block) old
  let selected := putView cleared {viewAt cleared view with committed := some block}
  let recorded : State := {selected with audit := selected.audit ++ [AuditEvent.commit selected.self view block]}
  have recordedOK : OutputHistory recorded := commitUpdate_output cleared view block clearedOK
  have witness : ∃ number, AuditEvent.commit recorded.self number block ∈ recorded.audit :=
    ⟨view, List.mem_append_right _ (by simp [recorded])⟩
  have deliveredOK := deliveredAppend_output recorded block recordedOK witness
  unfold doCommit
  dsimp only
  split_ifs <;> first
    | exact old
    | exact clearedOK
    | exact output_same_fields _ _ recordedOK rfl rfl rfl rfl
    | exact output_same_fields _ _ deliveredOK rfl rfl rfl rfl

#assert_axioms putView_committed
#assert_axioms putView_output
#assert_axioms append_output
#assert_axioms output_record
#assert_axioms initial_output
#assert_axioms register_output
#assert_axioms broadcast_output
#assert_axioms clear_output
#assert_axioms commitUpdate_output
#assert_axioms deliveredAppend_output
#assert_axioms doCommit_output
macro "output_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [output_record]
    | with_reducible apply register_output
    | with_reducible apply broadcast_output
    | with_reducible apply clear_output
    | with_reducible apply doCommit_output
    | with_reducible apply putView_output
    | solve | simp_all [viewAt_number]
    | split)
macro "output_chain" : tactic => `(tactic| repeat' output_step)

theorem sendCandidate_output (s : State) (view : Nat) (arg : Argument)
    (old : OutputHistory s) : OutputHistory (sendCandidate s view arg) := by
  unfold sendCandidate
  dsimp only
  output_chain

theorem castVote_output (s : State) (view : Nat) (block : Block)
    (old : OutputHistory s) : OutputHistory (castVote s view block) := by
  unfold castVote
  dsimp only
  output_chain

macro "output_action" : tactic => `(tactic|
  first
    | with_reducible apply sendCandidate_output
    | with_reducible apply castVote_output
    | output_step)
macro "output_actions" : tactic => `(tactic| repeat' output_action)

theorem output_fold {α : Type} (action : State → α → State)
    (each : ∀ state item, OutputHistory state → OutputHistory (action state item))
    (items : List α) (state : State) (old : OutputHistory state) :
    OutputHistory (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact old
  | cons item rest ih => exact ih (action state item) (each state item old)

theorem valueRules_output (c : Config) (s : State) (view : Nat) (block : Block)
    (old : OutputHistory s) : OutputHistory (valueRules c s view block) := by
  simp only [valueRules, Id.run, bind, pure]
  output_actions

theorem argumentRules_output (c : Config) (s : State) (view : Nat) (arg : Argument)
    (old : OutputHistory s) : OutputHistory (argumentRules c s view arg) := by
  simp only [argumentRules, Id.run, bind, pure]
  output_actions

theorem progressView_output (c : Config) (s : State) (view : Nat)
    (old : OutputHistory s) : OutputHistory (progressView c s view) := by
  simp only [progressView, Id.run, bind, pure]
  apply output_fold
  · intro state arg prior
    exact argumentRules_output c state view arg prior
  · apply output_fold
    · intro state block prior
      exact valueRules_output c state view block prior
    · exact old

theorem propose_output (s : State) (old : OutputHistory s) :
    OutputHistory (propose s) := by
  unfold propose
  dsimp only
  output_actions

theorem enterView_output (c : Config) (s : State) (view : Nat)
    (old : OutputHistory s) : OutputHistory (enterView c s view) := by
  unfold enterView
  dsimp only
  split
  · apply propose_output
    output_actions
  · output_actions

theorem progressOuter_output (c : Config) (s : State) (old : OutputHistory s) :
    OutputHistory (progressOuter c s) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | with_reducible apply enterView_output
    | output_action

theorem pass_output (c : Config) (s : State) (old : OutputHistory s) :
    OutputHistory (pass c s) := by
  unfold pass
  apply progressOuter_output
  apply output_fold
  · intro state view prior
    exact progressView_output c state view prior
  · exact old

theorem pump_output (c : Config) (fuel : Nat) (s : State) (old : OutputHistory s) :
    OutputHistory (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simpa only [pump, output_record] using old
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_output
      simpa only [output_record] using old
    · apply ih
      apply pass_output
      simpa only [output_record] using old

theorem ingest_output (c : Config) (s : State) (message : Message)
    (old : OutputHistory s) : OutputHistory (ingest c s message) := by
  unfold ingest
  dsimp only
  output_actions

theorem step_output (c : Config) (s : State) (input : Input) (old : OutputHistory s) :
    OutputHistory (step c s input) := by
  unfold step
  dsimp only
  split
  · output_actions
  · apply pump_output
    cases input with
    | delivery message => exact ingest_output c s message old
    | deliveryAt now message =>
      apply ingest_output
      output_actions
    | checked block => dsimp only; output_actions
    | offer payload => dsimp only; output_actions
    | poll => exact old
    | tick now =>
      dsimp only
      repeat' first
        | with_reducible apply pump_output
        | output_action

theorem start_output (c : Config) (self now : Nat) (offers : List Bytes)
    (checked : List Block) : OutputHistory (start c self now offers checked) := by
  unfold start
  split
  · exact output_same_fields _ _ (initial_output self now now [] []) rfl rfl rfl rfl
  · apply pump_output
    apply enterView_output
    exact initial_output self now (now + c.timeout) offers checked

#assert_axioms output_same_fields
#assert_axioms output_record
#assert_axioms append_output
#assert_axioms doCommit_output
#assert_axioms sendCandidate_output
#assert_axioms castVote_output
#assert_axioms output_fold
#assert_axioms start_output
#assert_axioms step_output
end Minidregg.Kernel.GenericSimplexOutputHistory
