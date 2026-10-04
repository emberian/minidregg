import Kernel.GenericSimplexCausal
import Mathlib.Tactic.FailIfNoProgress

namespace Minidregg.Kernel.GenericSimplexPositive
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
set_option autoImplicit false

def EventPositive : AuditEvent → Prop
  | .send message => 0 < message.view
  | .prepare _ view _ | .disable _ view | .commit _ view _ => 0 < view
  | .idle => True

def Positive (s : State) : Prop :=
  0 < s.current ∧ (∀ view ∈ s.views, 0 < view.number) ∧
    ∀ event ∈ s.audit, EventPositive event

theorem positive_record (s : State) (deadline now : Nat) (checked : List Block)
    (offers : List Bytes) (outbox : List Message) (delivered : List Block) (tip : Block)
    (needsPoll failed : Bool) :
    Positive {self := s.self, current := s.current, deadline := deadline, now := now, views := s.views, checked := checked, offers := offers, outbox := outbox, audit := s.audit, delivered := delivered, committedTip := tip, needsPoll := needsPoll, failed := failed} ↔ Positive s := Iff.rfl

theorem positive_new_current (s : State) (current deadline : Nat) (old : Positive s)
    (pos : 0 < current) : Positive {s with current := current, deadline := deadline} :=
  ⟨pos, old.2⟩

theorem positive_append (s : State) (event : AuditEvent) (old : Positive s)
    (pos : EventPositive event) : Positive {s with audit := s.audit ++ [event]} := by
  refine ⟨old.1, old.2.1, ?_⟩
  intro other member
  rcases List.mem_append.mp member with previous | added
  · exact old.2.2 other previous
  · have same : other = event := by simpa using added
    simpa only [same] using pos

theorem putView_positive (s : State) (view : View) (old : Positive s)
    (pos : 0 < view.number) : Positive (putView s view) := by
  refine ⟨old.1, ?_, old.2.2⟩
  intro other member
  unfold putView at member
  split at member
  · obtain ⟨prior, inside, same⟩ := List.mem_map.mp member
    split at same
    · subst other; exact pos
    · subst other; exact old.2.1 prior inside
  · rcases List.mem_append.mp member with prior | added
    · exact old.2.1 other prior
    · have same : other = view := by simpa using added
      simpa only [same] using pos

theorem register_positive (s : State) (message : Message) (old : Positive s)
    (pos : 0 < message.view) : Positive (register s message) := by
  unfold register
  apply putView_positive _ _ old
  simpa only [viewAt_number] using pos

theorem broadcast_positive (s : State) (view : Nat) (kind : Kind) (arg : Argument)
    (old : Positive s) (pos : 0 < view) : Positive (broadcast s view kind arg) := by
  have registered := register_positive s ⟨s.self,view,kind,arg⟩ old pos
  exact positive_append _ (.send ⟨s.self,view,kind,arg⟩) registered pos

theorem broadcast_current_positive (s : State) (kind : Kind) (arg : Argument)
    (old : Positive s) : Positive (broadcast s s.current kind arg) :=
  broadcast_positive s s.current kind arg old old.1

theorem clear_positive (s : State) (view : Nat) (arg : Argument)
    (old : Positive s) (pos : 0 < view) : Positive (clear s view arg) := by
  cases arg with
  | none =>
    simp only [clear]
    split
    · exact old
    · apply positive_append
      · apply putView_positive _ _ old; simpa only [viewAt_number] using pos
      · exact pos
  | some block =>
    simp only [clear]
    split
    · apply positive_append
      · apply putView_positive _ _ old; simpa only [viewAt_number] using pos
      · exact pos
    · exact old

theorem doCommit_positive (s : State) (view : Nat) (block : Block)
    (old : Positive s) (pos : 0 < view) : Positive (doCommit s view block) := by
  have cleared := clear_positive s view (some block) old pos
  have recorded := putView_positive (clear s view (some block))
    {viewAt (clear s view (some block)) view with committed := some block} cleared
    (by simpa only [viewAt_number] using pos)
  have appended := positive_append _ (.commit (clear s view (some block)).self view block) recorded pos
  unfold doCommit
  dsimp only
  split_ifs <;> first | exact old | exact cleared | exact appended

theorem castVote_positive (s : State) (view : Nat) (block : Block)
    (old : Positive s) (pos : 0 < view) : Positive (castVote s view block) := by
  unfold castVote
  dsimp only
  split
  · exact old
  · apply broadcast_positive
    · apply putView_positive _ _ old; simpa only [viewAt_number] using pos
    · exact pos

theorem castVote_current_positive (s : State) (block : Block) (old : Positive s) :
    Positive (castVote s s.current block) := castVote_positive s s.current block old old.1

theorem sendCandidate_positive (s : State) (view : Nat) (arg : Argument)
    (old : Positive s) (pos : 0 < view) : Positive (sendCandidate s view arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact old
  · apply broadcast_positive
    · apply putView_positive _ _ old; simpa only [viewAt_number] using pos
    · exact pos

theorem sendCandidate_current_positive (s : State) (arg : Argument) (old : Positive s) :
    Positive (sendCandidate s s.current arg) := sendCandidate_positive s s.current arg old old.1

@[simp] theorem putView_current (s : State) (view : View) :
    (putView s view).current = s.current := rfl
@[simp] theorem broadcast_current (s : State) (view : Nat) (kind : Kind) (arg : Argument) :
    (broadcast s view kind arg).current = s.current := rfl

macro "positive_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [positive_record]
    | with_reducible apply broadcast_current_positive
    | (with_reducible apply broadcast_positive; rotate_left; assumption)
    | (with_reducible apply clear_positive; rotate_left; assumption)
    | (with_reducible apply doCommit_positive; rotate_left; assumption)
    | with_reducible apply castVote_current_positive
    | with_reducible apply sendCandidate_current_positive
    | (with_reducible apply sendCandidate_positive; rotate_left; assumption)
    | with_reducible apply putView_positive
    | solve | simp_all [viewAt_number, putView_current, broadcast_current] <;> omega
    | split)
macro "positive_chain" : tactic => `(tactic| repeat' positive_step)

theorem positive_fold {α : Type} (action : State → α → State)
    (each : ∀ state item, Positive state → Positive (action state item))
    (items : List α) (state : State) (old : Positive state) :
    Positive (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact old
  | cons item rest ih => exact ih _ (each state item old)

theorem valueRules_positive (c : Config) (s : State) (view : Nat) (block : Block)
    (old : Positive s) (pos : 0 < view) : Positive (valueRules c s view block) := by
  simp only [valueRules, Id.run, bind, pure]
  positive_chain

theorem argumentRules_positive (c : Config) (s : State) (view : Nat) (arg : Argument)
    (old : Positive s) (pos : 0 < view) : Positive (argumentRules c s view arg) := by
  simp only [argumentRules, Id.run, bind, pure]
  positive_chain

theorem progressView_positive (c : Config) (s : State) (view : Nat)
    (old : Positive s) (pos : 0 < view) : Positive (progressView c s view) := by
  simp only [progressView, Id.run, bind, pure]
  apply positive_fold
  · intro state arg invariant; exact argumentRules_positive c state view arg invariant pos
  · apply positive_fold
    · intro state block invariant; exact valueRules_positive c state view block invariant pos
    · exact old

theorem propose_positive (s : State) (old : Positive s) : Positive (propose s) := by
  unfold propose
  dsimp only
  have currentPos := old.1
  positive_chain

theorem enterView_positive (c : Config) (s : State) (view : Nat)
    (old : Positive s) (pos : 0 < view) : Positive (enterView c s view) := by
  unfold enterView
  dsimp only
  have updated := positive_new_current s view (s.now+c.timeout) old pos
  split
  · apply propose_positive
    positive_chain
  · positive_chain

theorem enterNext_positive (c : Config) (s : State) (old : Positive s) :
    Positive (enterView c s (s.current+1)) := enterView_positive c s _ old (by omega)

theorem progressOuter_positive (c : Config) (s : State) (old : Positive s) :
    Positive (progressOuter c s) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | with_reducible apply enterNext_positive
    | with_reducible apply propose_positive
    | positive_step

theorem progressViews_positive (c : Config) (numbers : List Nat) (s : State)
    (old : Positive s) (pos : ∀ view ∈ numbers, 0 < view) :
    Positive (numbers.foldl (fun state view => progressView c state view) s) := by
  induction numbers generalizing s with
  | nil => exact old
  | cons number rest ih =>
    apply ih
    · exact progressView_positive c s number old (pos number (by simp))
    · intro view member; exact pos view (by simp [member])

theorem pass_positive (c : Config) (s : State) (old : Positive s) : Positive (pass c s) := by
  unfold pass
  apply progressOuter_positive
  apply progressViews_positive _ _ _ old
  intro view member
  obtain ⟨stored, inside, number⟩ := List.mem_map.mp (List.mem_eraseDups.mp member)
  simpa only [← number] using old.2.1 stored inside

theorem pump_positive (c : Config) (fuel : Nat) (s : State) (old : Positive s) :
    Positive (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simpa only [pump, positive_record] using old
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_positive; simpa only [positive_record] using old
    · apply ih; apply pass_positive; simpa only [positive_record] using old

theorem ingest_positive (c : Config) (s : State) (message : Message) (old : Positive s) :
    Positive (ingest c s message) := by
  unfold ingest
  split
  · exact old
  · rename_i admitted
    have pos : 0 < message.view := by
      have nonzero : message.view ≠ 0 := by
        intro zero
        simp [zero] at admitted
      omega
    dsimp only
    repeat' first
      | with_reducible exact register_positive s message old pos
      | positive_step

theorem step_positive (c : Config) (s : State) (input : Input) (old : Positive s) :
    Positive (step c s input) := by
  unfold step
  dsimp only
  split
  · positive_chain
  · apply pump_positive
    cases input with
    | delivery message => exact ingest_positive c s message old
    | deliveryAt now message => apply ingest_positive; positive_chain
    | checked block => dsimp only; positive_chain
    | offer payload => dsimp only; positive_chain
    | poll => exact old
    | tick now =>
      dsimp only
      have pumped := pump_positive c c.pumpBudget s old
      have currentPos := pumped.1
      positive_chain

theorem start_positive (c : Config) (self now : Nat) (offers : List Bytes) (checked : List Block) :
    Positive (start c self now offers checked) := by
  unfold start
  split
  · exact ⟨by change 0 < 1; decide, by simp, by simp⟩
  · apply pump_positive
    apply enterView_positive
    · exact ⟨by change 0 < 1; decide, by simp, by simp⟩
    · decide

#assert_axioms register_positive
#assert_axioms valueRules_positive
#assert_axioms argumentRules_positive
#assert_axioms progressOuter_positive
#assert_axioms pass_positive
#assert_axioms step_positive
#assert_axioms start_positive
end Minidregg.Kernel.GenericSimplexPositive
