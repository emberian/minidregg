import Kernel.GenericSimplexPreparedHistory
import Mathlib.Tactic.FailIfNoProgress

namespace Minidregg.Kernel.GenericSimplexVoteOrigin
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexPreparedHistory
open Minidregg.Kernel.GenericSimplexVAInvariant
set_option autoImplicit false
abbrev OriginEvent := Minidregg.Kernel.GenericSimplex.AuditEvent

def VoteOriginOn (priorEvents : List OriginEvent) : OriginEvent → Prop
  | .send ⟨party, view, .vote, some block⟩ =>
      SafeAt (localTrace priorEvents) priorEvents.length party view block ∨
        .prepare party view block ∈ priorEvents
  | _ => True

def VoteOrigins (events : List OriginEvent) : Prop :=
  ∀ index (within : index < events.length), VoteOriginOn (events.take index) events[index]

def OriginInvariant (s : State) : Prop := HistoryInvariant s ∧ VoteOrigins s.audit

theorem voteOrigins_append (events : List OriginEvent) (event : OriginEvent)
    (old : VoteOrigins events) (fresh : VoteOriginOn events event) :
    VoteOrigins (events ++ [event]) := by
  intro index within
  by_cases previous : index < events.length
  · rw [List.take_append_of_le_length (Nat.le_of_lt previous)]
    simpa only [List.getElem_append_left previous] using old index previous
  · have last : index = events.length := by
      simp only [List.length_append, List.length_singleton] at within
      omega
    subst index
    simpa using fresh

theorem origin_record (s : State) (current deadline now : Nat)
    (checked : List Block) (offers : List Bytes) (outbox : List Message)
    (delivered : List Block) (tip : Block) (needsPoll failed : Bool) :
    OriginInvariant { self := s.self, current := current, deadline := deadline, now := now, views := s.views, checked := checked, offers := offers, outbox := outbox, audit := s.audit, delivered := delivered, committedTip := tip, needsPoll := needsPoll, failed := failed } ↔ OriginInvariant s := by
  simp only [OriginInvariant, history_record]

theorem putView_origin (s : State) (v : View) (old : OriginInvariant s)
    (prepared : v.prepared = (viewAt s v.number).prepared)
    (disabled : v.disabled = (viewAt s v.number).disabled) :
    OriginInvariant (putView s v) := ⟨putView_history s v old.1 prepared disabled, old.2⟩

theorem register_origin (s : State) (m : Message) (old : OriginInvariant s) :
    OriginInvariant (register s m) := ⟨register_history s m old.1, old.2⟩

theorem broadcast_other_origin (s : State) (view : Nat) (kind : Kind) (arg : Argument)
    (old : OriginInvariant s) (notVote : kind ≠ .vote) :
    OriginInvariant (broadcast s view kind arg) := by
  refine ⟨broadcast_history s view kind arg old.1, ?_⟩
  rw [broadcast_audit]
  apply voteOrigins_append _ _ old.2
  cases kind <;> simp_all [VoteOriginOn]

theorem clear_origin (s : State) (view : Nat) (arg : Argument) (old : OriginInvariant s) :
    OriginInvariant (clear s view arg) := by
  refine ⟨clear_history s view arg old.1, ?_⟩
  cases arg with
  | none =>
    simp only [clear]
    split
    · exact old.2
    · exact voteOrigins_append _ _ old.2 (by trivial)
  | some block =>
    simp only [clear]
    split
    · exact voteOrigins_append _ _ old.2 (by trivial)
    · exact old.2

theorem doCommit_origin (s : State) (view : Nat) (block : Block) (old : OriginInvariant s) :
    OriginInvariant (doCommit s view block) := by
  refine ⟨doCommit_history s view block old.1, ?_⟩
  have cleared := (clear_origin s view (some block) old).2
  have appended := voteOrigins_append (clear s view (some block)).audit
    (.commit (clear s view (some block)).self view block) cleared (by trivial)
  unfold doCommit
  dsimp only
  split_ifs <;> first | exact old.2 | exact cleared | exact appended

theorem sendCandidate_origin (s : State) (view : Nat) (arg : Argument) (old : OriginInvariant s) :
    OriginInvariant (sendCandidate s view arg) := by
  refine ⟨sendCandidate_history s view arg old.1, ?_⟩
  unfold sendCandidate
  dsimp only
  split
  · exact old.2
  · rw [broadcast_audit]
    exact voteOrigins_append _ _ old.2 (by trivial)

theorem castVote_origin (s : State) (view : Nat) (block : Block) (old : OriginInvariant s)
    (cause : VoteOriginOn s.audit (.send ⟨s.self, view, .vote, some block⟩)) :
    OriginInvariant (castVote s view block) := by
  refine ⟨castVote_history s view block old.1, ?_⟩
  unfold castVote
  dsimp only
  split
  · exact old.2
  · rw [broadcast_audit]
    exact voteOrigins_append _ _ old.2 cause

theorem castVote_safe_origin (s : State) (block : Block) (old : OriginInvariant s)
    (safe : isSafe s block = true) : OriginInvariant (castVote s s.current block) :=
  castVote_origin s s.current block old (Or.inl (isSafe_safeAt s block old.1 safe))

theorem castVote_prepared_origin (s : State) (view : Nat) (block : Block) (old : OriginInvariant s)
    (prepared : block ∈ (viewAt s view).prepared) : OriginInvariant (castVote s view block) :=
  castVote_origin s view block old (Or.inr (old.1.prepared view block prepared))

macro "origin_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [origin_record]
    | with_reducible apply register_origin
    | (with_reducible apply broadcast_other_origin; rotate_left; solve | assumption | simp)
    | with_reducible apply clear_origin
    | with_reducible apply doCommit_origin
    | with_reducible apply sendCandidate_origin
    | with_reducible apply putView_origin
    | solve | simp_all [viewAt_number]
    | split)
macro "origin_chain" : tactic => `(tactic| repeat' origin_step)

theorem origin_fold {α : Type} (action : State → α → State)
    (each : ∀ state item, OriginInvariant state → OriginInvariant (action state item))
    (items : List α) (state : State) (old : OriginInvariant state) :
    OriginInvariant (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact old
  | cons item rest ih => exact ih _ (each state item old)

theorem valueRules_origin (c : Config) (s : State) (view : Nat) (block : Block)
    (old : OriginInvariant s) : OriginInvariant (valueRules c s view block) := by
  simp only [valueRules, Id.run, bind, pure]
  origin_chain

theorem argumentRules_origin (c : Config) (s : State) (view : Nat) (arg : Argument)
    (old : OriginInvariant s) : OriginInvariant (argumentRules c s view arg) := by
  simp only [argumentRules, Id.run, bind, pure]
  origin_chain

theorem progressView_origin (c : Config) (s : State) (view : Nat) (old : OriginInvariant s) :
    OriginInvariant (progressView c s view) := by
  simp only [progressView, Id.run, bind, pure]
  apply origin_fold
  · intro state arg invariant; exact argumentRules_origin c state view arg invariant
  · apply origin_fold
    · intro state block invariant; exact valueRules_origin c state view block invariant
    · exact old

theorem propose_origin (s : State) (old : OriginInvariant s) : OriginInvariant (propose s) := by
  unfold propose
  dsimp only
  origin_chain

theorem enterView_origin (c : Config) (s : State) (view : Nat) (old : OriginInvariant s) :
    OriginInvariant (enterView c s view) := by
  unfold enterView
  dsimp only
  split
  · apply propose_origin
    origin_chain
  · origin_chain

theorem progressOuter_origin (c : Config) (s : State) (old : OriginInvariant s) :
    OriginInvariant (progressOuter c s) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | with_reducible apply enterView_origin
    | with_reducible apply propose_origin
    | (with_reducible apply castVote_safe_origin; rotate_left; solve | simp_all)
    | (with_reducible apply castVote_prepared_origin; rotate_left; solve | apply List.mem_of_head?; assumption)
    | origin_step

theorem pass_origin (c : Config) (s : State) (old : OriginInvariant s) :
    OriginInvariant (pass c s) := by
  unfold pass
  apply progressOuter_origin
  apply origin_fold
  · intro state view invariant; exact progressView_origin c state view invariant
  · exact old

theorem pump_origin (c : Config) (fuel : Nat) (s : State) (old : OriginInvariant s) :
    OriginInvariant (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simpa only [pump, origin_record] using old
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_origin; simpa only [origin_record] using old
    · apply ih; apply pass_origin; simpa only [origin_record] using old

theorem ingest_origin (c : Config) (s : State) (message : Message) (old : OriginInvariant s) :
    OriginInvariant (ingest c s message) := by
  unfold ingest
  dsimp only
  origin_chain

theorem step_origin (c : Config) (s : State) (input : Input) (old : OriginInvariant s) :
    OriginInvariant (step c s input) := by
  unfold step
  dsimp only
  split
  · origin_chain
  · apply pump_origin
    cases input with
    | delivery message => exact ingest_origin c s message old
    | deliveryAt now message => apply ingest_origin; origin_chain
    | checked block => dsimp only; origin_chain
    | offer payload => dsimp only; origin_chain
    | poll => exact old
    | tick now =>
      dsimp only
      have pumped := pump_origin c c.pumpBudget s old
      origin_chain

theorem initial_origin (self now deadline : Nat) (offers : List Bytes) (checked : List Block) :
    OriginInvariant {self := self, now := now, deadline := deadline, offers := offers, checked := checked} := by
  exact ⟨initial_history self now deadline offers checked, by intro index within; simp at within⟩

theorem start_origin (c : Config) (self now : Nat) (offers : List Bytes) (checked : List Block) :
    OriginInvariant (start c self now offers checked) := by
  unfold start
  split
  · refine ⟨?_, ?_⟩
    · exact history_same_fields _ _ (initial_history self now now [] []) rfl rfl rfl
    · intro index within; simp at within
  · apply pump_origin
    apply enterView_origin
    exact initial_origin self now (now+c.timeout) offers checked

#assert_axioms voteOrigins_append
#assert_axioms clear_origin
#assert_axioms doCommit_origin
#assert_axioms castVote_safe_origin
#assert_axioms castVote_prepared_origin
#assert_axioms valueRules_origin
#assert_axioms argumentRules_origin
#assert_axioms progressOuter_origin
#assert_axioms step_origin
#assert_axioms start_origin
end Minidregg.Kernel.GenericSimplexVoteOrigin
