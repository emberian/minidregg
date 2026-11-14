import Kernel.GenericSimplexCausal
import Kernel.GenericSimplexErasure
import Mathlib.Tactic.FailIfNoProgress

/-! What one `step` adds, read against the floor it started from.

Three local facts about the specification's `step`, for any state. None is a consensus
fact. The running replica (`GenericSimplexRelative`) forgets the audit and every view below
its floor between inputs, so its proof needs them as statements about one step:

* `step_fresh`: every event a step appends to the audit is for a view above the floor the
  step started from, every SEND it appends is in the outbox it leaves, and every message it
  adds to the outbox is a SEND in the audit (the repeated CANDIDATE(⊥) of a tick is the one
  recorded earlier).
* `step_relay`: what a step adds to `relay` is the floor evidence it held (for a view at or
  below the floor) or one of its own received messages in a view above the floor.
* `step_evident`: a step that does not raise the floor keeps `floorEvidence`; one that
  raises it leaves evidence drawn from the received messages of the new floor view. -/
namespace Minidregg.Kernel.GenericSimplexFresh
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexErasure (absorb step_eq timeoutRule timeoutWith serveViews_eq ownFrom)
set_option autoImplicit false

def EventAbove (floor : Nat) : AuditEvent → Prop
  | .send message => floor < message.view
  | .prepare _ view _ | .disable _ view | .commit _ view _ => floor < view
  | .idle => True

/-- Against a floor, an audit and an outbox fixed beforehand: the floor has not dropped,
the current view is above it, an audit event is an old one or is above the floor (and, if a
SEND, in the outbox), and an outbox message is an old one or a SEND of the audit. -/
def Fresh (floor : Nat) (audit : List AuditEvent) (outbox : List Message)
    (relay : List (Nat × Message)) (s : State) : Prop :=
  floor ≤ s.lastCommitted ∧ floor < s.current ∧ s.relay = relay ∧
  (∀ event ∈ s.audit, event ∈ audit ∨
    (EventAbove floor event ∧ ∀ m, event = .send m → m ∈ s.outbox)) ∧
  (∀ m ∈ s.outbox, m ∈ outbox ∨ .send m ∈ s.audit)

variable {floor : Nat} {audit : List AuditEvent} {outbox : List Message}
  {relay : List (Nat × Message)}

@[simp] theorem fresh_record (s : State) (self deadline now : Nat) (views : List View)
    (checked : List Block) (offers : List Bytes) (delivered : List Block) (tip : Block)
    (needsPoll failed : Bool) (floorEvidence : List Message) (served : List Nat)
    (ahead : List (Nat × Nat)) :
    Fresh floor audit outbox relay { self := self, current := s.current, deadline := deadline, now := now, views := views, checked := checked, offers := offers, outbox := s.outbox, audit := s.audit, delivered := delivered, committedTip := tip, needsPoll := needsPoll, failed := failed, lastCommitted := s.lastCommitted, floorEvidence := floorEvidence, served := served, relay := s.relay, ahead := ahead } ↔
      Fresh floor audit outbox relay s := Iff.rfl

theorem putView_fresh (s : State) (view : View) :
    Fresh floor audit outbox relay (putView s view) ↔ Fresh floor audit outbox relay s := Iff.rfl

theorem fresh_new_current (s : State) (current deadline : Nat)
    (old : Fresh floor audit outbox relay s) (above : floor < current) :
    Fresh floor audit outbox relay { s with current := current, deadline := deadline } :=
  ⟨old.1, above, old.2.2⟩

theorem fresh_output (s : State) (event : AuditEvent) (old : Fresh floor audit outbox relay s)
    (above : EventAbove floor event) (output : ∀ m, event ≠ .send m) :
    Fresh floor audit outbox relay { s with audit := s.audit ++ [event] } := by
  refine ⟨old.1, old.2.1, old.2.2.1, ?_, ?_⟩
  · intro other member
    rcases List.mem_append.mp member with previous | added
    · exact old.2.2.2.1 other previous
    · have same : other = event := by simpa using added
      subst other
      exact Or.inr ⟨above, fun m sent => absurd sent (output m)⟩
  · intro m member
    exact (old.2.2.2.2 m member).imp id (fun sent => List.mem_append.mpr (Or.inl sent))

theorem broadcast_fresh (s : State) (view : Nat) (kind : Kind) (arg : Argument)
    (old : Fresh floor audit outbox relay s) (above : floor < view) :
    Fresh floor audit outbox relay (broadcast s view kind arg) := by
  refine ⟨old.1, old.2.1, old.2.2.1, ?_, ?_⟩
  · intro other member
    rcases List.mem_append.mp member with previous | added
    · exact (old.2.2.2.1 other previous).imp id (fun fresh =>
        ⟨fresh.1, fun m sent => List.mem_append.mpr (Or.inl (fresh.2 m sent))⟩)
    · have same : other = .send ⟨s.self, view, kind, arg⟩ := by simpa using added
      subst other
      refine Or.inr ⟨above, fun m sent => ?_⟩
      cases sent
      exact List.mem_append.mpr (Or.inr (by simp))
  · intro m member
    rcases List.mem_append.mp member with previous | added
    · exact (old.2.2.2.2 m previous).imp id (fun sent => List.mem_append.mpr (Or.inl sent))
    · have same : m = ⟨s.self, view, kind, arg⟩ := by simpa using added
      subst m
      exact Or.inr (List.mem_append.mpr (Or.inr (by simp)))

theorem broadcast_current_fresh (s : State) (kind : Kind) (arg : Argument)
    (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox relay (broadcast s s.current kind arg) :=
  broadcast_fresh s s.current kind arg old old.2.1

theorem clear_fresh (s : State) (view : Nat) (arg : Argument)
    (old : Fresh floor audit outbox relay s) (above : floor < view) :
    Fresh floor audit outbox relay (clear s view arg) := by
  cases arg with
  | none =>
    simp only [clear]
    split
    · exact old
    · exact fresh_output (putView s _) (.disable s.self view) old above (by intro m h; cases h)
  | some block =>
    simp only [clear]
    split
    · exact fresh_output (putView s _) (.prepare s.self view block) old above (by intro m h; cases h)
    · exact old

theorem doCommit_fresh (s : State) (view : Nat) (block : Block)
    (old : Fresh floor audit outbox relay s) (above : floor < view) :
    Fresh floor audit outbox relay (doCommit s view block) := by
  have cleared := clear_fresh s view (some block) old above
  have appended := fresh_output
    (putView (clear s view (some block))
      { viewAt (clear s view (some block)) view with committed := some block })
    (.commit (clear s view (some block)).self view block) cleared above (by intro m h; cases h)
  unfold doCommit
  dsimp only
  split_ifs <;> first | exact old | exact cleared | exact appended

theorem commitAt_fresh (s : State) (view : Nat) (block : Block)
    (old : Fresh floor audit outbox relay s) (above : floor < view) :
    Fresh floor audit outbox relay (commitAt s view block) := by
  have committed := doCommit_fresh s view block old above
  unfold commitAt
  rcases raiseFloor_cases (doCommit s view block) view block with same | ⟨_, same⟩ <;> rw [same]
  · exact committed
  · exact ⟨Nat.le_of_lt above, committed.2⟩

theorem castVote_fresh (s : State) (view : Nat) (block : Block)
    (old : Fresh floor audit outbox relay s) (above : floor < view) :
    Fresh floor audit outbox relay (castVote s view block) := by
  unfold castVote
  dsimp only
  split
  · exact old
  · exact broadcast_fresh (putView s _) view .vote (some block) old above

theorem castVote_current_fresh (s : State) (block : Block)
    (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox relay (castVote s s.current block) :=
  castVote_fresh s s.current block old old.2.1

theorem sendCandidate_fresh (s : State) (view : Nat) (arg : Argument)
    (old : Fresh floor audit outbox relay s) (above : floor < view) :
    Fresh floor audit outbox relay (sendCandidate s view arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact old
  · exact broadcast_fresh (putView s _) view .candidate arg old above

macro "fresh_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [fresh_record, putView_fresh]
    | with_reducible apply broadcast_current_fresh
    | (with_reducible apply broadcast_fresh; rotate_left; assumption)
    | (with_reducible apply clear_fresh; rotate_left; assumption)
    | (with_reducible apply commitAt_fresh; rotate_left; assumption)
    | with_reducible apply castVote_current_fresh
    | (with_reducible apply sendCandidate_fresh; rotate_left; assumption)
    | split)
macro "fresh_chain" : tactic => `(tactic| repeat' fresh_step)

theorem fresh_fold {α : Type} (action : State → α → State)
    (each : ∀ state item, Fresh floor audit outbox relay state →
      Fresh floor audit outbox relay (action state item))
    (items : List α) (state : State) (old : Fresh floor audit outbox relay state) :
    Fresh floor audit outbox relay (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact old
  | cons item rest ih => exact ih _ (each state item old)

theorem valueRules_fresh (c : Config) (s : State) (view : Nat) (block : Block)
    (old : Fresh floor audit outbox relay s) (above : floor < view) :
    Fresh floor audit outbox relay (valueRules c s view block) := by
  simp only [valueRules, Id.run, pure]
  fresh_chain

theorem argumentRules_fresh (c : Config) (s : State) (view : Nat) (arg : Argument)
    (old : Fresh floor audit outbox relay s) (above : floor < view) :
    Fresh floor audit outbox relay (argumentRules c s view arg) := by
  simp only [argumentRules, Id.run, pure]
  fresh_chain

theorem progressView_fresh (c : Config) (s : State) (view : Nat)
    (old : Fresh floor audit outbox relay s) (above : floor < view) :
    Fresh floor audit outbox relay (progressView c s view) := by
  simp only [progressView, Id.run, pure]
  apply fresh_fold
  · intro state arg invariant; exact argumentRules_fresh c state view arg invariant above
  · apply fresh_fold
    · intro state block invariant; exact valueRules_fresh c state view block invariant above
    · exact old

theorem propose_fresh (s : State) (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox relay (propose s) := by
  unfold propose
  dsimp only
  fresh_chain

theorem enterView_fresh (c : Config) (s : State) (view : Nat)
    (old : Fresh floor audit outbox relay s) (above : floor < view) :
    Fresh floor audit outbox relay (enterView c s view) := by
  unfold enterView
  dsimp only
  have updated := fresh_new_current s view (s.now + viewTimeout c s view) old above
  split
  · apply propose_fresh
    fresh_chain
  · fresh_chain

theorem floorJump_fresh (c : Config) (s : State) (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox relay (floorJump c s) := by
  unfold floorJump
  split
  · exact enterView_fresh c s _ old (by have := old.1; omega)
  · exact old

theorem enterNext_fresh (c : Config) (s : State) (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox relay (enterView c s (s.current + 1)) :=
  enterView_fresh c s _ old (by have := old.2.1; omega)

theorem progressOuter_fresh (c : Config) (s : State) (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox relay (progressOuter c s) := by
  simp only [progressOuter, Id.run, pure]
  repeat' first
    | with_reducible apply enterNext_fresh
    | with_reducible apply propose_fresh
    | fresh_step

theorem pass_fresh (c : Config) (s : State) (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox relay (pass c s) := by
  unfold pass
  apply progressOuter_fresh
  apply floorJump_fresh
  have numbers : ∀ (numbers : List Nat) (state : State), Fresh floor audit outbox relay state →
      (∀ view ∈ numbers, floor < view) →
      Fresh floor audit outbox relay (numbers.foldl (fun state view => progressView c state view) state) := by
    intro numbers
    induction numbers with
    | nil => intro state invariant _; exact invariant
    | cons number rest ih =>
      intro state invariant above
      exact ih _ (progressView_fresh c state number invariant (above number (by simp)))
        (fun view member => above view (by simp [member]))
  apply numbers _ _ old
  intro view member
  obtain ⟨stored, _, number⟩ := List.mem_filterMap.mp member
  split at number
  · rename_i live
    have same : stored.number = view := by simpa using number
    have := old.1
    omega
  · cases number

theorem pump_fresh (c : Config) (fuel : Nat) (s : State) (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox relay (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simpa only [pump, fresh_record] using old
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_fresh; simpa only [fresh_record] using old
    · apply ih; apply pass_fresh; simpa only [fresh_record] using old

theorem fresh_own (s : State) (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox s.relay s := ⟨old.1, old.2.1, rfl, old.2.2.2⟩

/-- The relay is written by `ingest` alone. -/
theorem fresh_relay (s : State) (other : List (Nat × Message))
    (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox other { s with relay := other } :=
  ⟨old.1, old.2.1, rfl, old.2.2.2⟩

theorem ingest_fresh (c : Config) (s : State) (message : Message)
    (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox (ingest c s message).relay (ingest c s message) := by
  have here : Fresh floor audit outbox s.relay s := ⟨old.1, old.2.1, rfl, old.2.2.2⟩
  unfold ingest serveFloor noteAhead serveViews register
  dsimp only
  repeat' first
    | exact here
    | exact fresh_relay s _ old
    | split

/-- The repeated CANDIDATE(⊥) of a tick is one already in the audit. -/
theorem fresh_repeat (s : State) (m : Message) (old : Fresh floor audit outbox relay s)
    (sent : .send m ∈ s.audit) :
    Fresh floor audit outbox relay { s with outbox := s.outbox ++ [m] } := by
  refine ⟨old.1, old.2.1, old.2.2.1, ?_, ?_⟩
  · intro event member
    exact (old.2.2.2.1 event member).imp id (fun fresh =>
      ⟨fresh.1, fun x same => List.mem_append.mpr (Or.inl (fresh.2 x same))⟩)
  · intro x member
    rcases List.mem_append.mp member with previous | added
    · exact old.2.2.2.2 x previous
    · have same : x = m := by simpa using added
      subst x
      exact Or.inr sent

theorem tick_fresh (c : Config) (s : State) (now : Nat) (causal : CausalInvariant s)
    (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox relay (absorb c s (.tick now)) := by
  have first := pump_fresh c c.pumpBudget s old
  have recorded := (pump_causal c c.pumpBudget s causal).candidateRecorded
  unfold absorb timeoutRule timeoutWith
  dsimp only
  split
  · exact first
  · split
    · split
      · exact sendCandidate_fresh _ _ _ first first.2.1
      · split
        · rename_i again
          exact fresh_repeat _ _ first
            ((recorded (pump c c.pumpBudget s).current none).mp (List.contains_iff_mem.mp again))
        · exact first
    · exact first

theorem absorb_fresh (c : Config) (s : State) (input : Input) (causal : CausalInvariant s)
    (old : Fresh floor audit outbox relay s) :
    Fresh floor audit outbox (absorb c s input).relay (absorb c s input) := by
  have here := fresh_own s old
  cases input with
  | delivery message => exact ingest_fresh c s message here
  | deliveryAt now message => exact ingest_fresh c { s with now := max s.now now } message here
  | checked block => exact here
  | offer payload => exact here
  | poll => exact here
  | tick now => exact fresh_own _ (tick_fresh c s now causal here)

/-- **What one step adds.** From a state whose current view is above its floor: the floor
does not drop; every audit event is one the state already had or is for a view above the
floor it started from, and then, if a SEND, in the outbox the step leaves; every outbox
message is one the state already had or a SEND of the audit. -/
theorem step_fresh (c : Config) (s : State) (input : Input) (causal : CausalInvariant s)
    (live : s.lastCommitted < s.current) :
    s.lastCommitted ≤ (step c s input).lastCommitted ∧
    (∀ event ∈ (step c s input).audit, event ∈ s.audit ∨
      (EventAbove s.lastCommitted event ∧ ∀ m, event = .send m → m ∈ (step c s input).outbox)) ∧
    (∀ m ∈ (step c s input).outbox, m ∈ s.outbox ∨ .send m ∈ (step c s input).audit) := by
  rw [step_eq]
  split
  · exact ⟨Nat.le_refl _, fun event member => Or.inl member, fun m member => Or.inl member⟩
  · have result := pump_fresh c c.pumpBudget _ (absorb_fresh (floor := s.lastCommitted)
      (audit := s.audit) (outbox := s.outbox) (relay := s.relay) c s input causal
      ⟨Nat.le_refl _, live, rfl, fun event member => Or.inl member, fun m member => Or.inl member⟩)
    exact ⟨result.1, result.2.2.2⟩

/-- What `ingest` adds to the relay: the floor evidence, or the replica's own received
messages in views above the floor. -/
theorem ingest_relay (c : Config) (s : State) (message : Message) :
    ∀ x ∈ (ingest c s message).relay, x ∈ s.relay ∨ x.2 ∈ s.floorEvidence ∨
      (x.2.sender = s.self ∧ ∃ number, s.lastCommitted < number ∧
        x.2 ∈ (viewAt s number).received) := by
  intro x member
  unfold ingest at member
  dsimp only at member
  split at member
  · exact Or.inl member
  · split at member
    · split at member
      · unfold serveFloor at member
        split at member
        · exact Or.inl member
        · rcases List.mem_append.mp member with old | new
          · exact Or.inl old
          · obtain ⟨m, inside, rfl⟩ := List.mem_map.mp new
            exact Or.inr (Or.inl inside)
      · exact Or.inl member
    · rename_i above
      split at member
      · unfold noteAhead at member
        split at member <;> exact Or.inl member
      · split at member
        · exact Or.inl member
        · split at member
          · split at member
            · exact Or.inl member
            · split at member <;> exact Or.inl member
          · split at member
            · rw [serveViews_eq] at member
              split at member
              · exact Or.inl member
              · rcases List.mem_append.mp member with old | new
                · exact Or.inl old
                · obtain ⟨offset, _, inside⟩ := List.mem_flatMap.mp new
                  obtain ⟨m, kept, rfl⟩ := List.mem_map.mp inside
                  have own := List.mem_filter.mp kept
                  exact Or.inr (Or.inr ⟨beq_iff_eq.mp own.2, message.view + offset, by omega, own.1⟩)
            · split at member <;> exact Or.inl member

/-- **What one step adds to the relay.** -/
theorem step_relay (c : Config) (s : State) (input : Input) (causal : CausalInvariant s)
    (live : s.lastCommitted < s.current) :
    ∀ x ∈ (step c s input).relay, x ∈ s.relay ∨ x.2 ∈ s.floorEvidence ∨
      (x.2.sender = s.self ∧ ∃ number, s.lastCommitted < number ∧
        x.2 ∈ (viewAt s number).received) := by
  have start : Fresh s.lastCommitted s.audit s.outbox s.relay s :=
    ⟨Nat.le_refl _, live, rfl, fun event member => Or.inl member, fun m member => Or.inl member⟩
  rw [step_eq]
  split
  · intro x member; exact Or.inl member
  · rw [(pump_fresh c c.pumpBudget _ (absorb_fresh c s input causal start)).2.2.1]
    cases input with
    | delivery message => exact ingest_relay c s message
    | deliveryAt now message => exact ingest_relay c { s with now := max s.now now } message
    | checked block => intro x member; exact Or.inl member
    | offer payload => intro x member; exact Or.inl member
    | poll => intro x member; exact Or.inl member
    | tick now =>
      rw [(tick_fresh c s now causal start).2.2.1]
      intro x member; exact Or.inl member

/-! ## The floor evidence -/

/-- Against a floor and its evidence fixed beforehand: the floor has not moved and the
evidence is the same, or the floor is higher and the evidence is among the received
messages of the floor view. -/
def Evident (floor : Nat) (evidence : List Message) (s : State) : Prop :=
  (s.lastCommitted = floor ∧ s.floorEvidence = evidence) ∨
  (floor < s.lastCommitted ∧ ∀ m ∈ s.floorEvidence, m ∈ (viewAt s s.lastCommitted).received)

variable {evidence : List Message}

@[simp] theorem evident_record (s : State) (self current deadline now : Nat)
    (checked : List Block) (offers : List Bytes) (sent : List Message) (events : List AuditEvent)
    (delivered : List Block) (tip : Block) (needsPoll failed : Bool) (served : List Nat)
    (owed : List (Nat × Message)) (ahead : List (Nat × Nat)) :
    Evident floor evidence { self := self, current := current, deadline := deadline, now := now, views := s.views, checked := checked, offers := offers, outbox := sent, audit := events, delivered := delivered, committedTip := tip, needsPoll := needsPoll, failed := failed, lastCommitted := s.lastCommitted, floorEvidence := s.floorEvidence, served := served, relay := owed, ahead := ahead } ↔
      Evident floor evidence s := Iff.rfl

theorem putView_evident (s : State) (view : View) (number : Nat)
    (old : Evident floor evidence s)
    (sameNumber : view.number = (viewAt s number).number)
    (keeps : ∀ m ∈ (viewAt s number).received, m ∈ view.received) :
    Evident floor evidence (putView s view) := by
  rcases old with same | ⟨raised, inside⟩
  · exact Or.inl same
  · refine Or.inr ⟨raised, fun m member => ?_⟩
    show m ∈ (viewAt (putView s view) s.lastCommitted).received
    have named : view.number = number := sameNumber.trans (viewAt_number s number)
    by_cases here : s.lastCommitted = view.number
    · rw [here, viewAt_put_same]
      exact keeps m (by rw [← named, ← here]; exact inside m member)
    · rw [viewAt_put_other s view _ here]
      exact inside m member

theorem putView_copied_evident (s : State) (view : View) (number : Nat)
    (old : Evident floor evidence s)
    (sameNumber : view.number = (viewAt s number).number)
    (sameReceived : view.received = (viewAt s number).received) :
    Evident floor evidence (putView s view) :=
  putView_evident s view number old sameNumber (fun m member => sameReceived ▸ member)

theorem register_evident (s : State) (message : Message) (old : Evident floor evidence s) :
    Evident floor evidence (register s message) := by
  unfold register
  refine putView_evident s _ message.view old rfl ?_
  intro m member
  show m ∈ addUnique (viewAt s message.view).received message
  unfold addUnique
  split
  · exact member
  · exact List.mem_append.mpr (Or.inl member)

theorem broadcast_evident (s : State) (view : Nat) (kind : Kind) (arg : Argument)
    (old : Evident floor evidence s) : Evident floor evidence (broadcast s view kind arg) :=
  register_evident s ⟨s.self, view, kind, arg⟩ old

theorem clear_evident (s : State) (view : Nat) (arg : Argument)
    (old : Evident floor evidence s) : Evident floor evidence (clear s view arg) := by
  cases arg with
  | none =>
    simp only [clear]
    split
    · exact old
    · exact putView_copied_evident s _ view old rfl rfl
  | some block =>
    simp only [clear]
    split
    · exact putView_copied_evident s _ view old rfl rfl
    · exact old

theorem doCommit_evident (s : State) (view : Nat) (block : Block)
    (old : Evident floor evidence s) : Evident floor evidence (doCommit s view block) := by
  have cleared := clear_evident s view (some block) old
  have recorded : Evident floor evidence (putView (clear s view (some block))
      { viewAt (clear s view (some block)) view with committed := some block }) :=
    putView_copied_evident _ _ view cleared rfl rfl
  unfold doCommit
  dsimp only
  split_ifs <;> first | exact old | exact cleared | exact recorded

theorem commitAt_evident (s : State) (view : Nat) (block : Block)
    (old : Evident floor evidence s) : Evident floor evidence (commitAt s view block) := by
  have committed := doCommit_evident s view block old
  unfold commitAt raiseFloor
  dsimp only
  split
  · rename_i raise
    rw [Bool.and_eq_true, decide_eq_true_eq] at raise
    refine Or.inr ⟨(show floor < view from ?_), fun m member => (List.mem_filter.mp member).1⟩
    rcases committed with same | higher
    · have := same.1; omega
    · have := higher.1; omega
  · exact committed

theorem castVote_evident (s : State) (view : Nat) (block : Block)
    (old : Evident floor evidence s) : Evident floor evidence (castVote s view block) := by
  unfold castVote
  dsimp only
  split
  · exact old
  · exact broadcast_evident _ view .vote (some block) (putView_copied_evident s _ view old rfl rfl)

theorem sendCandidate_evident (s : State) (view : Nat) (arg : Argument)
    (old : Evident floor evidence s) : Evident floor evidence (sendCandidate s view arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact old
  · exact broadcast_evident _ view .candidate arg (putView_copied_evident s _ view old rfl rfl)

macro "evident_step" : tactic => `(tactic|
  first
    | with_reducible assumption
    | fail_if_no_progress simp only [evident_record]
    | split
    | with_reducible apply broadcast_evident
    | with_reducible apply clear_evident
    | with_reducible apply commitAt_evident
    | with_reducible apply castVote_evident
    | with_reducible apply sendCandidate_evident
    | (with_reducible apply putView_copied_evident _ _ <;> try rfl))
macro "evident_chain" : tactic => `(tactic| repeat' evident_step)

theorem evident_fold {α : Type} (action : State → α → State)
    (each : ∀ state item, Evident floor evidence state → Evident floor evidence (action state item))
    (items : List α) (state : State) (old : Evident floor evidence state) :
    Evident floor evidence (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact old
  | cons item rest ih => exact ih _ (each state item old)

theorem valueRules_evident (c : Config) (s : State) (view : Nat) (block : Block)
    (old : Evident floor evidence s) : Evident floor evidence (valueRules c s view block) := by
  simp only [valueRules, Id.run, pure]
  evident_chain

theorem argumentRules_evident (c : Config) (s : State) (view : Nat) (arg : Argument)
    (old : Evident floor evidence s) : Evident floor evidence (argumentRules c s view arg) := by
  simp only [argumentRules, Id.run, pure]
  evident_chain

theorem progressView_evident (c : Config) (s : State) (view : Nat)
    (old : Evident floor evidence s) : Evident floor evidence (progressView c s view) := by
  simp only [progressView, Id.run, pure]
  apply evident_fold
  · intro state arg invariant; exact argumentRules_evident c state view arg invariant
  · apply evident_fold
    · intro state block invariant; exact valueRules_evident c state view block invariant
    · exact old

theorem propose_evident (s : State) (old : Evident floor evidence s) :
    Evident floor evidence (propose s) := by
  unfold propose
  dsimp only
  evident_chain

theorem enterView_evident (c : Config) (s : State) (view : Nat)
    (old : Evident floor evidence s) : Evident floor evidence (enterView c s view) := by
  unfold enterView
  dsimp only
  have entered : Evident floor evidence (putView
      { s with current := view, deadline := s.now + viewTimeout c s view }
      (viewAt { s with current := view, deadline := s.now + viewTimeout c s view } view)) :=
    putView_copied_evident _ _ view old rfl rfl
  split
  · exact propose_evident _ entered
  · exact entered

theorem floorJump_evident (c : Config) (s : State) (old : Evident floor evidence s) :
    Evident floor evidence (floorJump c s) := by
  unfold floorJump
  split
  · exact enterView_evident c s _ old
  · exact old

theorem progressOuter_evident (c : Config) (s : State) (old : Evident floor evidence s) :
    Evident floor evidence (progressOuter c s) := by
  simp only [progressOuter, Id.run, pure]
  repeat' first
    | with_reducible apply enterView_evident
    | with_reducible apply propose_evident
    | evident_step

theorem pass_evident (c : Config) (s : State) (old : Evident floor evidence s) :
    Evident floor evidence (pass c s) := by
  unfold pass
  apply progressOuter_evident
  apply floorJump_evident
  apply evident_fold
  · intro state view invariant; exact progressView_evident c state view invariant
  · exact old

theorem pump_evident (c : Config) (fuel : Nat) (s : State) (old : Evident floor evidence s) :
    Evident floor evidence (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simpa only [pump, evident_record] using old
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_evident; simpa only [evident_record] using old
    · apply ih; apply pass_evident; simpa only [evident_record] using old

theorem ingest_evident (c : Config) (s : State) (message : Message)
    (old : Evident floor evidence s) : Evident floor evidence (ingest c s message) := by
  unfold ingest serveFloor noteAhead serveViews
  dsimp only
  repeat' first
    | exact register_evident s message old
    | evident_step

/-- **What one step does to the floor evidence.** If the floor is where it was, the
evidence is what it was. If the floor rose, the evidence is among the received messages of
the new floor view. -/
theorem step_evident (c : Config) (s : State) (input : Input) :
    Evident s.lastCommitted s.floorEvidence (step c s input) := by
  have old : Evident s.lastCommitted s.floorEvidence s := Or.inl ⟨rfl, rfl⟩
  unfold step
  dsimp only
  split
  · exact old
  · apply pump_evident
    cases input with
    | delivery message => exact ingest_evident c s message old
    | deliveryAt now message => exact ingest_evident c { s with now := max s.now now } message old
    | checked block => exact old
    | offer payload => exact old
    | poll => exact old
    | tick now =>
      dsimp only
      have pumped := pump_evident c c.pumpBudget s old
      evident_chain

#assert_axioms step_fresh
#assert_axioms step_relay
#assert_axioms step_evident

end Minidregg.Kernel.GenericSimplexFresh
