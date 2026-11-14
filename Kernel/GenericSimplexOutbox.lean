import Kernel.GenericSimplexFloor

/-! The outbox only grows within a step.

`Kept outbox s`: every message of an outbox fixed beforehand is still in `s.outbox`. No rule
removes a message from the outbox (the driver drains it between inputs), so `step` keeps
it (`step_kept`). A run of several steps before one drain therefore loses no SEND. -/
namespace Minidregg.Kernel.GenericSimplexOutbox
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
set_option autoImplicit false

def Kept (outbox : List Message) (s : State) : Prop := ∀ m ∈ outbox, m ∈ s.outbox

variable {outbox : List Message}

theorem kept_of_same (a b : State) (old : Kept outbox a) (same : b.outbox = a.outbox) :
    Kept outbox b := fun m member => same ▸ old m member

@[simp] theorem kept_record (s : State) (self current deadline now : Nat) (views : List View)
    (checked : List Block) (offers : List Bytes)
    (audit : List AuditEvent) (delivered : List Block) (tip : Block) (needsPoll failed : Bool)
    (lastCommitted : Nat)
    (floorEvidence : List Message) (served : List Nat) (relay : List (Nat × Message))
    (ahead : List (Nat × Nat)) :
    Kept outbox { self := self, current := current, deadline := deadline, now := now, views := views, checked := checked, offers := offers, outbox := s.outbox, audit := audit, delivered := delivered, committedTip := tip, needsPoll := needsPoll, failed := failed, lastCommitted := lastCommitted, floorEvidence := floorEvidence, served := served, relay := relay, ahead := ahead } ↔ Kept outbox s := Iff.rfl

theorem kept_append (s : State) (extra : List Message) (old : Kept outbox s) :
    Kept outbox { s with outbox := s.outbox ++ extra } :=
  fun m member => List.mem_append.mpr (Or.inl (old m member))

theorem putView_kept (s : State) (v : View) (old : Kept outbox s) : Kept outbox (putView s v) :=
  kept_of_same s _ old rfl

theorem register_kept (s : State) (message : Message) (old : Kept outbox s) :
    Kept outbox (register s message) := putView_kept s _ old

theorem broadcast_kept (s : State) (view : Nat) (kind : Kind) (arg : Argument)
    (old : Kept outbox s) : Kept outbox (broadcast s view kind arg) :=
  fun m member => List.mem_append.mpr (Or.inl (register_kept s ⟨s.self, view, kind, arg⟩ old m member))

theorem clear_outbox (s : State) (view : Nat) (arg : Argument) :
    (clear s view arg).outbox = s.outbox := by
  cases arg <;> unfold clear <;> dsimp only <;> split <;> rfl

theorem clear_kept (s : State) (view : Nat) (arg : Argument) (old : Kept outbox s) :
    Kept outbox (clear s view arg) := kept_of_same s _ old (clear_outbox s view arg)

theorem sendCandidate_kept (s : State) (view : Nat) (arg : Argument) (old : Kept outbox s) :
    Kept outbox (sendCandidate s view arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact old
  · apply broadcast_kept
    exact putView_kept _ _ old

theorem castVote_kept (s : State) (view : Nat) (block : Block) (old : Kept outbox s) :
    Kept outbox (castVote s view block) := by
  unfold castVote
  dsimp only
  split
  · exact old
  · apply broadcast_kept
    exact putView_kept _ _ old

theorem commitAt_kept (s : State) (number : Nat) (block : Block) (old : Kept outbox s) :
    Kept outbox (commitAt s number block) := by
  have same : (doCommit s number block).outbox = s.outbox := by
    have cleared := clear_outbox s number (some block)
    unfold doCommit
    dsimp only
    split_ifs <;> first | rfl | exact cleared
  unfold commitAt raiseFloor
  dsimp only
  split <;> exact kept_of_same s _ old same


macro "kept_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [kept_record]
    | with_reducible apply commitAt_kept
    | with_reducible apply sendCandidate_kept
    | with_reducible apply castVote_kept
    | with_reducible apply register_kept
    | with_reducible apply broadcast_kept
    | with_reducible apply clear_kept
    | with_reducible apply putView_kept
    | with_reducible apply kept_append
    | solve | simp_all [viewAt_number]
    | split)
macro "kept_chain" : tactic => `(tactic| repeat' kept_step)

theorem kept_fold {α : Type} (action : State → α → State)
    (each : ∀ state item, Kept outbox state → Kept outbox (action state item))
    (items : List α) (state : State) (old : Kept outbox state) :
    Kept outbox (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact old
  | cons item rest ih => exact ih (action state item) (each state item old)

theorem valueRules_kept (c : Config) (s : State) (view : Nat) (block : Block)
    (old : Kept outbox s) : Kept outbox (valueRules c s view block) := by
  simp only [valueRules, Id.run, bind, pure]
  kept_chain

theorem argumentRules_kept (c : Config) (s : State) (view : Nat) (arg : Argument)
    (old : Kept outbox s) : Kept outbox (argumentRules c s view arg) := by
  simp only [argumentRules, Id.run, bind, pure]
  kept_chain

theorem progressView_kept (c : Config) (s : State) (view : Nat)
    (old : Kept outbox s) : Kept outbox (progressView c s view) := by
  simp only [progressView, Id.run, bind, pure]
  apply kept_fold
  · intro state arg prior
    exact argumentRules_kept c state view arg prior
  · apply kept_fold
    · intro state block prior
      exact valueRules_kept c state view block prior
    · exact old

theorem propose_kept (s : State) (old : Kept outbox s) : Kept outbox (propose s) := by
  unfold propose
  dsimp only
  kept_chain

theorem enterView_kept (c : Config) (s : State) (view : Nat)
    (old : Kept outbox s) : Kept outbox (enterView c s view) := by
  unfold enterView
  dsimp only
  split
  · apply propose_kept
    kept_chain
  · kept_chain

theorem floorJump_kept (c : Config) (s : State) (old : Kept outbox s) :
    Kept outbox (floorJump c s) := by
  unfold floorJump
  split
  · exact enterView_kept c s _ old
  · exact old

theorem progressOuter_kept (c : Config) (s : State) (old : Kept outbox s) :
    Kept outbox (progressOuter c s) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | with_reducible apply enterView_kept
    | with_reducible apply propose_kept
    | kept_step

theorem pass_kept (c : Config) (s : State) (old : Kept outbox s) :
    Kept outbox (pass c s) := by
  unfold pass
  apply progressOuter_kept
  apply floorJump_kept
  apply kept_fold
  · intro state view prior
    exact progressView_kept c state view prior
  · exact old

theorem pump_kept (c : Config) (fuel : Nat) (s : State) (old : Kept outbox s) :
    Kept outbox (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simpa only [pump, kept_record] using old
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_kept
      simpa only [kept_record] using old
    · apply ih
      apply pass_kept
      simpa only [kept_record] using old

theorem ingest_kept (c : Config) (s : State) (message : Message)
    (old : Kept outbox s) : Kept outbox (ingest c s message) := by
  unfold ingest
  repeat' split
  all_goals first
    | exact old
    | (try unfold serveFloor
       try unfold noteAhead
       try unfold serveViews
       try dsimp only
       kept_chain)

theorem step_kept (c : Config) (s : State) (input : Input) (old : Kept outbox s) :
    Kept outbox (step c s input) := by
  unfold step
  dsimp only
  split
  · kept_chain
  · apply pump_kept
    cases input with
    | delivery message => exact ingest_kept c s message old
    | deliveryAt now message =>
      apply ingest_kept
      kept_chain
    | checked block => dsimp only; kept_chain
    | offer payload => dsimp only; kept_chain
    | poll => exact old
    | tick now =>
      dsimp only
      repeat' first
        | with_reducible apply pump_kept
        | kept_step
      all_goals exact fun m member =>
        List.mem_append.mpr (Or.inl (pump_kept c c.pumpBudget s old m member))

#assert_axioms step_kept

end Minidregg.Kernel.GenericSimplexOutbox
