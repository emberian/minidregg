import Kernel.GenericSimplexReceiveProvenance
import Mathlib.Tactic.FailIfNoProgress

namespace Minidregg.Kernel.GenericSimplexReceiveStructure
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexReceiveProvenance
set_option autoImplicit false

theorem backed_record (external : Message → Prop) (state : State)
    (self current deadline now : Nat) (checked : List Block) (offers : List Bytes)
    (outbox : List Message) (delivered : List Block) (tip : Block)
    (needsPoll failed : Bool) :
    Backed external {
      self := self
      current := current
      deadline := deadline
      now := now
      views := state.views
      checked := checked
      offers := offers
      outbox := outbox
      audit := state.audit
      delivered := delivered
      committedTip := tip
      needsPoll := needsPoll
      failed := failed } ↔ Backed external state := Iff.rfl

theorem putView_copied_received {external : Message → Prop} {state : State}
    (view : View) (number : Nat) (backed : Backed external state)
    (same : view.received = (viewAt state number).received) :
    Backed external (putView state view) := putView_received_unchanged number view backed same

theorem backed_fold {α : Type} {external : Message → Prop}
    (action : State → α → State)
    (each : ∀ state item, Backed external state → Backed external (action state item))
    (items : List α) (state : State) (backed : Backed external state) :
    Backed external (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact backed
  | cons item rest ih => exact ih (action state item) (each state item backed)

macro "backed_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [backed_record]
    | split
    | with_reducible apply broadcast_backed
    | with_reducible apply clear_backed
    | with_reducible apply doCommit_backed
    | with_reducible apply castVote_backed
    | with_reducible apply sendCandidate_backed
    | (with_reducible apply putView_copied_received _ _; rotate_left; rfl))
macro "backed_chain" : tactic => `(tactic| repeat' backed_step)

theorem valueRules_backed {external : Message → Prop} (c : Config) (state : State)
    (number : Nat) (block : Block) (backed : Backed external state) :
    Backed external (valueRules c state number block) := by
  simp only [valueRules, Id.run, bind, pure]
  backed_chain

theorem argumentRules_backed {external : Message → Prop} (c : Config) (state : State)
    (number : Nat) (arg : Argument) (backed : Backed external state) :
    Backed external (argumentRules c state number arg) := by
  simp only [argumentRules, Id.run, bind, pure]
  backed_chain

theorem progressView_backed {external : Message → Prop} (c : Config) (state : State)
    (number : Nat) (backed : Backed external state) :
    Backed external (progressView c state number) := by
  simp only [progressView, Id.run, bind, pure]
  apply backed_fold
  · intro s arg hs; exact argumentRules_backed c s number arg hs
  · apply backed_fold
    · intro s block hs; exact valueRules_backed c s number block hs
    · exact backed

theorem propose_backed {external : Message → Prop} (state : State)
    (backed : Backed external state) : Backed external (propose state) := by
  unfold propose
  dsimp only
  backed_chain

theorem enterView_backed {external : Message → Prop} (c : Config) (state : State)
    (number : Nat) (backed : Backed external state) :
    Backed external (enterView c state number) := by
  unfold enterView
  dsimp only
  split
  · apply propose_backed
    backed_chain
  · backed_chain

theorem progressOuter_backed {external : Message → Prop} (c : Config) (state : State)
    (backed : Backed external state) : Backed external (progressOuter c state) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | with_reducible apply enterView_backed
    | with_reducible apply propose_backed
    | backed_step

theorem pass_backed {external : Message → Prop} (c : Config) (state : State)
    (backed : Backed external state) : Backed external (pass c state) := by
  unfold pass
  apply progressOuter_backed
  apply backed_fold
  · intro s number hs; exact progressView_backed c s number hs
  · exact backed

theorem pump_backed {external : Message → Prop} (c : Config) (fuel : Nat) (state : State)
    (backed : Backed external state) : Backed external (pump c fuel state) := by
  induction fuel generalizing state with
  | zero => simpa only [pump, backed_record] using backed
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_backed
      simpa only [backed_record] using backed
    · apply ih
      apply pass_backed
      simpa only [backed_record] using backed

theorem ingest_backed {external : Message → Prop} (c : Config) (state : State)
    (message : Message) (backed : Backed external state) (available : external message) :
    Backed external (ingest c state message) := by
  unfold ingest
  dsimp only
  repeat' first
    | with_reducible exact register_backed message backed (Or.inl available)
    | backed_step

def InputBacked (external : Message → Prop) : Input → Prop
  | .delivery message | .deliveryAt _ message => external message
  | _ => True

theorem step_backed {external : Message → Prop} (c : Config) (state : State)
    (input : Input) (backed : Backed external state) (inputBacked : InputBacked external input) :
    Backed external (step c state input) := by
  unfold step
  dsimp only
  split
  · backed_chain
  · apply pump_backed
    cases input with
    | delivery message => exact ingest_backed c state message backed inputBacked
    | deliveryAt time message =>
      apply ingest_backed
      · simpa only [backed_record] using backed
      · exact inputBacked
    | checked block => dsimp only; backed_chain
    | offer payload => dsimp only; backed_chain
    | poll => exact backed
    | tick time =>
      dsimp only
      have pumped := pump_backed c c.pumpBudget state backed
      backed_chain

theorem start_backed (c : Config) (party time : Nat) :
    Backed (fun _ => False) (start c party time) := by
  unfold start
  split
  · intro view member; cases member
  · apply pump_backed
    apply enterView_backed
    intro view member; cases member

#assert_axioms valueRules_backed
#assert_axioms argumentRules_backed
#assert_axioms progressOuter_backed
#assert_axioms pump_backed
#assert_axioms ingest_backed
#assert_axioms step_backed
#assert_axioms start_backed
end Minidregg.Kernel.GenericSimplexReceiveStructure
