import Kernel.GenericSimplexReceiveScope

namespace Minidregg.Kernel.GenericSimplexScopeStructure
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexReceiveScope
set_option autoImplicit false

theorem scoped_fold {α : Type} {c : Config}
    (action : State → α → State)
    (each : ∀ state item, Scoped c state → Scoped c (action state item))
    (items : List α) (state : State) (scopeOK : Scoped c state) :
    Scoped c (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact scopeOK
  | cons item rest ih => exact ih (action state item) (each state item scopeOK)

macro "scoped_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [scoped_record]
    | split
    | with_reducible apply broadcast_scoped
    | with_reducible apply clear_scoped
    | with_reducible apply doCommit_scoped
    | with_reducible apply castVote_scoped
    | with_reducible apply sendCandidate_scoped
    | (with_reducible apply putView_copied_received _ _ <;> try rfl))
macro "scoped_chain" : tactic => `(tactic| repeat' scoped_step)

theorem valueRules_scoped (c : Config) (state : State)
    (number : Nat) (block : Block) (scopeOK : Scoped c state) :
    Scoped c (valueRules c state number block) := by
  simp only [valueRules, Id.run, bind, pure]
  scoped_chain

theorem argumentRules_scoped (c : Config) (state : State)
    (number : Nat) (arg : Argument) (scopeOK : Scoped c state) :
    Scoped c (argumentRules c state number arg) := by
  simp only [argumentRules, Id.run, bind, pure]
  scoped_chain

theorem progressView_scoped (c : Config) (state : State)
    (number : Nat) (scopeOK : Scoped c state) :
    Scoped c (progressView c state number) := by
  simp only [progressView, Id.run, bind, pure]
  apply scoped_fold
  · intro s arg hs; exact argumentRules_scoped c s number arg hs
  · apply scoped_fold
    · intro s block hs; exact valueRules_scoped c s number block hs
    · exact scopeOK

theorem propose_scoped {c : Config} (state : State)
    (scopeOK : Scoped c state) : Scoped c (propose state) := by
  unfold propose
  dsimp only
  scoped_chain

theorem enterView_scoped (c : Config) (state : State)
    (number : Nat) (scopeOK : Scoped c state) :
    Scoped c (enterView c state number) := by
  unfold enterView
  dsimp only
  split
  · apply propose_scoped
    scoped_chain
  · scoped_chain

theorem progressOuter_scoped (c : Config) (state : State)
    (scopeOK : Scoped c state) : Scoped c (progressOuter c state) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | with_reducible apply enterView_scoped
    | scoped_step

theorem pass_scoped (c : Config) (state : State)
    (scopeOK : Scoped c state) : Scoped c (pass c state) := by
  unfold pass
  apply progressOuter_scoped
  apply scoped_fold
  · intro s number hs; exact progressView_scoped c s number hs
  · exact scopeOK

theorem pump_scoped (c : Config) (fuel : Nat) (state : State)
    (scopeOK : Scoped c state) : Scoped c (pump c fuel state) := by
  induction fuel generalizing state with
  | zero => simpa only [pump, scoped_record] using scopeOK
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_scoped
      simpa only [scoped_record] using scopeOK
    · apply ih
      apply pass_scoped
      simpa only [scoped_record] using scopeOK

theorem ingest_scoped (c : Config) (state : State) (message : Message)
    (scopeOK : Scoped c state) : Scoped c (ingest c state message) := by
  unfold ingest
  dsimp only
  repeat' first
    | (with_reducible apply register_scoped message scopeOK <;> simp_all <;> omega)
    | scoped_step

theorem step_scoped (c : Config) (state : State) (input : Input)
    (scopeOK : Scoped c state) : Scoped c (step c state input) := by
  unfold step
  dsimp only
  split
  · scoped_chain
  · apply pump_scoped
    cases input with
    | delivery message => exact ingest_scoped c state message scopeOK
    | deliveryAt time message =>
      apply ingest_scoped
      simpa only [scoped_record] using scopeOK
    | checked block => dsimp only; scoped_chain
    | offer payload => dsimp only; scoped_chain
    | poll => exact scopeOK
    | tick time =>
      dsimp only
      have pumped := pump_scoped c c.pumpBudget state scopeOK
      scoped_chain

theorem start_scoped (c : Config) (party time : Nat) (enrolled : party < c.parties) :
    Scoped c (start c party time) := by
  unfold start
  split
  · exact ⟨enrolled, by intro view member; cases member⟩
  · apply pump_scoped
    apply enterView_scoped
    exact ⟨enrolled, by intro view member; cases member⟩

#assert_axioms valueRules_scoped
#assert_axioms argumentRules_scoped
#assert_axioms progressOuter_scoped
#assert_axioms pump_scoped
#assert_axioms ingest_scoped
#assert_axioms step_scoped
#assert_axioms start_scoped
end Minidregg.Kernel.GenericSimplexScopeStructure
