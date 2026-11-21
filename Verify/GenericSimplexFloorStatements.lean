import Verify.GenericSimplexJumpStarvation

/-! Executed witnesses for the commit floor (issues #2, #13). The statements are proved
elsewhere:

* the floor is the fold: `Kernel.GenericSimplexFloor.lastCommitted_spec`;
* a rebase is unobservable, and a replica that forgets runs as one that does not:
  `Kernel.GenericSimplexErasure.rebase_observational`, `step_erase`, `liveStep_run`.

This file runs them on the F2 state (satisfiable) and on a state that lost its floor (teeth).
The `Reachable`-level statements are in `Verify.GenericSimplexJumpReach`, and so are this
file's axiom pins (it imports the kernel only). -/
namespace Minidregg.Verify.GenericSimplexFloorStatements
open Minidregg.Kernel.GenericSimplex
open Minidregg.Verify.GenericSimplexJumpStarvation
set_option autoImplicit false

def run (c : Config) (s : State) (inputs : List Input) : State := inputs.foldl (step c) s

/-- The sends a run added to the audit. -/
def newSends (before after : State) : List Message :=
  (after.audit.drop before.audit.length).filterMap fun event =>
    match event with
    | .send m => some m
    | _ => none

def FloorAgrees (s : State) : Prop := s.lastCommitted = lastCommittedView s

/-! ## Witnesses, executed -/

/-- Party `p` after `[[2]]` committed in view 2 (floor 2). -/
def before (party : Nat) : State := rebaseSetup.states[party]!

/-- The delayed view-1 votes of all four parties, four view-1 COMMITs, then a timeout. -/
def lateInputs : List Input :=
  ([0, 1, 2, 3].map fun p => Input.delivery ⟨p, 1, .vote, some [[1]]⟩) ++
  ([0, 1, 2, 3].map fun p => Input.delivery ⟨p, 1, .commit, some [[1]]⟩) ++ [.tick 50]

def allHonest (net : Net) (test : State → Bool) : Bool := (honestStates net).all test

/-- Compiled evaluation: four whole runs, one of them twelve rounds. -/
theorem floor_agrees_executed :
    ([mainRun, rescued, stranded, keptMemory].all fun net =>
      allHonest net fun s => s.lastCommitted == lastCommittedView s) = true := by
  native_decide

/-- Teeth: a state whose floor field was reset lags its committed view. -/
theorem lagging_floor_disagrees : ¬ FloorAgrees { before 0 with lastCommitted := 0 } := by
  unfold FloorAgrees
  decide +kernel

/-- The floor refuses: the late view-1 messages and a timeout produce no send at or below
the floor, and no failure. -/
theorem floor_refuses_executed :
    ([0, 1, 2].all fun p =>
      let s := before p
      let t := run cfg s lateInputs
      !t.failed && decide (t.lastCommitted < t.current) &&
        (newSends s t).all fun m => decide (s.lastCommitted < m.view)) = true := by
  decide +kernel

/-- Erasure, executed: the replica that forgets after every step is the forgotten image of
the one that keeps everything, and sends the same messages. -/
theorem erasure_executed :
    ([0, 1, 2].all fun p =>
      let s := before p
      lateInputs.foldl (liveStep cfg) (forget s) == forget (run cfg s lateInputs) &&
        (run cfg (forget s) lateInputs).outbox == (run cfg s lateInputs).outbox) = true := by
  decide +kernel


/-- Forgetting the floor as well is observable: the forgetful replica sends a view-1 COMMIT. -/
theorem forgotten_floor_observable :
    ([0, 1, 2].all fun p =>
      let s := before p
      let t := forgetFloor s
      (run cfg t lateInputs).outbox != (run cfg s lateInputs).outbox &&
        (newSends t (run cfg t lateInputs)).any fun m => m.view == 1 && m.kind == .commit) = true := by
  decide +kernel

end Minidregg.Verify.GenericSimplexFloorStatements
