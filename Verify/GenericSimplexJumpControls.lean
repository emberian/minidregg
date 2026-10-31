import Kernel.GenericSimplex
import Theory.AssertAxioms

/-! Deliberately finite mutation controls, not a general safety theorem.
The general proof is Kernel.GenericSimplexJumpSafety. The reachable 1 -> 3
witness there separately checks authenticated premise inhabitation. -/
namespace Minidregg.Verify.GenericSimplexJumpControls
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

def config : Config := {parties := 4, faults := 1, timeout := 7, backoffCap := 3}
def state : State :=
  {self := 0, current := 2, deadline := 9, now := 11,
   views := [
     {number := 3, prepared := [[[1]]]},
     {number := 5, prepared := [[[1], [2]]]},
     {number := 4, voted := true, disableRequested := true,
      sentCommit := some [[1]], sentCandidates := [some [[1]]],
      committed := some [[1]], received := [⟨2, 4, .ready, none⟩]}]}

/-- A larger hint without preparation cannot win maximum-prepared selection. -/
theorem selection_control :
    preparedAbove {state with views := state.views ++ [{number := 9}]} = 5 := by
  decide +kernel

/-- Distinguishes max from first/min, and j+1 from j, ordinary +1 or no jump. -/
theorem successor_control : (progressOuter config state).current = 6 := by
  decide +kernel

theorem deadline_control :
    (progressOuter config state).deadline = state.now + viewTimeout config state 6 := by
  decide +kernel

/-- Compare individual safety-bearing fields, not full-State BEq. -/
theorem flags_control :
    (viewAt (progressOuter config state) 4).disabled = false ∧
    (viewAt (progressOuter config state) 4).voted = true ∧
    (viewAt (progressOuter config state) 4).disableRequested = true ∧
    (viewAt (progressOuter config state) 4).sentCommit = some [[1]] ∧
    (viewAt (progressOuter config state) 4).committed = some [[1]] ∧
    (viewAt (progressOuter config state) 5).prepared = [[[1], [2]]] := by
  decide +kernel

def readyBelowView : View :=
  {number := 2, sentReadyRelay := [some []],
   received := [⟨1, 2, .ready, some []⟩, ⟨2, 2, .ready, some []⟩]}

def readyBelow : State :=
  {self := 0, deadline := 1, views := [readyBelowView]}

/-- Counts enrolled signer identities, not messages; READY uses 2f+1, while
VOTE/COMMIT use Q=n-f. These controls do not assert NF consensus safety. -/
theorem quorum_control :
    config.quorum = 3 ∧
    count {number := 2, received := [⟨1, 2, .vote, some [[1]]⟩,
      ⟨1, 2, .vote, some [[1]]⟩, ⟨2, 2, .vote, some [[1]]⟩]} .vote (some [[1]]) = 2 ∧
    (viewAt (argumentRules config readyBelow 2 (some [])) 2).prepared = [] := by
  decide +kernel

#assert_axioms selection_control
#assert_axioms successor_control
#assert_axioms deadline_control
#assert_axioms flags_control
#assert_axioms quorum_control
end Minidregg.Verify.GenericSimplexJumpControls
