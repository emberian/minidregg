import Compiler.BendObliviousRollbackSemantics
import Compiler.BendObliviousCodec
import Theory.AssertCompiled

namespace Minidregg.Assurance.BendObliviousRollbackWitness
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler ObliviousNetwork ObliviousWords
open BendObliviousStateSemantics BendObliviousRollbackSemantics
set_option autoImplicit false

def shape : BendObliviousState.Shape := ⟨2,1,1,2,4⟩
def limits : Limits := ⟨⟨2,2,by decide⟩,1,1⟩
def library : Library := ⟨⟨#[.lab 0],#["yes"],#[]⟩,#[]⟩
def started : BendClosureMachine.State :=
  ⟨⟨#[.nil,.vacant],1⟩,#[false,false],[],.evaluate 0 0,0⟩

theorem source_start_inhabited : start limits library 0 = .ok started := by native_decide

def layout := (BendObliviousState.stateInputs shape).run 0

def preparation : Builder (BendObliviousState.State shape × BendObliviousMutation.Trial shape) := do
  let valid ← emit (.constant false)
  let failure ← constant 5 13
  let changedCount ← constant shape.sourceCountBits 7
  let trial := {layout.1 with sourceSteps := changedCount}
  pure (layout.1, ⟨trial,valid,failure⟩)

def prepared := preparation.run {inputCount := layout.2}

def rollbackNetwork : Network :=
  let finished := (BendObliviousMutation.finish prepared.1.1 prepared.1.2).run prepared.2
  {finished.2 with outputs := finished.1.outputs}

def runRollback : Option BendClosureMachine.State := do
  let input ← BendObliviousCodec.encode shape started
  let output ← rollbackNetwork.evaluate input
  BendObliviousCodec.decode shape output

/-- A machine-created initial state, a genuinely changed tentative source
counter, and an actual failed circuit trial inhabit the rollback contract. -/
theorem rollback_native_start :
    runRollback = some {started with control := .refused .continuationCapacity} := by native_decide

/-- Hostile candidate: publishing the tentative counter despite refusal is
rejected by the actual network result. This distinguishes whole-state rollback
from merely setting the refusal control. -/
theorem tentative_counter_not_published :
    runRollback ≠ some {started with control := .refused .continuationCapacity, sourceSteps := 7} := by
  rw [rollback_native_start]
  decide

#assert_compiled source_start_inhabited
#assert_compiled rollback_native_start
#assert_compiled tentative_counter_not_published
end Minidregg.Assurance.BendObliviousRollbackWitness
