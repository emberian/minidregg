/- Conformance of actual source controller administrative transitions against
the emitted shared gate DAG, using the exact physical-state codec.
These are explicitly compiler-trusting execution checks, not the general
controller simulation theorem. Other dispatch branches remain unhandled. -/
import Compiler.BendObliviousAdministrative
import Compiler.BendObliviousCodec
import Theory.AssertCompiled

namespace Minidregg.Assurance.BendObliviousAdministrativeChecks
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler
set_option autoImplicit false

def shape : BendObliviousState.Shape := ⟨1,2,3,3,8⟩
def limits : Limits := ⟨⟨1,3,by decide⟩,2,3⟩
def library : Library := ⟨⟨#[],#[],#[]⟩,#[]⟩

def base (control : Control) : State :=
  ⟨⟨#[.nil],1⟩,#[false],[],control,4⟩

def runBlock (state : State) : Option State := do
  let input ← BendObliviousCodec.encode shape state
  let output ← (BendObliviousAdministrative.network shape).evaluate input
  if output[0]? == some true then
    BendObliviousCodec.decode shape (output.extract 1 output.size)
  else none

theorem reversing_argument_exact :
    let state := base (.reverseArguments 2 0 [(.Q1,1),(.Q0,2)] [(.Q2,3)])
    runBlock state = some (step limits library state) := by native_decide

theorem reversal_finished_exact :
    let state := base (.reverseArguments 2 0 [] [(.Q1,1),(.Q0,2)])
    runBlock state = some (step limits library state) := by native_decide

theorem installing_argument_exact :
    let state := base (.installArguments 2 0 [(.Q1,1),(.Q0,2)])
    runBlock state = some (step limits library state) := by native_decide

theorem installation_finished_exact :
    let state := base (.installArguments 2 0 [])
    runBlock state = some (step limits library state) := by native_decide

theorem full_stack_refusal_preserves_source_state :
    let state := {base (.installArguments 2 0 [(.Q1,1)]) with
      stack := [.rewrite 1 0,.rewrite 2 0]}
    runBlock state = some (step limits library state) := by native_decide

theorem complete_absorbs_exact :
    let state := base (.complete 0)
    runBlock state = some (step limits library state) := by native_decide

theorem refusal_absorbs_exact :
    let state := base (.refused .argumentCapacity)
    runBlock state = some (step limits library state) := by native_decide

theorem unhandled_is_not_success :
    runBlock (base (.evaluate 0 0)) = none := by native_decide

#assert_compiled reversing_argument_exact
#assert_compiled reversal_finished_exact
#assert_compiled installing_argument_exact
#assert_compiled installation_finished_exact
#assert_compiled full_stack_refusal_preserves_source_state
#assert_compiled complete_absorbs_exact
#assert_compiled refusal_absorbs_exact
#assert_compiled unhandled_is_not_success
end Minidregg.Assurance.BendObliviousAdministrativeChecks
