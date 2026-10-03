/- Smallest inhabited source-admitted full-controller consumer for native
unrolled IR2 qualification. Public source/input; no private-execution claim. -/
import Compiler.BendObliviousExecution
import Compiler.BendInvocationAdmission
import Compiler.BendObliviousCodec
import Theory.AssertCompiled

namespace Minidregg.Assurance.BendObliviousMinimal
open Minidregg.Theory BendTT BendClosureMachine
open Minidregg.Compiler
set_option autoImplicit false

def shape : BendObliviousState.Shape := ⟨2,0,1,1,1⟩
def limits : Limits := ⟨⟨2,1,by decide⟩,0,1⟩
def source : Term := .Lab "yes"
def resultType : Term := .Enu ["yes"]
def ticks : Nat := 2

structure Input where
  prepared : BendObliviousExecution.Prepared [] source shape
  state : State
  bits : Array Bool

def prepare : Option Input := do
  let _ ← BendInvocationAdmission.admit [] 32 source resultType
  let prepared ← BendObliviousExecution.prepare [] source shape
  let state ← (start limits prepared.compiled.library prepared.compiled.entry).toOption
  let bits ← BendObliviousCodec.encode shape state
  pure ⟨prepared,state,bits⟩

def observe : Option (Term × Nat × Array Bool) := do
  let input ← prepare
  let result ← BendObliviousExecution.runReference input.prepared.network ticks input.bits
  let state ← BendObliviousCodec.decode shape result.bits
  match state.control with
  | .complete pointer =>
    let value ← BendClosureArena.decode input.prepared.compiled.library.program state.heap 8 pointer
    pure (value.term,state.sourceSteps,result.physical)
  | _ => none

theorem actual_full_controller : observe = some (.Lab "yes",0,#[true,true]) := by native_decide
#assert_compiled actual_full_controller
end Minidregg.Assurance.BendObliviousMinimal
