/- Whole admitted source -> actual compiler -> fixed circuit -> source result.
This consumer never calls Machine.run or executeChecked to generate its result.
The public example is clear conformance, not a private input protocol. -/
import Compiler.BendObliviousExecution
import Compiler.BendInvocationAdmission
import Compiler.BendObliviousCodec
import Theory.AssertCompiled

namespace Minidregg.Assurance.BendObliviousExecutionChecks
open Minidregg.Theory BendTT BendClosureMachine
open Minidregg.Compiler
set_option autoImplicit false

def shape : BendObliviousState.Shape := ⟨16,8,8,5,8⟩
def limits : Limits := ⟨⟨16,5,by decide⟩,8,8⟩

def identityBook (opaqueModel : Bool) : Book :=
  [⟨"identity",.All .Q1 (.Enu ["yes"]) (.Enu ["yes"]),
    .Lam .Q1 (.Var 0),opaqueModel⟩]

/-- Actual typed source admission and actual fixed controller execution.
Public tick padding continues through complete/refused states. -/
def observe (book : Book) (entry outputType : Term) : Option Term := do
  let _admitted ← BendInvocationAdmission.admit book 256 entry outputType
  let prepared ← BendObliviousExecution.prepare book entry shape
  let initial ← (start limits prepared.compiled.library prepared.compiled.entry).toOption
  let bits ← BendObliviousCodec.encode shape initial
  let result ← BendObliviousExecution.runReference prepared.network 40 bits
  if !result.physical.all id then none
  else do
    let final ← BendObliviousCodec.decode shape result.bits
    match final.control with
    | .complete pointer =>
      let value ← decode prepared.compiled.library.program final.heap 100 pointer
      pure value.term
    | _ => none

theorem admitted_source_runs_through_fixed_network :
    observe (identityBook false) (.App .Q1 (.Ref "identity") (.Lab "yes"))
      (.Enu ["yes"]) = some (.Lab "yes") := by native_decide

theorem opaque_source_model_runs_through_fixed_network :
    observe (identityBook true) (.App .Q1 (.Ref "identity") (.Lab "yes"))
      (.Enu ["yes"]) = some (.Lab "yes") := by native_decide

#assert_compiled admitted_source_runs_through_fixed_network
#assert_compiled opaque_source_model_runs_through_fixed_network
end Minidregg.Assurance.BendObliviousExecutionChecks
