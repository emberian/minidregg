/- Actual fixed-schema initializer -> same compiled controller -> exact source
Data value for both private-input choices. These are explicitly clear native
conformance executions, not malicious-share or all-input refinement proofs. -/
import Compiler.BendObliviousInput
import Compiler.BendInvocationAdmission
import Theory.AssertCompiled

namespace Minidregg.Assurance.BendObliviousInputChecks
open Minidregg.Theory BendTT BendClosureMachine
open Minidregg.Compiler
set_option autoImplicit false

def shape : BendObliviousState.Shape := ⟨16,8,8,5,8⟩
def book : Book :=
  [⟨"inputFalse",.Enu ["False","True"],.Lab "False",false⟩,
   ⟨"inputTrue",.Enu ["False","True"],.Lab "True",false⟩,
   ⟨"inputUnit",.Enu ["()"],.Lab "()",false⟩]

def schema : BendObliviousInput.Schema :=
  .pair .Q1 (.choice 0 (.literal (.label "True")) (.literal (.label "False")))
    (.literal (.label "()"))

def sourceValue (input : Bool) : Term :=
  .Tup .Q1 (.Lab (if input then "True" else "False")) (.Lab "()")

def observe (input : Bool) : Option (Term × Nat) := do
  let expected := sourceValue input
  let _admitted ← BendInvocationAdmission.admit book 256 expected
    (.Sig .Q1 (.Enu ["False","True"]) (.Enu ["()"]))
  let compiled ← BendClosureCompile.compile book (.Var 0)
  let initialized ← BendObliviousInput.prepare compiled shape 1 .Q2 schema
  let controller ← BendObliviousExecution.ofCompiled shape compiled
  let initial ← initialized.network.evaluate #[input]
  if initial[0]? != some true then none else do
    let result ← BendObliviousExecution.runReference controller.network 16
      (initial.extract 1 initial.size)
    if !result.physical.all id then none else do
      let final ← BendObliviousCodec.decode shape result.bits
      match final.control with
      | .complete pointer =>
        let value ← BendClosureArena.decode compiled.library.program final.heap 100 pointer
        pure (value.term,final.heap.used)
      | _ => none

theorem both_secret_choices_produce_their_exact_source_value :
    observe false = some (sourceValue false,6) ∧
    observe true = some (sourceValue true,6) := by native_decide

#assert_compiled both_secret_choices_produce_their_exact_source_value
end Minidregg.Assurance.BendObliviousInputChecks
