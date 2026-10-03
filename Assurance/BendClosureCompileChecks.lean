import Compiler.BendClosureCompile
import Theory.AssertCompiled

namespace Minidregg.Assurance.BendClosureCompileChecks
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler.BendClosureCompile
set_option autoImplicit false

def limits : Limits := ⟨⟨64, 8, by decide⟩, 32, 32⟩

def identityBook : Book :=
  [⟨"identity", .All .Q1 (.Enu ["yes"]) (.Enu ["yes"]),
    .Lam .Q1 (.Var 0), false⟩]

/-- This result comes from compiled code plus the actual closure controller,
not from executeChecked or WNF. Decoding only proves which source term the
result pointer denotes. The general controller simulation is separate. -/
def observe (book : Book) (entry : Term) : Option Term := do
  let compiled ← compile book entry
  let initial ← (start limits compiled.library compiled.entry).toOption
  let final := run limits compiled.library 100 initial
  match final.control with
  | .complete pointer =>
    let decoded ← decode compiled.library.program final.heap 100 pointer
    some decoded.term
  | _ => none

theorem named_source_compiles_and_runs :
    observe identityBook (.App .Q1 (.Ref "identity") (.Lab "yes")) =
      some (.Lab "yes") := by native_decide

/-- Opacity does not erase the source model from live Eval. -/
theorem opaque_source_model_compiles_and_runs :
    observe [⟨"identity", .All .Q1 (.Enu ["yes"]) (.Enu ["yes"]),
      .Lam .Q1 (.Var 0), true⟩]
      (.App .Q1 (.Ref "identity") (.Lab "yes")) =
      some (.Lab "yes") := by native_decide

#assert_compiled named_source_compiles_and_runs
#assert_compiled opaque_source_model_compiles_and_runs
end Minidregg.Assurance.BendClosureCompileChecks
