/- Actual source compiler -> shared fixed controller program.
The public Book/template is compiled once and retained with successful source
translation-validation evidence. Secret arguments belong in a separately
qualified loaded environment, never in this public ROM producer.

runReference evaluates the SAME emitted Boolean network for a public tick
budget. This is a clear conformance consumer, not an MPC implementation.
Physical status wires are retained privately per tick, not publicly released.
A private backend must evaluate the source-approved release predicate over them
and include that predicate in its exact circuit/correlation plan. -/
import Compiler.BendClosureCompile
import Compiler.BendObliviousController

namespace Minidregg.Compiler.BendObliviousExecution
open Minidregg.Theory BendTT
open ObliviousNetwork BendObliviousState
set_option autoImplicit false

structure Prepared (book : Book) (publicTemplate : Term) (shape : Shape) where
  compiled : BendClosureCompile.Compiled book publicTemplate
  network : Network
  exact : BendObliviousController.network shape compiled.library = some network

def prepare (book : Book) (publicTemplate : Term) (shape : Shape) :
    Option (Prepared book publicTemplate shape) := do
  let compiled ← BendClosureCompile.compile book publicTemplate
  match exact : BendObliviousController.network shape compiled.library with
  | none => none
  | some network => pure ⟨compiled,network,exact⟩

structure ReferenceResult where
  bits : Array Bool
  /-- Private physical acceptance wires, one per public tick. These are not
  user-visible timing, fees, or permission to release an execution result. -/
  physical : Array Bool
  deriving Repr

/-- No early completion/refusal branch: absorbing states still evaluate the
whole fixed network. Option failure here is malformed public graph/shape.
Semantic typed-input and coherent-sharing admission are separate prerequisites. -/
def runReference (network : Network) (publicTicks : Nat) (input : Array Bool) :
    Option ReferenceResult := do
  let mut state := input
  let mut physical := #[]
  for _ in List.range publicTicks do
    let output ← network.evaluate state
    let accepted ← output[0]?
    state := output.extract 1 output.size
    physical := physical.push accepted
  pure ⟨state,physical⟩

/-- Every successfully prepared program retains the ACTUAL compiler relation;
no caller-supplied digest or arbitrary network can replace its public source. -/
theorem prepared_source {book : Book} {template : Term} {shape : Shape}
    (prepared : Prepared book template shape) :
    prepared.compiled.library.SourceCorrespondence book ∧
      BendClosureArena.CodeDenotes prepared.compiled.library.program
        prepared.compiled.entry template :=
  ⟨prepared.compiled.definitions,prepared.compiled.exactEntry⟩

theorem prepared_network {book : Book} {template : Term} {shape : Shape}
    (prepared : Prepared book template shape) :
    BendObliviousController.network shape prepared.compiled.library = some prepared.network :=
  prepared.exact

#assert_axioms prepared_source
#assert_axioms prepared_network
end Minidregg.Compiler.BendObliviousExecution
