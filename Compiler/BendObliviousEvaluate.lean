/- The actual closure evaluate control lowered into fixed DAG branches.
All code variants are constructed from the SAME starting state. Trial.finish
preserves source rollback. Counter overflow is a separate physical refusal:
handled=false and unchanged state, never a wrapped successful source count.
The general graph-to-Machine.evaluate refinement is not yet proved. -/
import Compiler.BendObliviousMutation

namespace Minidregg.Compiler.BendObliviousEvaluate
open ObliviousNetwork ObliviousWords BendObliviousState
open BendObliviousAccess BendObliviousAdministrative BendObliviousProgram
open BendObliviousMutation
set_option autoImplicit false

structure Result (shape : Shape) where
  trial : Trial shape
  overflow : Nat

def choose {shape : Shape} (selector : Nat) (yes no : Result shape) : Builder (Result shape) := do
  pure ⟨← select selector yes.trial no.trial,← emitMux selector yes.overflow no.overflow⟩

def counted {shape : Shape} (one : Nat) (trial : Trial shape) : Builder (Result shape) := do
  let (carry,trial) ← sourceStep one trial
  pure ⟨trial,carry⟩

/-- Source failure wins over a tentative counter carry. Physical overflow is
reported by the handled bit only when the selected source operation succeeds. -/
def finishResult {shape : Shape} (zero one handled : Nat) (original : State shape)
    (result : Result shape) : Builder (Nat × State shape) := do
  let overflow ← emit (.and result.trial.valid result.overflow)
  let safe ← notBit one overflow
  let handled ← emit (.and handled safe)
  let next ← finish original result.trial
  pure (handled,← muxState handled next original)

def block {shape : Shape} {library : Minidregg.Theory.BendClosureMachine.Library}
    (zero one : Nat) (rom : ROM shape library) (state : State shape) :
    Builder (Nat × State shape) := do
  let handled ← equalConstant one state.control.tag 0
  let (codeValid,instruction) ← readCode zero one rom state.control.a
  let initial ← guard codeValid 12 (begin zero one state)
  let environment := state.control.b
  let blank := Vector.replicate shape.wordBits zero
  let q0 ← constant 2 0
  let dead ← equalConstant one instruction.quantity 0
  /- Default includes every source constructor not singled out by evaluate. -/
  let (pointer,defaultTrial) ← closure zero one rom initial state.control.a environment
  let defaultTrial ← go 3 pointer blank defaultTrial
  let mut result : Result shape := ⟨defaultTrial,zero⟩
  /- Var: environment lookup is one later physical microstep. -/
  let variableTrial ← go 1 instruction.a environment initial
  result ← choose (← equalConstant one instruction.tag 0) ⟨variableTrial,zero⟩ result
  /- Ref: retain the source reference thunk as original call. -/
  let reference ← go 5 pointer pointer {defaultTrial with state :=
    {defaultTrial.state with control := {defaultTrial.state.control with
      firstLength := blank,first := Vector.replicate shape.argumentSlots
        (Vector.replicate (argumentBits shape) zero)}}}
  result ← choose (← equalConstant one instruction.tag 1) ⟨reference,zero⟩ result
  /- Annotation performs exactly one source Eval step. -/
  let annotation ← counted one (← go 0 instruction.a environment initial)
  result ← choose (← equalConstant one instruction.tag 2) annotation result
  /- Let has distinct dead/live allocation and continuation paths. -/
  let frameTag ← constant 3 3
  let liveLet ← push zero one initial
    (frameWord zero frameTag instruction.quantity instruction.b environment)
  let liveLet ← go 0 instruction.a environment liveLet
  let (value,deadLet) ← closure zero one rom initial instruction.a environment
  let (bound,deadLet) ← bind zero one rom deadLet instruction.quantity value environment
  let deadLet ← counted one (← go 0 instruction.b bound deadLet)
  let lett ← choose dead deadLet ⟨liveLet,zero⟩
  result ← choose (← equalConstant one instruction.tag 3) lett result
  /- Application evaluates its function first. -/
  let frameTag ← constant 3 0
  let application ← push zero one initial
    (frameWord zero frameTag instruction.quantity instruction.b environment)
  let application ← go 0 instruction.a environment application
  result ← choose (← equalConstant one instruction.tag 7) ⟨application,zero⟩ result
  /- Pair keeps an actual dead thunk, retaining the dead binder position. -/
  let frameTag ← constant 3 4
  let livePair ← push zero one initial
    (frameWord zero frameTag instruction.quantity instruction.b environment)
  let livePair ← go 0 instruction.a environment livePair
  let (first,deadPair) ← closure zero one rom initial instruction.a environment
  let frameTag ← constant 3 5
  let deadPair ← push zero one deadPair
    (frameWord zero frameTag instruction.quantity first blank)
  let deadPair ← go 0 instruction.b environment deadPair
  let pair ← choose dead ⟨deadPair,zero⟩ ⟨livePair,zero⟩
  result ← choose (← equalConstant one instruction.tag 9) pair result
  /- Rewrite evaluates evidence; source motive remains a ghost syntax witness. -/
  let frameTag ← constant 3 6
  let rewrite ← push zero one initial
    (frameWord zero frameTag q0 instruction.c environment)
  let rewrite ← go 0 instruction.a environment rewrite
  result ← choose (← equalConstant one instruction.tag 17) ⟨rewrite,zero⟩ result
  finishResult zero one handled state result

end Minidregg.Compiler.BendObliviousEvaluate
