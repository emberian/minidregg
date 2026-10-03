/- Administrative blocks of the ONE Bend fixed-access controller.
This is a composable partial dispatch block: handled=false means another block
must handle the control tag. It is never an execution success or a full backend.
It implements actual v2 reverse/install argument controls plus absorbing states,
using the same packed layout and shared Op DAG as the remaining controller.
Source refinement and physical-wire decoding are still required. -/
import Compiler.BendObliviousState

namespace Minidregg.Compiler.BendObliviousAdministrative
open ObliviousNetwork ObliviousWords BendObliviousState
set_option autoImplicit false

def tailRows {slots width : Nat} (zero : Nat)
    (rows : Vector (Word width) slots) : Vector (Word width) slots :=
  Vector.ofFn fun index => rows.toArray[index.val + 1]?.getD (Vector.replicate width zero)

def prependRow {slots width : Nat} (zero : Nat) (head : Word width)
    (rows : Vector (Word width) slots) : Vector (Word width) slots :=
  Vector.ofFn fun index =>
    if index.val = 0 then head
    else rows.toArray[index.val - 1]?.getD (Vector.replicate width zero)

def headRow {slots width : Nat} (zero : Nat)
    (rows : Vector (Word width) slots) : Word width :=
  rows.toArray[0]?.getD (Vector.replicate width zero)

def knownArgumentFrame {shape : Shape} (zero : Nat) (tag : Word 3)
    (argument : Word (argumentBits shape)) : Word (frameBits shape) :=
  Vector.ofFn fun bit =>
    if bit.val < 3 then tag.toArray[bit.val]?.getD zero
    else if bit.val < 5 + shape.wordBits then argument.toArray[bit.val - 3]?.getD zero
    else zero

/-- Both outcomes are built; the secret empty test is a gate selector.
For a represented reachable state, the two lists' combined length is bounded
by argumentSlots. No host loop depends on either secret length. -/
def reverseBlock {shape : Shape} (zero one : Nat) (state : State shape) :
    Builder (State shape) := do
  let empty ← equalConstant one state.control.firstLength 0
  let installTag ← constant 4 11
  let (_, firstLength) ← decrement one state.control.firstLength
  let (_, secondLength) ← increment one state.control.secondLength
  let moved : State shape := {state with control := {state.control with
    first := tailRows zero state.control.first
    second := prependRow zero (headRow zero state.control.first) state.control.second
    firstLength, secondLength}}
  let finished : State shape := {state with control := {state.control with
    tag := installTag
    first := state.control.second
    firstLength := state.control.secondLength}}
  muxState empty finished moved

def installBlock {shape : Shape} (zero one : Nat) (state : State shape) :
    Builder (State shape) := do
  let empty ← equalConstant one state.control.firstLength 0
  let maximum ← constant shape.wordBits shape.frameSlots
  let room ← lessThan zero one state.stackLength maximum
  let refusedTag ← constant 4 9
  let capacityFailure ← constant 5 13
  let evaluateTag ← constant 4 0
  let knownTag ← constant 3 2
  let frame := knownArgumentFrame zero knownTag (headRow zero state.control.first)
  let (_, stackLength) ← increment one state.stackLength
  let (_, remainingLength) ← decrement one state.control.firstLength
  let installed : State shape := {state with
    stack := prependRow zero frame state.stack
    stackLength
    control := {state.control with
      first := tailRows zero state.control.first
      firstLength := remainingLength}}
  let refused : State shape := {state with control := {state.control with
    tag := refusedTag, failure := capacityFailure}}
  let finished : State shape := {state with control := {state.control with tag := evaluateTag}}
  let nonempty ← muxState room installed refused
  muxState empty finished nonempty

/-- The handled bit is explicit; callers cannot treat an unknown branch as a
successful step merely because its fallback state is unchanged. -/
def block {shape : Shape} (zero one : Nat) (state : State shape) :
    Builder (Nat × State shape) := do
  let complete ← equalConstant one state.control.tag 8
  let refused ← equalConstant one state.control.tag 9
  let reverse ← equalConstant one state.control.tag 10
  let install ← equalConstant one state.control.tag 11
  let reverseState ← reverseBlock zero one state
  let installState ← installBlock zero one state
  let afterReverse ← muxState reverse reverseState state
  let afterInstall ← muxState install installState afterReverse
  let absorbing ← emit (.xor complete refused)
  let administrative ← emit (.xor reverse install)
  let handled ← emit (.xor absorbing administrative)
  pure (handled, afterInstall)

def network (shape : Shape) : Network := Id.run do
  let (state, size) := (stateInputs shape).run 0
  let build : Builder Unit := do
    let zero ← emit (.constant false)
    let one ← emit (.constant true)
    let (handled, result) ← block zero one state
    modify fun graph => {graph with outputs := #[handled] ++ result.outputs}
  pure (build.run {inputCount := size}).2

end Minidregg.Compiler.BendObliviousAdministrative
