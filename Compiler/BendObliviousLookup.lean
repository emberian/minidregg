/- Fixed-gate implementation of actual environment-lookup controls 1/2.
The second heap read occurs for every input, including walk-resume and failure.
This is a block of the complete controller under construction, with explicit
handled output; source relation and whole-dispatch qualification are separate. -/
import Compiler.BendObliviousAccess

namespace Minidregg.Compiler.BendObliviousLookup
open ObliviousNetwork ObliviousWords BendObliviousState
open BendObliviousAccess BendObliviousAdministrative
set_option autoImplicit false

def evaluatePointer {shape : Shape} (zero one : Nat) (state : State shape)
    (pointer : Word shape.wordBits) (valid : Nat) (row : RowView shape) :
    Builder (State shape) := do
  let closure ← equalConstant one row.tag 3
  let pair ← equalConstant one row.tag 4
  let application ← equalConstant one row.tag 5
  let ready ← emit (.xor pair application)
  let evaluateTag ← constant 4 0
  let returnedTag ← constant 4 3
  let evaluated : State shape := {state with control := {state.control with
    tag := evaluateTag,a := row.first,b := row.second}}
  let returned : State shape := {state with control := {state.control with
    tag := returnedTag,a := pointer}}
  let notTerm ← refused state 18
  let missing ← refused state 15
  let present ← muxState ready returned notTerm
  let present ← muxState closure evaluated present
  muxState valid present missing

def resumeWalk {shape : Shape} (zero one : Nat) (state : State shape)
    (pointer : Word shape.wordBits) : Builder (State shape) := do
  let capacity ← constant shape.wordBits shape.argumentSlots
  let room ← lessThan zero one state.control.firstLength capacity
  let (_, length) ← increment one state.control.firstLength
  let walkTag ← constant 4 6
  let resumed : State shape := {state with control := {state.control with
    tag := walkTag,a := state.control.c,b := state.control.d,c := state.control.e,
    firstLength := length,
    first := prependRow zero (argument zero state.control.quantity pointer) state.control.first}}
  let full ← refused state 6
  muxState room resumed full

def block {shape : Shape} (zero one : Nat) (state : State shape) :
    Builder (Nat × State shape) := do
  let ordinary ← equalConstant one state.control.tag 1
  let walking ← equalConstant one state.control.tag 2
  let handled ← emit (.xor ordinary walking)
  let (environmentValid, environment) ← readHeap zero one state state.control.b
  /- Port two is fixed, even when this branch will not consume it. -/
  let (valueValid, value) ← readHeap zero one state environment.first
  let environmentTag ← equalConstant one environment.tag 2
  let atHead ← equalConstant one state.control.a 0
  let (_, index) ← decrement one state.control.a
  let next : State shape := {state with control := {state.control with a := index,b := environment.second}}
  let evaluated ← evaluatePointer zero one state environment.first valueValid value
  let walked ← resumeWalk zero one state environment.first
  let head ← muxState walking walked evaluated
  let indexed ← muxState atHead head next
  let unbound ← refused state 21
  let missing ← refused state 15
  let named ← muxState environmentTag indexed unbound
  let present ← muxState environmentValid named missing
  let result ← muxState handled present state
  pure (handled,result)

def network (shape : Shape) : Network := Id.run do
  let (state,size) := (stateInputs shape).run 0
  let build : Builder Unit := do
    let zero ← emit (.constant false)
    let one ← emit (.constant true)
    let (handled,result) ← block zero one state
    modify fun graph => {graph with outputs := #[handled] ++ result.outputs}
  pure (build.run {inputCount := size}).2

end Minidregg.Compiler.BendObliviousLookup
