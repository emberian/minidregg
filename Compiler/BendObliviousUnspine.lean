/- Actual unspine control lowered to one fixed gate schedule.
The original normalized call pointer survives every edge. Definition lookup
uses the public ROM's exact first-name semantics. All three reads occur on every
input, including failure branches. Full dispatch is composed separately. -/
import Compiler.BendObliviousProgram

namespace Minidregg.Compiler.BendObliviousUnspine
open ObliviousNetwork ObliviousWords BendObliviousState
open BendObliviousAccess BendObliviousAdministrative BendObliviousProgram
set_option autoImplicit false

def block {shape : Shape} {library : Minidregg.Theory.BendClosureMachine.Library}
    (zero one : Nat) (rom : ROM shape library) (state : State shape) :
    Builder (Nat × State shape) := do
  let handled ← equalConstant one state.control.tag 5
  let (rowValid,row) ← readHeap zero one state state.control.a
  let (codeValid,code) ← readCode zero one rom row.first
  let (nameValid,definitionExists,body) ← readDefinition zero one rom code.a
  let application ← equalConstant one row.tag 5
  let closure ← equalConstant one row.tag 3
  let reference ← equalConstant one code.tag 1
  let capacity ← constant shape.wordBits shape.argumentSlots
  let room ← lessThan zero one state.control.firstLength capacity
  let (_,length) ← increment one state.control.firstLength
  let next : State shape := {state with control := {state.control with
    a := row.first,firstLength := length,
    first := prependRow zero (argument zero row.quantity row.second) state.control.first}}
  let full ← refused state 6
  let next ← muxState room next full
  let walkTag ← constant 4 6
  let emptyEnvironment ← constant shape.wordBits 0
  let walked : State shape := {state with control := {state.control with
    tag := walkTag,a := body,b := emptyEnvironment,c := state.control.b}}
  let unknown ← refused state 22
  let invalidName ← refused state 16
  let notCall ← refused state 7
  let invalidCode ← refused state 12
  let invalidRow ← refused state 15
  let named ← muxState definitionExists walked unknown
  let named ← muxState nameValid named invalidName
  let referred ← muxState reference named notCall
  let coded ← muxState codeValid referred invalidCode
  let closed ← muxState closure coded notCall
  let selected ← muxState application next closed
  let selected ← muxState rowValid selected invalidRow
  let result ← muxState handled selected state
  pure (handled,result)

end Minidregg.Compiler.BendObliviousUnspine
