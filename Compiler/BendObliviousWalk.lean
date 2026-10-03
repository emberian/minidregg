/- Full case-tree walk/classify controls of the same fixed-access controller.
Each physical tick follows at most one classifier edge. Leaf argument reversal
and installation remain their own controls; no secret-length host recursion.
All capacity refusals retain the original pre-tick state. -/
import Compiler.BendObliviousApply

namespace Minidregg.Compiler.BendObliviousWalk
open ObliviousNetwork ObliviousWords BendObliviousState
open BendObliviousAccess BendObliviousAdministrative BendObliviousProgram
open BendObliviousMutation BendObliviousEvaluate BendObliviousApply
set_option autoImplicit false

/-- Exact widened sum of two w-bit lengths; the extra bit prevents aliasing. -/
def lengthSum {width : Nat} (zero one : Nat) (left right : Word width) :
    Builder (Word (width+1)) := do
  let mut carry := zero
  let mut out := Vector.replicate (width+1) zero
  for bit in List.finRange width do
    let different ← emit (.xor left[bit] right[bit])
    let sum ← emit (.xor different carry)
    let both ← emit (.and left[bit] right[bit])
    let passing ← emit (.and different carry)
    carry ← emit (.xor both passing)
    out := out.set bit.val sum (by omega)
  pure (out.set width carry (by omega))

def nodeCode {shape : Shape} (one : Nat) (code : CodeView shape) : Builder Nat := do
  let lam ← equalConstant one code.tag 6
  let projection ← equalConstant one code.tag 10
  let matched ← equalConstant one code.tag 13
  let empty ← equalConstant one code.tag 14
  let first ← emit (.xor lam projection)
  let second ← emit (.xor matched empty)
  emit (.xor first second)

def rootWalk {shape : Shape} {library : Minidregg.Theory.BendClosureMachine.Library}
    (zero one : Nat) (rom : ROM shape library) (state : State shape)
    (initial : Trial shape) (code : CodeView shape) (isNode : Nat) :
    Builder (Result shape) := do
  let blank := Vector.replicate shape.wordBits zero
  let q0 ← constant 2 0
  let args := state.control.first
  let length := state.control.firstLength
  let pc := state.control.a
  let environment := state.control.b
  let original := state.control.c
  let head := headRow zero args
  let q := slice zero head 0 2
  let value := slice zero head 2 shape.wordBits
  let rest := tailRows zero args
  let (_,restLength) ← decrement one length
  let qDead ← equalConstant one q 0
  let qLive ← notBit one qDead
  /- A non-node is a completed source call, not another interpreter loop. -/
  let required ← lengthSum zero one state.stackLength length
  let cap ← constant (shape.wordBits+1) shape.frameSlots
  let tooMany ← lessThan zero one cap required
  let leaf ← guard (← notBit one tooMany) 13 initial
  let leaf ← go 10 pc environment leaf
  let leaf := {leaf with state := {leaf.state with control := {leaf.state.control with
    secondLength := blank,second := Vector.replicate shape.argumentSlots
      (Vector.replicate (argumentBits shape) zero)}}}
  let leaf ← counted one leaf
  /- Non-application node with an argument: source default is caseArgument. -/
  let failure ← guard zero 8 initial
  let mut nonempty : Result shape := ⟨failure,zero⟩
  let binderDead ← equalConstant one code.quantity 0
  let mismatch ← emit (.xor binderDead qDead)
  let lambda ← guard (← notBit one mismatch) 19 initial
  let (bound,lambda) ← bind zero one rom lambda code.quantity value environment
  let lambda ← go 6 code.a bound lambda
  let lambda := {lambda with state := {lambda.state with control := {lambda.state.control with
    c := original,first := rest,firstLength := restLength}}}
  nonempty ← choose (← equalConstant one code.tag 6) ⟨lambda,zero⟩ nonempty
  /- Projection inserts exactly two arguments while consuming one. -/
  let projection ← guard qLive 9 initial
  let (valid,pair) ← readHeap zero one state value
  let projection ← guard valid 15 projection
  let projection ← guard (← equalConstant one pair.tag 4) 11 projection
  let argsCapacity ← constant shape.wordBits shape.argumentSlots
  let projection ← guard (← lessThan zero one length argsCapacity) 6 projection
  let firstQ ← fieldQuantity one pair.quantity q
  let args := prependRow zero (argument zero firstQ pair.first)
    (prependRow zero (argument zero q pair.second) rest)
  let (_,newLength) ← increment one length
  let projection ← go 6 code.a environment projection
  let projection := {projection with state := {projection.state with control :=
    {projection.state.control with c := original,first := args,firstLength := newLength}}}
  nonempty ← choose (← equalConstant one code.tag 10) ⟨projection,zero⟩ nonempty
  /- Match removes the head only on the yes branch. -/
  let matched ← guard qLive 9 initial
  let (actual,matched) ← labelOf zero one rom value matched
  let (wantedValid,_,_) ← readDefinition zero one rom code.a
  let matched ← guard wantedValid 16 matched
  let same ← equal one actual code.a
  let yes ← go 6 code.b environment matched
  let yes := {yes with state := {yes.state with control := {yes.state.control with
    c := original,first := rest,firstLength := restLength}}}
  let no ← go 6 code.c environment matched
  let no := {no with state := {no.state with control := {no.state.control with c := original}}}
  let matched ← select same yes no
  nonempty ← choose (← equalConstant one code.tag 13) ⟨matched,zero⟩ nonempty
  let empty ← equalConstant one length 0
  let returned ← go 3 original blank initial
  let ordinary ← choose empty ⟨returned,zero⟩ nonempty
  /- Application-node arguments are variables in the captured environment. -/
  let (argValid,argCode) ← readCode zero one rom code.b
  let application ← guard argValid 12 initial
  let application ← guard (← equalConstant one argCode.tag 0) 10 application
  let application ← go 2 argCode.a environment application
  let application := {application with state := {application.state with control :=
    {application.state.control with quantity := code.quantity,c := code.a,d := environment,e := original}}}
  let node ← choose (← equalConstant one code.tag 7) ⟨application,zero⟩ ordinary
  choose isNode node leaf

def block {shape : Shape} {library : Minidregg.Theory.BendClosureMachine.Library}
    (zero one : Nat) (rom : ROM shape library) (state : State shape) :
    Builder (Nat × State shape) := do
  let walking ← equalConstant one state.control.tag 6
  let classifying ← equalConstant one state.control.tag 7
  let handled ← emit (.xor walking classifying)
  let (rootValid,root) ← readCode zero one rom state.control.a
  let start ← guard rootValid 12 (begin zero one state)
  let (argValid,arg) ← readCode zero one rom root.b
  let rootApplication ← equalConstant one root.tag 7
  let appStart ← guard argValid 12 start
  let start ← select rootApplication appStart start
  let argumentVariable ← equalConstant one arg.tag 0
  let startClassify ← emit (.and rootApplication argumentVariable)
  let node ← nodeCode one root
  let walked ← rootWalk zero one rom state start root node
  let continued ← go 7 state.control.a state.control.b start
  let continued := {continued with state := {continued.state with control :=
    {continued.state.control with d := root.a}}}
  let startResult ← choose startClassify ⟨continued,zero⟩ walked
  /- Classify reads cursor before re-reading the original code in walk. -/
  let (cursorValid,cursor) ← readCode zero one rom state.control.d
  let classifier ← guard cursorValid 12 (begin zero one state)
  let cursorApplication ← equalConstant one cursor.tag 7
  let continued := {classifier with state := {classifier.state with control :=
    {classifier.state.control with d := cursor.a}}}
  let classifier ← guard rootValid 12 classifier
  let cursorNode ← nodeCode one cursor
  let classified ← rootWalk zero one rom state classifier root cursorNode
  let classifierResult ← choose cursorApplication ⟨continued,zero⟩ classified
  let result ← choose classifying classifierResult startResult
  finishResult zero one handled state result

end Minidregg.Compiler.BendObliviousWalk
