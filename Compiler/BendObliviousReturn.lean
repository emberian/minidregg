/- Fixed-access lowering of actual returnValue and its seven frame variants.
No secret frame or pointer selects a host branch. All branches are constructed,
and their first failure rolls back the original pre-pop state. -/
import Compiler.BendObliviousEvaluate

namespace Minidregg.Compiler.BendObliviousReturn
open ObliviousNetwork ObliviousWords BendObliviousState
open BendObliviousAccess BendObliviousAdministrative BendObliviousProgram
open BendObliviousMutation BendObliviousEvaluate
set_option autoImplicit false

/-- The actual evaluatePointer operation, used after a known live argument. -/
def evaluatePointer {shape : Shape} (zero one : Nat) (pointer : Word shape.wordBits)
    (initial : Trial shape) : Builder (Trial shape) := do
  let (valid,row) ← readHeap zero one initial.state pointer
  let initial ← guard valid 15 initial
  let closureTag ← equalConstant one row.tag 3
  let pair ← equalConstant one row.tag 4
  let application ← equalConstant one row.tag 5
  let ordinary ← emit (.xor pair application)
  let term ← emitOr closureTag ordinary
  let initial ← guard term 18 initial
  let returned ← go 3 pointer (Vector.replicate shape.wordBits zero) initial
  let closure ← go 0 row.first row.second initial
  select closureTag closure returned

def block {shape : Shape} {library : Minidregg.Theory.BendClosureMachine.Library}
    (zero one : Nat) (rom : ROM shape library) (state : State shape) :
    Builder (Nat × State shape) := do
  let handled ← equalConstant one state.control.tag 3
  let empty ← equalConstant one state.stackLength 0
  let blank := Vector.replicate shape.wordBits zero
  let (_,length) ← decrement one state.stackLength
  let popped := {state with stack := tailRows zero state.stack,stackLength := length}
  let initial := begin zero one popped
  let frame := viewRow zero (headRow zero state.stack)
  let pointer := state.control.a
  let dead ← equalConstant one frame.quantity 0
  let frame1 ← constant 3 1
  let complete ← go 8 pointer blank (begin zero one state)
  /- Function continuation: either evaluate the live argument or retain thunk. -/
  let liveFunction ← push zero one initial
    (frameWord zero frame1 frame.quantity pointer blank)
  let liveFunction ← go 0 frame.first frame.second liveFunction
  let (argument,deadFunction) ← closure zero one rom initial frame.first frame.second
  let deadFunction ← go 4 pointer argument deadFunction
  let deadFunction := {deadFunction with state := {deadFunction.state with
    control := {deadFunction.state.control with quantity := frame.quantity}}}
  let function ← select dead deadFunction liveFunction
  let mut result : Result shape := ⟨function,zero⟩
  /- Evaluated argument. -/
  let argument ← go 4 frame.first pointer initial
  let argument := {argument with state := {argument.state with control :=
    {argument.state.control with quantity := frame.quantity}}}
  result ← choose (← equalConstant one frame.tag 1) ⟨argument,zero⟩ result
  /- Known argument may be a retained dead thunk; reopen it if live. -/
  let liveKnown ← push zero one initial
    (frameWord zero frame1 frame.quantity pointer blank)
  let liveKnown ← evaluatePointer zero one frame.first liveKnown
  let deadKnown ← go 4 pointer frame.first initial
  let deadKnown := {deadKnown with state := {deadKnown.state with control :=
    {deadKnown.state.control with quantity := frame.quantity}}}
  let known ← select dead deadKnown liveKnown
  result ← choose (← equalConstant one frame.tag 2) ⟨known,zero⟩ result
  /- Let evaluates binding before source count and body. -/
  let (environment,lett) ← bind zero one rom initial frame.quantity pointer frame.second
  let lett ← counted one (← go 0 frame.first environment lett)
  result ← choose (← equalConstant one frame.tag 3) lett result
  /- Pair first and pair second. -/
  let frame5 ← constant 3 5
  let first ← push zero one initial (frameWord zero frame5 frame.quantity pointer blank)
  let first ← go 0 frame.first frame.second first
  result ← choose (← equalConstant one frame.tag 4) ⟨first,zero⟩ result
  let tag4 ← constant 3 4
  let (pair,second) ← allocate zero one rom initial ⟨tag4,frame.quantity,frame.first,pointer⟩
  let second ← go 3 pair blank second
  result ← choose (← equalConstant one frame.tag 5) ⟨second,zero⟩ result
  /- Rewrite checks heap, closure tag, code, then reflexivity in source order. -/
  let (valid,evidence) ← readHeap zero one state pointer
  let rewrite ← guard valid 15 initial
  let rewrite ← guard (← equalConstant one evidence.tag 3) 20 rewrite
  let (codeValid,code) ← readCode zero one rom evidence.first
  let rewrite ← guard codeValid 12 rewrite
  let rewrite ← guard (← equalConstant one code.tag 16) 20 rewrite
  let rewrite ← counted one (← go 0 frame.first frame.second rewrite)
  result ← choose (← equalConstant one frame.tag 6) rewrite result
  result ← choose empty ⟨complete,zero⟩ result
  finishResult zero one handled state result

end Minidregg.Compiler.BendObliviousReturn
