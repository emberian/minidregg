/- Fixed-access source application, including beta, projection, matching and
full call-spine fallback. It uses actual retained heap rows and ROM, and never
substitutes a source evaluator result. Successful source counts remain bounded
private words; carry is an explicit unsupported physical transition. -/
import Compiler.BendObliviousReturn

namespace Minidregg.Compiler.BendObliviousApply
open ObliviousNetwork ObliviousWords BendObliviousState
open BendObliviousAccess BendObliviousAdministrative BendObliviousProgram
open BendObliviousMutation BendObliviousEvaluate
set_option autoImplicit false

def labelOf {shape : Shape} {library : Minidregg.Theory.BendClosureMachine.Library}
    (zero one : Nat) (rom : ROM shape library) (pointer : Word shape.wordBits)
    (trial : Trial shape) : Builder (Word shape.wordBits × Trial shape) := do
  let (valid,row) ← readHeap zero one trial.state pointer
  let trial ← guard valid 15 trial
  let trial ← guard (← equalConstant one row.tag 3) 17 trial
  let (valid,code) ← readCode zero one rom row.first
  let trial ← guard valid 12 trial
  let trial ← guard (← equalConstant one code.tag 12) 17 trial
  let (valid,_,_) ← readDefinition zero one rom code.a
  let trial ← guard valid 16 trial
  pure (code.a,trial)

def fieldQuantity (one : Nat) (first applied : Word 2) : Builder (Word 2) := do
  let linear ← equalConstant one first 1
  mux linear applied first

def block {shape : Shape} {library : Minidregg.Theory.BendClosureMachine.Library}
    (zero one : Nat) (rom : ROM shape library) (state : State shape) :
    Builder (Nat × State shape) := do
  let handled ← equalConstant one state.control.tag 4
  let q := state.control.quantity
  let function := state.control.a
  let argumentPointer := state.control.b
  let blank := Vector.replicate shape.wordBits zero
  let (valid,row) ← readHeap zero one state function
  let initial ← guard valid 15 (begin zero one state)
  let isClosure ← equalConstant one row.tag 3
  let isApplication ← equalConstant one row.tag 5
  let term ← emitOr isClosure isApplication
  let initial ← guard term 14 initial
  let (codeValid,code) ← readCode zero one rom row.first
  let closureInitial ← guard codeValid 12 initial
  /- Ordinary neutral spine fallback; the next unspine checks argument budget. -/
  let fallbackInitial ← select isClosure closureInitial initial
  let appTag ← constant 3 5
  let (original,fallback) ← allocate zero one rom fallbackInitial
    ⟨appTag,q,function,argumentPointer⟩
  let fallback ← go 5 function original fallback
  let oneLength ← constant shape.wordBits 1
  let args := prependRow zero (argument zero q argumentPointer)
    (Vector.replicate shape.argumentSlots (Vector.replicate (argumentBits shape) zero))
  let fallback := {fallback with state := {fallback.state with control :=
    {fallback.state.control with firstLength := oneLength,first := args}}}
  let mut result : Result shape := ⟨fallback,zero⟩
  let qDead ← equalConstant one q 0
  let qLive ← notBit one qDead
  /- Beta preserves binder quantity, including Q2 Data check. -/
  let binderDead ← equalConstant one code.quantity 0
  let quantityDifference ← emit (.xor qDead binderDead)
  let beta ← guard (← notBit one quantityDifference) 19 closureInitial
  let (environment,beta) ← bind zero one rom beta code.quantity argumentPointer row.second
  let beta ← counted one (← go 0 code.a environment beta)
  let isLambda ← equalConstant one code.tag 6
  result ← choose (← emit (.and isClosure isLambda)) beta result
  /- Projection checks live first, then actual pair, then reserves frames. -/
  let projection ← guard qLive 9 closureInitial
  let (argumentValid,pair) ← readHeap zero one state argumentPointer
  let projection ← guard argumentValid 15 projection
  let projection ← guard (← equalConstant one pair.tag 4) 11 projection
  let knownTag ← constant 3 2
  let projection ← push zero one projection
    (frameWord zero knownTag q pair.second blank)
  let firstQuantity ← fieldQuantity one pair.quantity q
  let projection ← push zero one projection
    (frameWord zero knownTag firstQuantity pair.first blank)
  let projection ← counted one (← go 0 code.a row.second projection)
  let isProjection ← equalConstant one code.tag 10
  result ← choose (← emit (.and isClosure isProjection)) projection result
  /- Match labels compare intern indices only under public names.Nodup. -/
  let matched ← guard qLive 9 closureInitial
  let (actual,matched) ← labelOf zero one rom argumentPointer matched
  let (wantedValid,_,_) ← readDefinition zero one rom code.a
  let matched ← guard wantedValid 16 matched
  let same ← equal one actual code.a
  let no ← push zero one matched (frameWord zero knownTag q argumentPointer blank)
  let no ← go 0 code.c row.second no
  let yes ← go 0 code.b row.second matched
  let matched ← counted one (← select same yes no)
  let isMatch ← equalConstant one code.tag 13
  result ← choose (← emit (.and isClosure isMatch)) matched result
  finishResult zero one handled state result

end Minidregg.Compiler.BendObliviousApply
