/- Initial Objective code-dispatch tranche over the SAME private-capable
fixed code-table layout. Literal Nat/Bool/label and lambda return, plus empty
return completion, compose with the real thunk enter/update graph. Remaining
opcodes explicitly return handled=false. Code rows are input wires and every
fixed row is scanned; public constant-program specialization is optional.
Every table region of the layout (code rows, code fields, names, environments,
record fields) is an input and is carried to the next tick, so a decoder of the
output reads the same tables the graph executed. -/
import Compiler.ObjectiveDemandLayout

namespace Minidregg.Compiler.ObjectiveDemandLiteralNetwork
open ObliviousNetwork ObliviousWords ObjectiveThunkNetwork ObjectiveDemandLayout
set_option autoImplicit false

def valuePayload (shape : Shape) (tag : Word 3) (a b : Word shape.wordBits) : Word shape.payloadBits :=
  Vector.ofFn fun bit =>
    if bit.val < 3 then tag.toArray[bit.val]?.getD 0
    else if bit.val < 3+shape.wordBits then a.toArray[bit.val-3]?.getD 0
    else b.toArray[bit.val-3-shape.wordBits]?.getD 0

def build (shape : Shape) (codeSlots tableBits : Nat) : Builder Unit := do
  ObjectiveThunkNetwork.build shape
  let thunk ← get
  let old := inputWires shape
  let zero ← emit (.constant false)
  let one ← emit (.constant true)
  let codeRows : Vector (Word (rowBits shape)) codeSlots :=
    Vector.ofFn fun row => inputs (rowBits shape) (shape.inputCount+row.val*rowBits shape)
  let codePointer := slice shape.wordBits 0 old.payload
  let environment := slice shape.wordBits shape.wordBits old.payload
  let (codePresent,code) ← readRows zero one codePointer codeRows
  let opcode := slice ObjectiveDemandPackedCode.tagBits 0 code
  let a := slice shape.wordBits
    (ObjectiveDemandPackedCode.tagBits+ObjectiveDemandPackedCode.primitiveBits) code
  let isNat ← equalConstant one opcode 10
  let isBool ← equalConstant one opcode 11
  let isLabel ← equalConstant one opcode 12
  let isLambda ← equalConstant one opcode 1
  let boolCanonical ← emitOr (← equalConstant one a 0) (← equalConstant one a 1)
  let boolReady ← emit (.and isBool boolCanonical)
  let supported ← disjunction zero [isNat,boolReady,isLabel,isLambda]
  let live ← notBit one old.suspended
  let evaluating ← equalConstant one old.control 2
  let dispatch ← conjunction one [live,evaluating,codePresent,supported]
  let finish ← conjunction one [live,← equalConstant one old.control 1,
    ← equalConstant one old.stackLength 0]
  let selected ← emitOr dispatch finish
  let zeroWord ← constant shape.wordBits 0
  let natPayload := valuePayload shape (← constant 3 1) a zeroWord
  let boolPayload := valuePayload shape (← constant 3 2) a zeroWord
  let labelPayload := valuePayload shape (← constant 3 3) a zeroWord
  let closurePayload := valuePayload shape (← constant 3 0) a environment
  let mut payload := natPayload
  payload ← mux boolReady boolPayload payload
  payload ← mux isLabel labelPayload payload
  payload ← mux isLambda closurePayload payload
  payload ← mux dispatch payload old.payload
  let tag ← mux finish (← constant 3 5) (← constant 3 1)
  let candidate := flatten {old with control:=tag,payload}
  let mut output := #[← emitOr (thunk.outputs[0]?.getD zero) selected]
  for index in [:shape.inputCount] do
    let before := thunk.outputs[index+1]?.getD zero
    let after := candidate[index]?.getD zero
    output := output.push (← if before == after then pure before else emitMux selected after before)
  for index in [:tableBits] do
    output := output.push (shape.inputCount+index)
  modify fun network => {network with outputs:=output}

def network (layout : Layout) : Option Network :=
  if layout.fits then
    let result := (build layout.shape layout.codeSlots layout.tableBits).run
      {inputCount:=layout.inputCount}
    if result.2.valid then some result.2 else none
  else none

end Minidregg.Compiler.ObjectiveDemandLiteralNetwork

