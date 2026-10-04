/- Objective demand-machine thunk transitions in the shared Boolean DAG.
This is the concrete enter/update part of the new controller, not a second
source evaluator or a claim of full Objective dispatch. Every heap/stack row
is scanned; inactive padding is retained. Capacity suspension preserves the
entire semantic state and only sets the physical suspension bit. Payloads
are fixed-width encoded closure/value data; their source representation and
the general transition refinement remain explicit joins. -/
import Compiler.ObliviousWords

namespace Minidregg.Compiler.ObjectiveThunkNetwork
open ObliviousNetwork ObliviousWords
set_option autoImplicit false

structure Shape where
  wordBits : Nat
  payloadBits : Nat
  heapSlots : Nat
  stackSlots : Nat
  deriving Repr, DecidableEq

def Shape.cellBits (shape : Shape) : Nat := 2 + 2 * shape.payloadBits
def Shape.frameBits (shape : Shape) : Nat := 4 + shape.wordBits + shape.payloadBits
def Shape.headerBits (shape : Shape) : Nat := 1 + 3 + 3 * shape.wordBits + shape.payloadBits
def Shape.inputCount (shape : Shape) : Nat :=
  shape.headerBits + shape.heapSlots * shape.cellBits + shape.stackSlots * shape.frameBits

def Shape.fits (shape : Shape) : Bool :=
  3 ≤ shape.wordBits && shape.heapSlots < 2^shape.wordBits && shape.stackSlots < 2^shape.wordBits

/-- Layout: suspended; control tag; address/reason; heap length; stack length;
control payload; cell rows; frame rows. Control tags: enter0, returned1,
evaluate2, blackhole3, refused4, complete5. Cell tags: suspended0,
evaluating1,cached2. Frame update tag0. Origins and cached payloads occupy
separate cell fields, so update cannot overwrite provenance. -/
structure Wires (shape : Shape) where
  suspended : Nat
  control : Word 3
  address : Word shape.wordBits
  heapLength : Word shape.wordBits
  stackLength : Word shape.wordBits
  payload : Word shape.payloadBits
  heap : Vector (Word shape.cellBits) shape.heapSlots
  stack : Vector (Word shape.frameBits) shape.stackSlots

def inputWires (shape : Shape) : Wires shape :=
  ⟨0, inputs 3 1, inputs shape.wordBits 4,
    inputs shape.wordBits (4+shape.wordBits), inputs shape.wordBits (4+2*shape.wordBits),
    inputs shape.payloadBits (4+3*shape.wordBits),
    Vector.ofFn (fun row => inputs shape.cellBits (shape.headerBits+row.val*shape.cellBits)),
    Vector.ofFn (fun row => inputs shape.frameBits
      (shape.headerBits+shape.heapSlots*shape.cellBits+row.val*shape.frameBits))⟩

def slice {width : Nat} (count offset : Nat) (word : Word width) : Word count :=
  Vector.ofFn fun bit => word.toArray[offset+bit.val]?.getD 0

def replace {width count : Nat} (offset : Nat) (value : Word count) (word : Word width) : Word width :=
  Vector.ofFn fun bit => if offset ≤ bit.val && bit.val < offset+count then
    value.toArray[bit.val-offset]?.getD 0 else word[bit]

def flatten {shape : Shape} (state : Wires shape) : Array Nat :=
  #[state.suspended] ++ state.control.toArray ++ state.address.toArray ++
  state.heapLength.toArray ++ state.stackLength.toArray ++ state.payload.toArray ++
  state.heap.toArray.foldl (fun out row => out ++ row.toArray) #[] ++
  state.stack.toArray.foldl (fun out row => out ++ row.toArray) #[]

def conjunction (one : Nat) (bits : List Nat) : Builder Nat :=
  bits.foldlM (fun acc bit => emit (.and acc bit)) one

def disjunction (zero : Nat) (bits : List Nat) : Builder Nat :=
  bits.foldlM emitOr zero

/-- All physical side effects are constructed first, then selected as a whole.
A suspended result retains old heap/control/stack lengths and inactive rows. -/
def build (shape : Shape) : Builder Unit := do
  let old := inputWires shape
  let zero ← emit (.constant false)
  let one ← emit (.constant true)
  let isEnter ← equalConstant one old.control 0
  let isReturn ← equalConstant one old.control 1
  let blackhole ← equalConstant one old.control 3
  let refused ← equalConstant one old.control 4
  let complete ← equalConstant one old.control 5
  let terminal ← disjunction zero [old.suspended,blackhole,refused,complete]
  let (stackBorrow,top) ← decrement one old.stackLength
  let (stackAddressValid,topFrame) ← readRows zero one top old.stack
  let updateTag ← equalConstant one (slice 4 0 topFrame) 0
  let stackNonempty ← notBit one stackBorrow
  let update ← conjunction one [isReturn,stackNonempty,stackAddressValid,updateTag]
  let handled ← disjunction zero [terminal,isEnter,update]
  let live ← notBit one terminal
  let entering ← emit (.and live isEnter)
  let updating ← emit (.and live update)
  let address ← mux updating (slice shape.wordBits 4 topFrame) old.address
  let (physicalCell,cell) ← readRows zero one address old.heap
  let belowLength ← lessThan zero one address old.heapLength
  let present ← conjunction one [physicalCell,belowLength]
  let suspendedTag ← equalConstant one (slice 2 0 cell) 0
  let evaluatingTag ← equalConstant one (slice 2 0 cell) 1
  let cachedTag ← equalConstant one (slice 2 0 cell) 2
  let start ← conjunction one [entering,present,suspendedTag]
  let cached ← conjunction one [entering,present,cachedTag]
  let busy ← conjunction one [entering,present,evaluatingTag]
  let store ← conjunction one [updating,present,evaluatingTag]
  let recognizedCell ← disjunction zero [suspendedTag,evaluatingTag,cachedTag]
  let enterValid ← emit (.and present recognizedCell)
  let badEnter ← conjunction one [entering,← notBit one enterValid]
  let badUpdate ← conjunction one [updating,← notBit one (← emit (.and present evaluatingTag))]
  let (stackCarry,nextStackLength) ← increment one old.stackLength
  let room ← lessThan zero one old.stackLength (← constant shape.wordBits shape.stackSlots)
  let roomSafe ← conjunction one [room,← notBit one stackCarry]
  let capacity ← conjunction one [start,← notBit one roomSafe]
  let perform ← conjunction one [handled,live,← notBit one capacity]
  let cellEvaluating := replace 0 (← constant 2 1) cell
  let cellCached := replace (2+shape.payloadBits) old.payload (replace 0 (← constant 2 2) cell)
  let replacement ← mux store cellCached cellEvaluating
  let writeCell ← emit (.and perform (← emitOr start store))
  let heap ← writeRows one writeCell address replacement old.heap
  let frameZero ← constant shape.frameBits 0
  let updateFrame := replace 4 old.address frameZero
  let stack ← writeRows one (← emit (.and perform start)) old.stackLength updateFrame old.stack
  let mut control := old.control
  control ← mux start (← constant 3 2) control
  control ← mux cached (← constant 3 1) control
  control ← mux busy (← constant 3 3) control
  control ← mux (← emitOr badEnter badUpdate) (← constant 3 4) control
  let mut resultAddress := old.address
  resultAddress ← mux badEnter (← constant shape.wordBits 1) resultAddress
  resultAddress ← mux badUpdate (← constant shape.wordBits 4) resultAddress
  let mut payload := old.payload
  payload ← mux start (slice shape.payloadBits 2 cell) payload
  payload ← mux cached (slice shape.payloadBits (2+shape.payloadBits) cell) payload
  let stackLength ← mux start nextStackLength (← mux updating top old.stackLength)
  let candidate : Wires shape :=
    ⟨← emitOr old.suspended capacity, ← mux perform control old.control,
     ← mux perform resultAddress old.address,old.heapLength,
     ← mux perform stackLength old.stackLength,← mux perform payload old.payload,heap,stack⟩
  modify fun network => {network with outputs:=#[handled] ++ flatten candidate}

def network (shape : Shape) : Option Network :=
  if shape.fits then
    let result := (build shape).run {inputCount:=shape.inputCount}
    if result.2.valid then some result.2 else none
  else none

end Minidregg.Compiler.ObjectiveThunkNetwork

