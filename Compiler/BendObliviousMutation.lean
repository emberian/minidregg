/- Transactional mutation primitives for the fixed Bend controller.
Each primitive emits its entire fixed circuit. Failure is accumulated in wires;
finish restores the original state and changes only the refusal control, matching
the actual StateT State (Except Failure) rollback. Packed-state well-formedness
discharges word-width/array-shape checks; dynamic capacity and backward-pointer
checks remain gates. General primitive refinement remains to be proved. -/
import Compiler.BendObliviousProgram

namespace Minidregg.Compiler.BendObliviousMutation
open ObliviousNetwork ObliviousWords BendObliviousState
open BendObliviousAccess BendObliviousAdministrative BendObliviousProgram
set_option autoImplicit false

structure Trial (shape : Shape) where
  state : State shape
  valid : Nat
  failure : Word 5

def begin {shape : Shape} (zero one : Nat) (state : State shape) : Trial shape :=
  ⟨state,one,Vector.replicate 5 zero⟩

def guard {shape : Shape} (condition : Nat) (reason : Nat) (trial : Trial shape) :
    Builder (Trial shape) := do
  let error ← constant 5 reason
  let failure ← mux trial.valid error trial.failure
  let valid ← emit (.and trial.valid condition)
  pure ⟨trial.state,valid,failure⟩

def select {shape : Shape} (selector : Nat) (yes no : Trial shape) : Builder (Trial shape) := do
  pure ⟨← muxState selector yes.state no.state,
    ← emitMux selector yes.valid no.valid,
    ← mux selector yes.failure no.failure⟩

def finish {shape : Shape} (original : State shape) (trial : Trial shape) :
    Builder (State shape) := do
  let tag ← constant 4 9
  let rollback := {original with control := {original.control with tag,failure := trial.failure}}
  muxState trial.valid trial.state rollback

def rowWord {shape : Shape} (zero : Nat) (row : RowView shape) : Word (rowBits shape) :=
  Vector.ofFn fun bit =>
    if bit.val < 3 then row.tag.toArray[bit.val]?.getD zero
    else if bit.val < 5 then row.quantity.toArray[bit.val-3]?.getD zero
    else if bit.val < 5+shape.wordBits then row.first.toArray[bit.val-5]?.getD zero
    else row.second.toArray[bit.val-(5+shape.wordBits)]?.getD zero

def dataRows {shape : Shape} (state : State shape) : Vector (Word 1) shape.heapSlots :=
  Vector.ofFn fun row => Vector.replicate 1 state.data[row]

def readData {shape : Shape} (zero one : Nat) (state : State shape)
    (pointer : Word shape.wordBits) : Builder Nat := do
  let (_,value) ← readRows zero one pointer (dataRows state)
  pure value[0]

def allocate {shape : Shape} {library : Minidregg.Theory.BendClosureMachine.Library}
    (zero one : Nat) (rom : ROM shape library) (trial : Trial shape)
    (row : RowView shape) : Builder (Word shape.wordBits × Trial shape) := do
  let state := trial.state
  let closure ← equalConstant one row.tag 3
  let pair ← equalConstant one row.tag 4
  let nil ← equalConstant one row.tag 1
  let environment ← equalConstant one row.tag 2
  let application ← equalConstant one row.tag 5
  /- Actual allocate computes a closure's code qualification BEFORE arena checks. -/
  let (codeValid,code) ← readCode zero one rom row.first
  let label ← equalConstant one code.tag 12
  let reflexive ← equalConstant one code.tag 16
  let codeData ← emit (.xor label reflexive)
  let firstData ← readData zero one state row.first
  let secondData ← readData zero one state row.second
  let dead ← equalConstant one row.quantity 0
  let allowedFirst ← emitOr dead firstData
  let pairData ← emit (.and allowedFirst secondData)
  let qualifies ← emitMux pair pairData zero
  let qualifies ← emitMux closure codeData qualifies
  let codeOK ← emitMux closure codeValid one
  let checked ← guard codeOK 12 trial
  let capacity ← constant (shape.wordBits+1) shape.heapSlots
  let room ← lessThan zero one state.used capacity
  let checked ← guard room 1 checked
  let firstPast ← lessThan zero one (extend zero row.first) state.used
  let secondPast ← lessThan zero one (extend zero row.second) state.used
  let bothPast ← emit (.and firstPast secondPast)
  /- C=2^w is representable by the separate read-valid bit, not a truncated
  constant comparator. codeValid already means first is a live ROM index. -/
  let closurePast ← emit (.and codeValid secondPast)
  let ordinary ← emit (.xor environment pair)
  let ordinary ← emit (.xor ordinary application)
  let past ← emit (.and ordinary bothPast)
  let past ← emitMux closure closurePast past
  let past ← emitOr nil past
  let checked ← guard past 3 checked
  let pointer := slice zero state.used 0 shape.wordBits
  let rows ← writeRows one one pointer (rowWord zero row) state.heap
  let cacheRows ← writeRows one one pointer (Vector.replicate 1 qualifies) (dataRows state)
  let data := Vector.ofFn fun index => cacheRows[index][0]
  let (_,used) ← increment one state.used
  pure (pointer,{checked with state := {state with heap := rows,data,used}})

def bind {shape : Shape} {library : Minidregg.Theory.BendClosureMachine.Library}
    (zero one : Nat) (rom : ROM shape library) (trial : Trial shape)
    (quantity : Word 2) (value environment : Word shape.wordBits) :
    Builder (Word shape.wordBits × Trial shape) := do
  let duplicated ← equalConstant one quantity 2
  let data ← readData zero one trial.state value
  let acceptable ← emitMux duplicated data one
  let checked ← guard acceptable 5 trial
  let tag ← constant 3 2
  let q ← constant 2 0
  allocate zero one rom checked ⟨tag,q,value,environment⟩

def closure {shape : Shape} {library : Minidregg.Theory.BendClosureMachine.Library}
    (zero one : Nat) (rom : ROM shape library) (trial : Trial shape)
    (code environment : Word shape.wordBits) : Builder (Word shape.wordBits × Trial shape) := do
  let tag ← constant 3 3
  let q ← constant 2 0
  allocate zero one rom trial ⟨tag,q,code,environment⟩

def push {shape : Shape} (zero one : Nat) (trial : Trial shape)
    (frame : Word (frameBits shape)) : Builder (Trial shape) := do
  let capacity ← constant shape.wordBits shape.frameSlots
  let room ← lessThan zero one trial.state.stackLength capacity
  let checked ← guard room 13 trial
  let (_,length) ← increment one trial.state.stackLength
  pure {checked with state := {trial.state with
    stack := prependRow zero frame trial.state.stack,stackLength := length}}

def frameWord {shape : Shape} (zero : Nat) (tag : Word 3) (quantity : Word 2)
    (first second : Word shape.wordBits) : Word (frameBits shape) :=
  Vector.ofFn fun bit =>
    if bit.val < 3 then tag.toArray[bit.val]?.getD zero
    else if bit.val < 5 then quantity.toArray[bit.val-3]?.getD zero
    else if bit.val < 5+shape.wordBits then first.toArray[bit.val-5]?.getD zero
    else second.toArray[bit.val-(5+shape.wordBits)]?.getD zero

def go {shape : Shape} (tag : Nat) (a b : Word shape.wordBits) (trial : Trial shape) :
    Builder (Trial shape) := do
  let tag ← constant 4 tag
  pure {trial with state := {trial.state with control := {trial.state.control with tag,a,b}}}

/-- Counter carry must be ruled out by the public admitted run bound. A later
physical-capacity flag will expose it; it cannot be called a source refusal. -/
def sourceStep {shape : Shape} (one : Nat) (trial : Trial shape) :
    Builder (Nat × Trial shape) := do
  let (carry,count) ← increment one trial.state.sourceSteps
  pure (carry,{trial with state := {trial.state with sourceSteps := count}})

end Minidregg.Compiler.BendObliviousMutation
