/- Physical codec for the actual Objective storage references. It matches
ObjectiveThunkNetwork's fixed layout and preserves every live frame/value field.
Inactive padding is ignored. Runtime tables (code, environments, record fields)
are separate fixed-capacity shared inputs, not secretly published ROM.
General full-state roundtrip/refinement is still a proof obligation. -/
import Compiler.ObjectiveDemandStorage
import Compiler.ObjectiveThunkNetwork
import Compiler.ObliviousBitCodec

namespace Minidregg.Compiler.ObjectiveDemandStateCodec
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendOpenRecursion
open ObjectiveDemandStorage
set_option autoImplicit false

abbrev Shape := ObjectiveThunkNetwork.Shape
def compatible (shape : Shape) : Bool := shape.fits && shape.payloadBits == 3+2*shape.wordBits

def bits (width value : Nat) : Array Bool := (ObliviousBitCodec.bits width value).toArray
def number (input : Array Bool) (offset width : Nat) : Nat :=
  (BitVec.ofBoolListLE ((input.extract offset (offset+width)).toList)).toNat

def valueData : ValueRef → Nat × Nat × Nat
  | .closure code environment => (0,code,environment)
  | .natural n => (1,n,0)
  | .boolean bit => (2,if bit then 1 else 0,0)
  | .label name => (3,name,0)
  | .record fields => (4,fields,0)
  | .specification metadata extension => (5,metadata,extension)
  | .prototype specification target => (6,specification,target)

def encodeValue (width : Nat) (value : ValueRef) : Option (Array Bool) :=
  let (tag,a,b) := valueData value
  if a < 2^width && b < 2^width then some (bits 3 tag ++ bits width a ++ bits width b) else none

def decodeValue (width : Nat) (input : Array Bool) (offset : Nat) : Option ValueRef :=
  let a := number input (offset+3) width
  let b := number input (offset+3+width) width
  match number input offset 3 with
  | 0 => some (.closure a b)
  | 1 => some (.natural a)
  | 2 => if a ≤ 1 then some (.boolean (a == 1)) else none
  | 3 => some (.label a)
  | 4 => some (.record a)
  | 5 => some (.specification a b)
  | 6 => some (.prototype a b)
  | _ => none

def encodeClosure (width : Nat) (origin : ClosureRef) : Option (Array Bool) :=
  if origin.code < 2^width && origin.environment < 2^width then
    some (bits width origin.code ++ bits width origin.environment ++ bits 3 0)
  else none

def decodeClosure (width : Nat) (input : Array Bool) (offset : Nat) : ClosureRef :=
  ⟨number input offset width,number input (offset+width) width⟩

def refusalCode : Refusal → Nat
  | .unbound => 0 | .missingCell => 1 | .missingField => 2
  | .wrongValue => 3 | .invalidUpdate => 4 | .capacity => 5
def refusalOf : Nat → Option Refusal
  | 0 => some .unbound | 1 => some .missingCell | 2 => some .missingField
  | 3 => some .wrongValue | 4 => some .invalidUpdate | 5 => some .capacity
  | _ => none

def primitiveCode : Primitive → Nat
  | .add => 0 | .multiply => 1 | .equal => 2 | .conjunction => 3
def primitiveOf : Nat → Option Primitive
  | 0 => some .add | 1 => some .multiply | 2 => some .equal | 3 => some .conjunction
  | _ => none

def encodeCell (shape : Shape) : CellRef → Option (Array Bool)
  | .suspended origin => do
    pure (bits 2 0 ++ (← encodeClosure shape.wordBits origin) ++ bits shape.payloadBits 0)
  | .evaluating origin => do
    pure (bits 2 1 ++ (← encodeClosure shape.wordBits origin) ++ bits shape.payloadBits 0)
  | .cached origin value => do
    pure (bits 2 2 ++ (← encodeClosure shape.wordBits origin) ++ (← encodeValue shape.wordBits value))

def decodeCell (shape : Shape) (input : Array Bool) (offset : Nat) : Option CellRef := do
  let origin := decodeClosure shape.wordBits input (offset+2)
  match number input offset 2 with
  | 0 => pure (.suspended origin)
  | 1 => pure (.evaluating origin)
  | 2 => pure (.cached origin (← decodeValue shape.wordBits input (offset+2+shape.payloadBits)))
  | _ => none

def frameData : FrameRef → Nat × Nat × Nat × Nat
  | .argument code environment => (0,code,environment,0)
  | .update address => (1,address,0,0)
  | .field name => (2,name,0,0)
  | .reflect => (3,0,0,0)
  | .metadata => (4,0,0,0)
  | .project => (5,0,0,0)
  | .extend fields environment => (6,fields,environment,0)
  | .condition zero successor environment => (7,zero,successor,environment)
  | .binaryLeft primitive right environment => (8,primitiveCode primitive,right,environment)
  | .binaryRight primitive _ => (9,primitiveCode primitive,0,0)

/-- Physical update tag0 is shared with the actual thunk graph; other tags
are shifted only where necessary, never inferred from semantic constructor order. -/
def physicalFrameTag (tag : Nat) : Nat := if tag == 0 then 1 else if tag == 1 then 0 else tag

def encodeFrame (shape : Shape) (frame : FrameRef) : Option (Array Bool) := do
  let (tag,a,b,c) := frameData frame
  if !([a,b,c].all (· < 2^shape.wordBits)) then none else do
    let payload ← match frame with
      | .binaryRight _ left => encodeValue shape.wordBits left
      | _ => some (bits shape.wordBits b ++ bits shape.wordBits c ++ bits 3 0)
    pure (bits 4 (physicalFrameTag tag) ++ bits shape.wordBits a ++ payload)

def decodeFrame (shape : Shape) (input : Array Bool) (offset : Nat) : Option FrameRef := do
  let a := number input (offset+4) shape.wordBits
  let b := number input (offset+4+shape.wordBits) shape.wordBits
  let c := number input (offset+4+2*shape.wordBits) shape.wordBits
  match number input offset 4 with
  | 0 => pure (.update a)
  | 1 => pure (.argument a b)
  | 2 => pure (.field a)
  | 3 => pure .reflect
  | 4 => pure .metadata
  | 5 => pure .project
  | 6 => pure (.extend a b)
  | 7 => pure (.condition a b c)
  | 8 => pure (.binaryLeft (← primitiveOf a) b c)
  | 9 => pure (.binaryRight (← primitiveOf a)
      (← decodeValue shape.wordBits input (offset+4+shape.wordBits)))
  | _ => none

def encodeControl (shape : Shape) : ControlRef → Option (Nat × Nat × Array Bool)
  | .enter address => if address < 2^shape.wordBits then some (0,address,bits shape.payloadBits 0) else none
  | .returned result => do pure (1,0,← encodeValue shape.wordBits result)
  | .evaluate code environment => do pure (2,0,← encodeClosure shape.wordBits ⟨code,environment⟩)
  | .blackhole address => if address < 2^shape.wordBits then some (3,address,bits shape.payloadBits 0) else none
  | .refused reason => some (4,refusalCode reason,bits shape.payloadBits 0)
  | .complete result => do pure (5,0,← encodeValue shape.wordBits result)

def decodeControl (shape : Shape) (input : Array Bool) : Option ControlRef := do
  let address := number input 4 shape.wordBits
  let payload := 4+3*shape.wordBits
  match number input 1 3 with
  | 0 => pure (.enter address)
  | 1 => pure (.returned (← decodeValue shape.wordBits input payload))
  | 2 =>
    let origin := decodeClosure shape.wordBits input payload
    pure (.evaluate origin.code origin.environment)
  | 3 => pure (.blackhole address)
  | 4 => pure (.refused (← refusalOf address))
  | 5 => pure (.complete (← decodeValue shape.wordBits input payload))
  | _ => none

def encode (shape : Shape) (state : StateRef) (suspended : Bool := false) : Option (Array Bool) := do
  if !compatible shape || state.heap.size > shape.heapSlots || state.stack.length > shape.stackSlots then none else do
    let (tag,address,payload) ← encodeControl shape state.control
    let mut out := #[suspended] ++ bits 3 tag ++ bits shape.wordBits address ++
      bits shape.wordBits state.heap.size ++ bits shape.wordBits state.stack.length ++ payload
    for index in [:shape.heapSlots] do
      out := out ++ (← match state.heap[index]? with
        | some cell => encodeCell shape cell | none => some (bits shape.cellBits 0))
    let frames := state.stack.reverse.toArray
    for index in [:shape.stackSlots] do
      out := out ++ (← match frames[index]? with
        | some frame => encodeFrame shape frame | none => some (bits shape.frameBits 0))
    pure out

def decode (shape : Shape) (input : Array Bool) : Option (StateRef × Bool) := do
  if !compatible shape || input.size != shape.inputCount then none else do
    let used := number input (4+shape.wordBits) shape.wordBits
    let frameCount := number input (4+2*shape.wordBits) shape.wordBits
    if used > shape.heapSlots || frameCount > shape.stackSlots then none else do
      let mut heap := #[]
      for index in [:used] do
        heap := heap.push (← decodeCell shape input (shape.headerBits+index*shape.cellBits))
      let mut stack := []
      for index in [:frameCount] do
        stack := (← decodeFrame shape input
          (shape.headerBits+shape.heapSlots*shape.cellBits+index*shape.frameBits)) :: stack
      pure (⟨heap,← decodeControl shape input,stack⟩,input[0]?.getD false)

def represents (shape : Shape) (tables : Tables) (depth : Nat) (input : Array Bool)
    (state : State) : Prop :=
  ∃ reference suspended, decode shape input = some (reference,suspended) ∧
    ObjectiveDemandStorage.decode tables depth reference = some state

end Minidregg.Compiler.ObjectiveDemandStateCodec

