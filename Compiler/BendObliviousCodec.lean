/- Fixed-bit codec for the ACTUAL Bend closure State used by the controller.
It preserves all operational fields and the private source counter. Unlike the
persistent canonical byte codec, inactive union fields may contain arbitrary
bits; decoding ignores them. Invalid active tags/quantities/lengths refuse.
General roundtrip and circuit simulation proofs remain explicit obligations. -/
import Compiler.BendObliviousState
import Compiler.BendClosurePacking
import Compiler.BendClosureContinuationCodec
import Init.Data.BitVec.Basic

namespace Minidregg.Compiler.BendObliviousCodec
open Minidregg.Theory BendTT BendClosureArena
open BendObliviousState
set_option autoImplicit false

def bits := BendClosurePacking.natBits

structure ControlData where
  tag : Nat
  quantity : Quan := .Q0
  failure : Nat := 0
  a : Nat := 0
  b : Nat := 0
  c : Nat := 0
  d : Nat := 0
  e : Nat := 0
  first : List (Quan × Nat) := []
  second : List (Quan × Nat) := []

def controlData : BendClosureMachine.Control → ControlData
  | .evaluate a b => {tag := 0, a, b}
  | .lookup a b .evaluateValue => {tag := 1, a, b}
  | .lookup a b (.walkArgument quantity c d e first) => {tag := 2, quantity, a,b,c,d,e,first}
  | .returned a => {tag := 3,a}
  | .apply quantity a b => {tag := 4,quantity,a,b}
  | .unspine a b first => {tag := 5,a,b,first}
  | .walk a b c first => {tag := 6,a,b,c,first}
  | .classify a b c d first => {tag := 7,a,b,c,d,first}
  | .complete a => {tag := 8,a}
  | .refused reason => {tag := 9,failure := BendClosureContinuationCodec.failureCode reason}
  | .reverseArguments a b first second => {tag := 10,a,b,first,second}
  | .installArguments a b first => {tag := 11,a,b,first}

def encodeArgument (width : Nat) (argument : Quan × Nat) : List Bool :=
  bits 2 (BendClosureContinuationCodec.quanCode argument.1) ++ bits width argument.2

def padArguments (shape : Shape) (args : List (Quan × Nat)) : List Bool :=
  ((args ++ List.replicate (shape.argumentSlots - args.length) (.Q0,0)).take shape.argumentSlots).
    flatMap (encodeArgument shape.wordBits)

def encodeControl (shape : Shape) (control : BendClosureMachine.Control) : Option (List Bool) := do
  let c := controlData control
  if !([c.a,c.b,c.c,c.d,c.e].all (· < 2^shape.wordBits)) ||
      c.first.length > shape.argumentSlots || c.second.length > shape.argumentSlots ||
      !((c.first ++ c.second).all (fun arg => arg.2 < 2^shape.wordBits)) then none
  else some (bits 4 c.tag ++ bits 2 (BendClosureContinuationCodec.quanCode c.quantity) ++ bits 5 c.failure ++
    [c.a,c.b,c.c,c.d,c.e,c.first.length,c.second.length].flatMap (bits shape.wordBits) ++
    padArguments shape c.first ++ padArguments shape c.second)

def frameData : BendClosureMachine.Frame → Nat × Quan × Nat × Nat
  | .function q a b => (0,q,a,b)
  | .argument q a => (1,q,a,0)
  | .knownArgument q a => (2,q,a,0)
  | .lett q a b => (3,q,a,b)
  | .first q a b => (4,q,a,b)
  | .second q a => (5,q,a,0)
  | .rewrite a b => (6,.Q0,a,b)

def encodeFrame (width : Nat) (frame : BendClosureMachine.Frame) : List Bool :=
  let (tag,q,a,b) := frameData frame
  bits 3 tag ++ bits 2 (BendClosureContinuationCodec.quanCode q) ++ bits width a ++ bits width b

def encode (shape : Shape) (state : BendClosureMachine.State) : Option (Array Bool) := do
  if !shape.valid || state.heap.rows.size != shape.heapSlots ||
      state.heap.used > shape.heapSlots || state.data.size != shape.heapSlots ||
      !(state.heap.rows.all (fun row => row.fits (2^shape.wordBits))) ||
      state.stack.length > shape.frameSlots ||
      !(state.stack.all fun frame =>
        let (_,_,a,b) := frameData frame
        a < 2^shape.wordBits && b < 2^shape.wordBits) ||
      state.sourceSteps ≥ 2^shape.sourceCountBits then none
  else do
    let control ← encodeControl shape state.control
    let heap := state.heap.rows.toList.flatMap fun row =>
      BendClosurePacking.bits (BendClosurePacking.pack shape.wordBits row)
    let stack := ((state.stack ++ List.replicate (shape.frameSlots - state.stack.length)
      (.rewrite 0 0)).take shape.frameSlots).flatMap (encodeFrame shape.wordBits)
    some ((heap ++ bits (shape.wordBits+1) state.heap.used ++ state.data.toList ++
      stack ++ bits shape.wordBits state.stack.length ++ control ++
      bits shape.sourceCountBits state.sourceSteps).toArray)

abbrev Read := StateT (List Bool) Option

def takeBits (width : Nat) : Read (List Bool) := do
  let input ← get
  if width > input.length then failure
  else set (input.drop width); pure (input.take width)

def nat (width : Nat) : Read Nat := do
  let value ← takeBits width
  pure (BitVec.ofBoolListLE value).toNat

def quantity : Read Quan := do
  match ← nat 2 with
  | 0 => pure .Q0 | 1 => pure .Q1 | 2 => pure .Q2 | _ => failure

def row (width : Nat) : Read Row := do
  let tag ← nat 3
  let q ← quantity
  let first ← nat width
  let second ← nat width
  match tag with
  | 0 => pure .vacant | 1 => pure .nil
  | 2 => pure (.environment first second)
  | 3 => pure (.closure first second)
  | 4 => pure (.pair q first second)
  | 5 => pure (.application q first second)
  | _ => failure

def frame (width : Nat) : Read BendClosureMachine.Frame := do
  let tag ← nat 3
  let q ← quantity
  let first ← nat width
  let second ← nat width
  match tag with
  | 0 => pure (.function q first second)
  | 1 => pure (.argument q first)
  | 2 => pure (.knownArgument q first)
  | 3 => pure (.lett q first second)
  | 4 => pure (.first q first second)
  | 5 => pure (.second q first)
  | 6 => pure (.rewrite first second)
  | _ => failure

def argument (width : Nat) : Read (Quan × Nat) := do
  pure (← quantity, ← nat width)

def repeatRead {α : Type} (count : Nat) (read : Read α) : Read (List α) :=
  (List.range count).mapM fun _ => read

def control (shape : Shape) : Read BendClosureMachine.Control := do
  let tag ← nat 4
  let q ← quantity
  let failureCode ← nat 5
  let a ← nat shape.wordBits
  let b ← nat shape.wordBits
  let c ← nat shape.wordBits
  let d ← nat shape.wordBits
  let e ← nat shape.wordBits
  let firstLength ← nat shape.wordBits
  let secondLength ← nat shape.wordBits
  let first ← repeatRead shape.argumentSlots (argument shape.wordBits)
  let second ← repeatRead shape.argumentSlots (argument shape.wordBits)
  if firstLength > shape.argumentSlots || secondLength > shape.argumentSlots then failure
  else
    let first := first.take firstLength
    let second := second.take secondLength
    match tag with
    | 0 => pure (.evaluate a b)
    | 1 => pure (.lookup a b .evaluateValue)
    | 2 => pure (.lookup a b (.walkArgument q c d e first))
    | 3 => pure (.returned a)
    | 4 => pure (.apply q a b)
    | 5 => pure (.unspine a b first)
    | 6 => pure (.walk a b c first)
    | 7 => pure (.classify a b c d first)
    | 8 => pure (.complete a)
    | 9 => if failureCode ≤ 22 then pure (.refused (BendClosureContinuationCodec.failureOf failureCode)) else failure
    | 10 => pure (.reverseArguments a b first second)
    | 11 => pure (.installArguments a b first)
    | _ => failure

def readState (shape : Shape) : Read BendClosureMachine.State := do
  let rows ← repeatRead shape.heapSlots (row shape.wordBits)
  let used ← nat (shape.wordBits + 1)
  let data ← takeBits shape.heapSlots
  let frames ← repeatRead shape.frameSlots (frame shape.wordBits)
  let stackLength ← nat shape.wordBits
  let control ← control shape
  let sourceSteps ← nat shape.sourceCountBits
  if used > shape.heapSlots || stackLength > shape.frameSlots then failure
  else pure ⟨⟨rows.toArray,used⟩,data.toArray,frames.take stackLength,control,sourceSteps⟩

def decode (shape : Shape) (input : Array Bool) : Option BendClosureMachine.State := do
  if !shape.valid then none else do
    let (state, rest) ← (readState shape).run input.toList
    if rest.isEmpty then some state else none

end Minidregg.Compiler.BendObliviousCodec
