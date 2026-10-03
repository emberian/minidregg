/- Canonical checkpoints of the actual bounded Bend controller.
Every State field is retained, including administrative lookup/walk state.
Decoding is not source admission, authority, freshness, or private custody.
-/
import Theory.BendClosureMachine
import Compiler.Tower256ConcreteBackend
import Mathlib.Data.Char

namespace Minidregg.Compiler.BendClosureContinuationCodec
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

def quanCode : Quan → Nat
  | .Q0 => 0 | .Q1 => 1 | .Q2 => 2

def quanOf : Nat → Quan
  | 1 => .Q1 | 2 => .Q2 | _ => .Q0

@[simp] theorem quan_roundtrip (q : Quan) : quanOf (quanCode q) = q := by
  cases q <;> rfl

def quanStream : StreamCodec Quan :=
  StreamCodec.xmap StreamCodec.nat quanCode quanOf quan_roundtrip

def boolStream : StreamCodec Bool :=
  StreamCodec.xmap StreamCodec.nat (fun b => if b then 1 else 0)
    (fun n => n == 1) (by intro b; cases b <;> rfl)

def arrayStream {α : Type} (codec : StreamCodec α) : StreamCodec (Array α) :=
  StreamCodec.xmap (StreamCodec.list codec) Array.toList List.toArray
    (by intro values; simp)

def rowWire : Row → List Nat
  | .vacant => [0]
  | .nil => [1]
  | .environment a b => [2, a, b]
  | .closure a b => [3, a, b]
  | .pair q a b => [4, quanCode q, a, b]
  | .application q a b => [5, quanCode q, a, b]

def rowOf : List Nat → Row
  | [0] => .vacant
  | [1] => .nil
  | [2, a, b] => .environment a b
  | [3, a, b] => .closure a b
  | [4, q, a, b] => .pair (quanOf q) a b
  | [5, q, a, b] => .application (quanOf q) a b
  | _ => .vacant

theorem row_roundtrip (row : Row) : rowOf (rowWire row) = row := by
  cases row <;> simp [rowOf, rowWire]

def rowStream : StreamCodec Row :=
  StreamCodec.xmap (StreamCodec.list StreamCodec.nat) rowWire rowOf row_roundtrip

def heapStream : StreamCodec Heap :=
  StreamCodec.xmap (StreamCodec.product (arrayStream rowStream) StreamCodec.nat)
    (fun heap => (heap.rows, heap.used)) (fun wire => ⟨wire.1, wire.2⟩)
    (by intro heap; cases heap; rfl)

def frameWire : BendClosureMachine.Frame → List Nat
  | .function q a b => [0, quanCode q, a, b]
  | .argument q a => [1, quanCode q, a]
  | .knownArgument q a => [2, quanCode q, a]
  | .lett q a b => [3, quanCode q, a, b]
  | .first q a b => [4, quanCode q, a, b]
  | .second q a => [5, quanCode q, a]
  | .rewrite a b => [6, a, b]

def frameOf : List Nat → BendClosureMachine.Frame
  | [0, q, a, b] => .function (quanOf q) a b
  | [1, q, a] => .argument (quanOf q) a
  | [2, q, a] => .knownArgument (quanOf q) a
  | [3, q, a, b] => .lett (quanOf q) a b
  | [4, q, a, b] => .first (quanOf q) a b
  | [5, q, a] => .second (quanOf q) a
  | [6, a, b] => .rewrite a b
  | _ => .rewrite 0 0

theorem frame_roundtrip (frame : BendClosureMachine.Frame) : frameOf (frameWire frame) = frame := by
  cases frame <;> simp [frameOf, frameWire]

def frameStream : StreamCodec BendClosureMachine.Frame :=
  StreamCodec.xmap (StreamCodec.list StreamCodec.nat) frameWire frameOf frame_roundtrip

def failureCode : Failure → Nat
  | .arena .shape => 0
  | .arena .capacity => 1
  | .arena .word => 2
  | .arena .dangling => 3
  | .programCapacity => 4
  | .notData => 5
  | .argumentCapacity => 6
  | .callHead => 7
  | .caseArgument => 8
  | .liveArgument => 9
  | .caseNode => 10
  | .pairRequired => 11
  | .codePointer => 12
  | .continuationCapacity => 13
  | .functionRequired => 14
  | .heapPointer => 15
  | .labelPointer => 16
  | .labelRequired => 17
  | .notTerm => 18
  | .quantity => 19
  | .rewriteEvidence => 20
  | .unbound => 21
  | .unknownDefinition => 22

def failureOf : Nat → Failure
  | 0 => .arena .shape
  | 1 => .arena .capacity
  | 2 => .arena .word
  | 3 => .arena .dangling
  | 4 => .programCapacity
  | 5 => .notData
  | 6 => .argumentCapacity
  | 7 => .callHead
  | 8 => .caseArgument
  | 9 => .liveArgument
  | 10 => .caseNode
  | 11 => .pairRequired
  | 12 => .codePointer
  | 13 => .continuationCapacity
  | 14 => .functionRequired
  | 15 => .heapPointer
  | 16 => .labelPointer
  | 17 => .labelRequired
  | 18 => .notTerm
  | 19 => .quantity
  | 20 => .rewriteEvidence
  | 21 => .unbound
  | 22 => .unknownDefinition
  | _ => .codePointer

@[simp] theorem failure_roundtrip (failure : Failure) :
    failureOf (failureCode failure) = failure := by
  cases failure <;> try rfl
  case arena reason => cases reason <;> rfl

abbrev ControlWire := List Nat × List (Quan × Nat)

def controlWire : Control → ControlWire
  | .evaluate a b => ([0, a, b], [])
  | .lookup a b .evaluateValue => ([1, a, b], [])
  | .lookup a b (.walkArgument q c d e args) => ([2, a, b, quanCode q, c, d, e], args)
  | .returned a => ([3, a], [])
  | .apply q a b => ([4, quanCode q, a, b], [])
  | .unspine a b args => ([5, a, b], args)
  | .walk a b c args => ([6, a, b, c], args)
  | .classify a b c d args => ([7, a, b, c, d], args)
  | .complete a => ([8, a], [])
  | .refused failure => ([9, failureCode failure], [])
  | .reverseArguments a b remaining reversed =>
      ([10, a, b, remaining.length], remaining ++ reversed)
  | .installArguments a b args => ([11, a, b], args)

def controlOf : ControlWire → Control
  | ([0, a, b], []) => .evaluate a b
  | ([1, a, b], []) => .lookup a b .evaluateValue
  | ([2, a, b, q, c, d, e], args) => .lookup a b (.walkArgument (quanOf q) c d e args)
  | ([3, a], []) => .returned a
  | ([4, q, a, b], []) => .apply (quanOf q) a b
  | ([5, a, b], args) => .unspine a b args
  | ([6, a, b, c], args) => .walk a b c args
  | ([7, a, b, c, d], args) => .classify a b c d args
  | ([8, a], []) => .complete a
  | ([9, failure], []) => .refused (failureOf failure)
  | ([10, a, b, count], args) => .reverseArguments a b (args.take count) (args.drop count)
  | ([11, a, b], args) => .installArguments a b args
  | _ => .refused .codePointer

theorem control_roundtrip (control : Control) :
    controlOf (controlWire control) = control := by
  cases control <;> try simp [controlOf, controlWire, List.take_left, List.drop_left]
  case lookup index environment resume =>
    cases resume <;> simp [controlOf, controlWire, List.take_left, List.drop_left]

def controlStream : StreamCodec Control :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list StreamCodec.nat)
      (StreamCodec.list (StreamCodec.product quanStream StreamCodec.nat)))
    controlWire controlOf control_roundtrip

def stateStream : StreamCodec State :=
  StreamCodec.xmap
    (StreamCodec.product heapStream (StreamCodec.product (arrayStream boolStream)
      (StreamCodec.product (StreamCodec.list frameStream)
        (StreamCodec.product controlStream StreamCodec.nat))))
    (fun state => (state.heap, state.data, state.stack, state.control, state.sourceSteps))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2⟩)
    (by intro state; cases state; rfl)

def codeWire : Code → List Nat
  | .var index => [0, index]
  | .ref name => [1, name]
  | .ann value type => [2, value, type]
  | .lett q value body => [3, quanCode q, value, body]
  | .typ q => [4, quanCode q]
  | .all q domain body => [5, quanCode q, domain, body]
  | .lam q body => [6, quanCode q, body]
  | .app q function argument => [7, quanCode q, function, argument]
  | .sig q domain body => [8, quanCode q, domain, body]
  | .tup q first second => [9, quanCode q, first, second]
  | .prj handler => [10, handler]
  | .enu labels => [11, labels]
  | .lab label => [12, label]
  | .mat label yes no => [13, label, yes, no]
  | .efq  => [14]
  | .eql left right type => [15, left, right, type]
  | .rfl  => [16]
  | .rwt evidence motive body => [17, evidence, motive, body]

def codeOf : List Nat → Code
  | [0, index] => .var index
  | [1, name] => .ref name
  | [2, value, type] => .ann value type
  | [3, q, value, body] => .lett (quanOf q) value body
  | [4, q] => .typ (quanOf q)
  | [5, q, domain, body] => .all (quanOf q) domain body
  | [6, q, body] => .lam (quanOf q) body
  | [7, q, function, argument] => .app (quanOf q) function argument
  | [8, q, domain, body] => .sig (quanOf q) domain body
  | [9, q, first, second] => .tup (quanOf q) first second
  | [10, handler] => .prj handler
  | [11, labels] => .enu labels
  | [12, label] => .lab label
  | [13, label, yes, no] => .mat label yes no
  | [14] => .efq 
  | [15, left, right, type] => .eql left right type
  | [16] => .rfl 
  | [17, evidence, motive, body] => .rwt evidence motive body
  | _ => .efq

theorem code_roundtrip (code : Code) : codeOf (codeWire code) = code := by
  cases code <;> simp [codeOf, codeWire]

def codeStream : StreamCodec Code :=
  StreamCodec.xmap (StreamCodec.list StreamCodec.nat) codeWire codeOf code_roundtrip

def charStream : StreamCodec Char :=
  StreamCodec.xmap StreamCodec.nat Char.toNat Char.ofNat Char.ofNat_toNat

def stringStream : StreamCodec String :=
  StreamCodec.xmap (StreamCodec.list charStream) String.toList String.ofList
    (by intro value; exact String.ofList_toList)

/-- The context stores exact operational tables and bounds, plus the native
source-selected activity/policy binding. Hash equality is not substituted for
exact identity here. The authority of that native binding is checked elsewhere. -/
abbrev ExecutionContext := List UInt8 × Nat × Nat × Nat × Nat × Array Code ×
  Array String × Array (List String) × Array (Nat × Nat)

def machineSemanticsFrame : List UInt8 :=
  "DREGG.BEND.CLOSURE-MACHINE/microsteps-v2".toUTF8.toList ++ [0]

def executionContext (bindingBytes : List UInt8) (limits : Limits)
    (library : Library) : ExecutionContext :=
  (machineSemanticsFrame ++ bindingBytes, limits.heap.slots, limits.heap.wordBits, limits.frames, limits.arguments,
    library.program.code, library.program.names, library.program.enumerations,
    library.definitions)

def executionContextStream : StreamCodec ExecutionContext :=
  StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product (arrayStream codeStream)
        (StreamCodec.product (arrayStream stringStream)
          (StreamCodec.product (arrayStream (StreamCodec.list stringStream))
            (arrayStream (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))))

def encodeContext (context : ExecutionContext) : List UInt8 :=
  executionContextStream.encode context

theorem context_bytes_injective {left right : ExecutionContext}
    (same : encodeContext left = encodeContext right) : left = right := by
  have equality := congrArg
    (fun bytes => executionContextStream.decodePrefix (bytes ++ [])) same
  change executionContextStream.decodePrefix (executionContextStream.encode left ++ []) =
    executionContextStream.decodePrefix (executionContextStream.encode right ++ []) at equality
  rw [executionContextStream.decodePrefix_encode, executionContextStream.decodePrefix_encode] at equality
  exact congrArg Prod.fst (Option.some.inj equality)

/-- Exact context bytes must bind admitted Book/library, numeric/evaluator and
cost versions, bounds and activity identity. A current native receiver supplies
these expected bytes and the monotone generation; the checkpoint cannot mint
its own authorization, freshness, or current custody. -/
structure Checkpoint where
  contextBytes : List UInt8
  generation : Nat
  state : State
  deriving DecidableEq, Repr

def checkpointStream : StreamCodec Checkpoint :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat stateStream))
    (fun checkpoint => (checkpoint.contextBytes, checkpoint.generation, checkpoint.state))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro checkpoint; cases checkpoint; rfl)

def checkpointFrame : List UInt8 := "DREGG.BEND.CONTINUATION".toUTF8.toList ++ [1]

def framedStream : StreamCodec Checkpoint :=
  StreamCodec.xmap (StreamCodec.product bytesStream checkpointStream)
    (fun checkpoint => (checkpointFrame, checkpoint)) Prod.snd
    (by intro checkpoint; rfl)

def encode (checkpoint : Checkpoint) : List UInt8 := framedStream.encode checkpoint

def decode (bytes : List UInt8) : Option Checkpoint :=
  match framedStream.toLawful.decode bytes with
  | none => none
  | some checkpoint => if encode checkpoint = bytes then some checkpoint else none

@[simp] theorem decode_encode (checkpoint : Checkpoint) :
    decode (encode checkpoint) = some checkpoint := by
  have roundtrip := framedStream.decodePrefix_encode checkpoint []
  simp only [List.append_nil] at roundtrip
  simp [decode, encode, StreamCodec.toLawful, roundtrip]

theorem decode_canonical {bytes : List UInt8} {checkpoint : Checkpoint}
    (accepted : decode bytes = some checkpoint) : encode checkpoint = bytes := by
  unfold decode at accepted
  cases decoded : framedStream.toLawful.decode bytes with
  | none => simp [decoded] at accepted
  | some result =>
    simp only [decoded] at accepted
    split at accepted
    · cases accepted; assumption
    · cases accepted

theorem encode_injective {left right : Checkpoint}
    (same : encode left = encode right) : left = right := by
  have equality := congrArg decode same
  simpa using equality

/-- A bounded canonical decoder for a source-selected continuation coordinate.
This performs no world effect and does not authorize scheduling the result. -/
def restore (maximumBytes : Nat) (expectedContext : List UInt8)
    (expectedGeneration : Nat) (bytes : List UInt8) : Option State := do
  if bytes.length > maximumBytes then none else do
    let checkpoint ← decode bytes
    if checkpoint.contextBytes = expectedContext ∧ checkpoint.generation = expectedGeneration
    then some checkpoint.state else none

theorem restore_encode (checkpoint : Checkpoint) (maximumBytes : Nat)
    (fits : (encode checkpoint).length ≤ maximumBytes) :
    restore maximumBytes checkpoint.contextBytes checkpoint.generation
      (encode checkpoint) = some checkpoint.state := by
  simp [restore, fits, Nat.not_lt.mpr fits]

/-- Canonical persistence retains any already-established invariant over the
ENTIRE actual state. This does not manufacture a source simulation invariant. -/
theorem restore_preserves {checkpoint : Checkpoint} {maximumBytes : Nat}
    (fits : (encode checkpoint).length ≤ maximumBytes)
    (invariant : State → Prop) (valid : invariant checkpoint.state) :
    ∃ restored, restore maximumBytes checkpoint.contextBytes checkpoint.generation
      (encode checkpoint) = some restored ∧ invariant restored :=
  ⟨checkpoint.state, restore_encode checkpoint maximumBytes fits, valid⟩

/-- Exact serialized pause/resume law for every actual controller state and
both tick budgets, including unfinished lookup/walk and absorbing refusals. -/
theorem serialized_resume_exact (limits : Limits) (library : Library)
    (context : List UInt8) (generation first second : Nat) (initial : State)
    (maximumBytes : Nat)
    (fits : (encode ⟨context, generation, run limits library first initial⟩).length ≤ maximumBytes) :
    (restore maximumBytes context generation
      (encode ⟨context, generation, run limits library first initial⟩)).map
      (run limits library second) = some (run limits library (first + second) initial) := by
  rw [restore_encode _ maximumBytes fits]
  simp only [Option.map_some]
  rw [run_add]

#assert_axioms code_roundtrip
#assert_axioms context_bytes_injective
#assert_axioms row_roundtrip
#assert_axioms frame_roundtrip
#assert_axioms control_roundtrip
#assert_axioms decode_encode
#assert_axioms decode_canonical
#assert_axioms encode_injective
#assert_axioms restore_encode
#assert_axioms restore_preserves
#assert_axioms serialized_resume_exact
end Minidregg.Compiler.BendClosureContinuationCodec
