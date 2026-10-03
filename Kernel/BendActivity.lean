/- Source-owned persistent Bend activity state. Computing successors use the
actual bounded controller, never client-supplied checkpoint states. Effect
preparation/outcome proposals still require the native typed Plan/receipt join;
pure proposal construction grants no dispatch authority or durable admission.
-/
import Compiler.BendClosureContinuationCodec
import Compiler.DurableReceiverCodec
import Theory.BendClosureResponse

namespace Minidregg.Kernel.BendActivity
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler.BendClosureContinuationCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableReceiver
set_option autoImplicit false

structure Pending where
  /-- Exact shared identity of source transition, dispatch and expected outcome. -/
  identity : List UInt8
  nativeIntent : IntentRecord
  response : BendClosureResponse.ABI

structure Outcome where
  identity : List UInt8
  responseBytes : List UInt8
  /-- Retained actual admitted receipt bytes, not a worker assertion of success. -/
  receiptBytes : List UInt8

structure Record where
  checkpoint : Checkpoint
  ordinal : Nat
  segment : Nat
  priorSourceSteps : Nat
  pending : Option Pending
  lastOutcome : Option Outcome

def abiStream : StreamCodec BendClosureResponse.ABI :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun abi => (abi.falseCode, abi.trueCode, abi.emptyEnvironment, abi.continuation))
    (fun (f,t,e,c) => ⟨f,t,e,c⟩) (by intro abi; cases abi; rfl)

def pendingStream : StreamCodec Pending :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product Minidregg.Compiler.DurableReceiverCodec.intentStream abiStream))
    (fun pending => (pending.identity, pending.nativeIntent, pending.response))
    (fun (i,n,r) => ⟨i,n,r⟩) (by intro pending; cases pending; rfl)

def outcomeStream : StreamCodec Outcome :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream))
    (fun outcome => (outcome.identity, outcome.responseBytes, outcome.receiptBytes))
    (fun (i,r,c) => ⟨i,r,c⟩) (by intro outcome; cases outcome; rfl)

def recordStream : StreamCodec Record :=
  StreamCodec.xmap
    (StreamCodec.product checkpointStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.option pendingStream) (StreamCodec.option outcomeStream))))))
    (fun record => (record.checkpoint, record.ordinal, record.segment,
      record.priorSourceSteps, record.pending, record.lastOutcome))
    (fun (c,o,s,t,p,r) => ⟨c,o,s,t,p,r⟩) (by intro record; cases record; rfl)

def frame : List UInt8 := "DREGG.BEND.ACTIVITY/v1".toUTF8.toList

def framedStream : StreamCodec Record :=
  StreamCodec.xmap (StreamCodec.product bytesStream recordStream)
    (fun record => (frame, record)) Prod.snd (by intro record; rfl)

def encode (record : Record) : List UInt8 := framedStream.encode record

def decode (bytes : List UInt8) : Option Record := do
  let record ← framedStream.toLawful.decode bytes
  if encode record = bytes then some record else none

@[simp] theorem decode_encode (record : Record) : decode (encode record) = some record := by
  have roundtrip := framedStream.decodePrefix_encode record []
  simp only [List.append_nil] at roundtrip
  simp [decode, encode, StreamCodec.toLawful, roundtrip]

def start (binding : List UInt8) (generation : Nat) (limits : Limits)
    (library : Library) (entry : Nat) : Except Failure Record := do
  let state ← BendClosureMachine.start limits library entry
  .ok ⟨⟨encodeContext (executionContext binding limits library), generation, state⟩,
    0, 0, 0, none, none⟩

/-- No checkpoint parameter is accepted: the successor is actual run of the
retained predecessor. Pending external work cannot be bypassed by ticking. -/
def advance (limits : Limits) (library : Library) (ticks : Nat) (before : Record) :
    Option Record :=
  match before.pending with
  | some _ => none
  | none => some {before with ordinal := before.ordinal + 1, checkpoint := {before.checkpoint with state := run limits library ticks before.checkpoint.state}}

theorem advance_actual_run {limits : Limits} {library : Library} {ticks : Nat}
    {before after : Record} (accepted : advance limits library ticks before = some after) :
    after.checkpoint.state = run limits library ticks before.checkpoint.state ∧
    after.ordinal = before.ordinal + 1 ∧
    after.checkpoint.contextBytes = before.checkpoint.contextBytes ∧
    after.checkpoint.generation = before.checkpoint.generation := by
  unfold advance at accepted
  cases pending : before.pending with
  | some value => simp [pending] at accepted
  | none => simp only [pending, Option.some.injEq] at accepted; cases accepted; exact ⟨rfl,rfl,rfl,rfl⟩

/-- This candidate starts a distinct pure source segment after an external
response. Native receiving must first verify the exact current pending identity,
source-authorized outcome and phase CAS; raw receipt bytes are not that proof. -/
def resumeProposal (limits : Limits) (library : Library) (before : Record)
    (outcome : Outcome) : Option Record := do
  let pending ← before.pending
  if outcome.identity != pending.identity then none else do
    let bit ← BendClosureResponse.decodeResponse outcome.responseBytes
    match BendClosureResponse.resume limits library.program pending.response before.checkpoint.state bit with
    | .error _ => none
    | .ok resumed =>
      some {before with ordinal := before.ordinal + 1, segment := before.segment + 1, priorSourceSteps := before.priorSourceSteps + before.checkpoint.state.sourceSteps, checkpoint := {before.checkpoint with state := resumed.state}, pending := none, lastOutcome := some outcome}

/-- Every pure tick successor strictly consumes its predecessor ordinal. This
arithmetic fact supports, but does not replace, the native compare-and-swap. -/
theorem advance_no_same_ordinal {limits : Limits} {library : Library} {ticks : Nat}
    {before after : Record} (accepted : advance limits library ticks before = some after) :
    after.ordinal ≠ before.ordinal := by
  have changed := (advance_actual_run accepted).2.1
  omega

#assert_axioms decode_encode
#assert_axioms advance_actual_run
#assert_axioms advance_no_same_ordinal
end Minidregg.Kernel.BendActivity
