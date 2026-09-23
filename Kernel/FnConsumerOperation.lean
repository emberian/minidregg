/-
Bounded local E1 consumer operation. The application/operation pair selects a
stable transaction nonce independent of fn source identity. The ordinary native
resource receiver remains the admission and atomic CAS owner. This module only
authors its command and interprets its historical signed event.

The first profile has one local consumer subject and one pre-birthed content
resource. The trusted fn verdict reference is an input from an explicit test
adapter until fn's native historical verdict connector is available.
-/
import Kernel.FnEvidence
import Kernel.NativeHost
import Kernel.ContentResource

namespace Minidregg.Kernel.FnConsumerOperation

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

structure Provenance where
  history : List UInt8
  incarnation : List UInt8
  sourceIdentity : List UInt8
  fnVerdictRef : List UInt8
  deriving DecidableEq, Repr

structure Report where
  application : List UInt8
  operation : List UInt8
  provenance : Provenance
  package : List UInt8
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  expectedAuthorityRoot : Digest
  expectedTargetRoot : Digest
  deriving Repr

structure Reply where
  application : List UInt8
  operation : List UInt8
  sourceIdentity : List UInt8
  miniReceipt : Receipt
  deriving DecidableEq, Repr

structure Binding where
  application : List UInt8
  operation : List UInt8
  provenance : Provenance
  package : List UInt8
  reply : Reply
  deriving DecidableEq, Repr

def provenanceStream : StreamCodec Provenance :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream bytesStream)))
    (fun value => (value.history, value.incarnation,
      value.sourceIdentity, value.fnVerdictRef))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

def replyStream : StreamCodec Reply :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream receiptStream)))
    (fun value => (value.application, value.operation,
      value.sourceIdentity, value.miniReceipt))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

def replyCodec : LawfulCodec Reply :=
  NativeHostCodec.framed "DREGG/FN/APPLICATION-REPLY/v1".toUTF8.toList replyStream

def bindingStream : StreamCodec Binding :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product provenanceStream (StreamCodec.product bytesStream replyStream))))
    (fun value => (value.application, value.operation, value.provenance,
      value.package, value.reply))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def bindingCodec : LawfulCodec Binding :=
  NativeHostCodec.framed "DREGG/FN/OPERATION-BINDING/v1".toUTF8.toList bindingStream

def maxNameBytes : Nat := 64
def maxVerdictRefBytes : Nat := 256
def maxBindingBytes : Nat := 18432

def validName (value : List UInt8) : Bool :=
  !value.isEmpty && value.length ≤ maxNameBytes

def checkReport (report : Report) : Except String Unit := do
  unless validName report.application && validName report.operation &&
      validName report.provenance.history && validName report.provenance.incarnation &&
      validName report.provenance.sourceIdentity do
    throw "empty or oversized consumer identity"
  unless !report.provenance.fnVerdictRef.isEmpty &&
      report.provenance.fnVerdictRef.length ≤ maxVerdictRefBytes do
    throw "missing or oversized fn verdict reference"
  unless report.package.length ≤ FnEvidenceCodec.maxPackageBytes do
    throw "Mini report package exceeds P0 bound"

def operationPreimage (domain semantics : Digest) (application operation : List UInt8) :
    List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product bytesStream bytesStream))).encode
    (domain, semantics, application, operation)

/-- Source identity is deliberately absent. The even tag is reserved for a
unique application effect; odd nonces are for distinct conflict evidence. -/
def operationNonce (domain semantics : Digest) (application operation : List UInt8) : Nat :=
  2 * (Sp800185Cshake256.hash "DREGG.FN.OPERATION/v1".toUTF8.toList
    (operationPreimage domain semantics application operation)).digest.value

def conflictNonce (domain semantics : Digest) (report : Report) : Nat :=
  2 * (Sp800185Cshake256.hash "DREGG.FN.CONFLICT/v1".toUTF8.toList
    (operationPreimage domain semantics report.application report.operation ++
      provenanceStream.encode report.provenance)).digest.value + 1

theorem operationNonce_ne_conflictNonce (domain semantics : Digest)
    (report : Report) :
    operationNonce domain semantics report.application report.operation ≠
      conflictNonce domain semantics report := by
  unfold operationNonce conflictNonce
  omega

def operationAtom (domain semantics : Digest) (application operation : List UInt8) : AtomId :=
  ⟨⟨operationNonce domain semantics application operation⟩⟩

def replyAtom (domain semantics : Digest) (application operation : List UInt8) : AtomId :=
  ⟨⟨operationNonce domain semantics application operation + 1⟩⟩

def conflictAtom (domain semantics : Digest) (report : Report) : AtomId :=
  ⟨⟨conflictNonce domain semantics report⟩⟩

theorem operationAtom_ne_replyAtom (domain semantics : Digest)
    (application operation : List UInt8) :
    operationAtom domain semantics application operation ≠
      replyAtom domain semantics application operation := by
  intro equal
  have n : operationNonce domain semantics application operation =
    operationNonce domain semantics application operation + 1 := by
    exact congrArg (fun id => id.digest.value) equal
  omega

/-- The existing native transaction-id function is the only marker owner. Its
choice depends on the local consumer subject and stable operation nonce. -/
def marker (domain semantics : Digest) (subject : SubjectId) (nonce : Nat) : Digest :=
  DeclaredResourceController.transactionId domain semantics
    ⟨subject, ⟨0⟩, nonce, []⟩

def bindingCommand (domain semantics : Digest) (report : Report)
    (receipt : Receipt) : Except String DeclaredResourceController.Command := do
  let reply : Reply := ⟨report.application, report.operation,
    report.provenance.sourceIdentity, receipt⟩
  let binding : Binding := ⟨report.application, report.operation,
    report.provenance, report.package, reply⟩
  let bytes := bindingCodec.encode binding
  unless bytes.length ≤ maxBindingBytes do throw "consumer binding exceeds bound"
  let actions : List ContentResource.Action :=
    [.createAtom (operationAtom domain semantics report.application report.operation)
      (.inlineObject ⟨1⟩) bytes,
     .createAtom (replyAtom domain semantics report.application report.operation)
      (.inlineObject ⟨2⟩) (replyCodec.encode reply)]
  pure ⟨report.subject, report.expectedAuthorityRoot,
    operationNonce domain semantics report.application report.operation,
    [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
      .content ⟨actions⟩, none⟩]⟩

def conflictCommand (domain semantics : Digest) (report : Report) :
    DeclaredResourceController.Command :=
  ⟨report.subject, report.expectedAuthorityRoot,
   conflictNonce domain semantics report,
   [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
     .content ⟨[.createAtom (conflictAtom domain semantics report)
       (.inlineObject ⟨3⟩) (provenanceStream.encode report.provenance)]⟩, none⟩]⟩

inductive Decision where
  | fresh (command : DeclaredResourceController.Command) (reply : Reply)
  | repeated (reply : Reply)
  | conflict (command : DeclaredResourceController.Command)
  | refused (detail : String)
  deriving Repr

/-- Inspect the original accepted call, rather than a mutable current atom.
The prior reply remains recoverable from the durable accepted event history. -/
def originalBinding (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option Binding := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  match command.targets with
  | [target] =>
      match target.payload with
      | .content content =>
          match content.actions with
          | [.createAtom atom (.inlineObject ⟨1⟩) bytes,
             .createAtom outbox (.inlineObject ⟨2⟩) replyBytes] => do
              let binding ← bindingCodec.decode bytes
              let reply ← replyCodec.decode replyBytes
              if atom == operationAtom domain semantics binding.application binding.operation &&
                  outbox == replyAtom domain semantics binding.application binding.operation &&
                  reply == binding.reply &&
                  reply.application == binding.application &&
                  reply.operation == binding.operation &&
                  reply.sourceIdentity == binding.provenance.sourceIdentity &&
                  command.nonce == operationNonce domain semantics
                    binding.application binding.operation then
                some binding
              else none
          | _ => none
      | _ => none
  | _ => none

def decide (domain semantics : Digest) (report : Report) (receipt : Receipt)
    (accepted : List DurableReceiver.IntentRecord) : Decision :=
  let transaction := marker domain semantics report.subject
    (operationNonce domain semantics report.application report.operation)
  match accepted.find? (fun entry => entry.transactionId == transaction) with
  | none =>
      match bindingCommand domain semantics report receipt with
      | .ok command => .fresh command
          ⟨report.application, report.operation, report.provenance.sourceIdentity, receipt⟩
      | .error detail => .refused detail
  | some original =>
      match originalBinding domain semantics original with
      | none => .refused "operation marker occupied by nonconsumer transaction"
      | some binding =>
          if binding.application != report.application ||
              binding.operation != report.operation then
            .refused "operation marker collision or foreign binding"
          else if binding.provenance == report.provenance &&
              binding.package == report.package then
            .repeated binding.reply
          else .conflict (conflictCommand domain semantics report)

def Decision.intent (report : Report) : Decision → Option NativeObservationCodec.Intent
  | .fresh command _ | .conflict command =>
      some ⟨report.subject, command.nonce + 1,
        .prepare (.invoke (DeclaredResourceController.commandCodec.encode command)),
        [⟨.object, report.target, report.capability⟩]⟩
  | _ => none

/-- This local test adapter does not claim a fn authorship verdict. The caller
must supply a separately selected origin pin; the verified Mini receipt is
recomputed here before any operation command is authored. -/
def evaluate (origin consumer : NativeHost.Config) (report : Report) :
    IO (Except String Decision) := do
  match checkReport report with
  | .error detail => return .error detail
  | .ok () => pure ()
  let receipt ← match ← FnEvidence.verify origin report.package with
    | .error detail => return .error s!"Mini evidence: {detail}"
    | .ok receipt => pure receipt
  let opened ← match ← NativeHost.openExisting consumer with
    | .error detail => return .error s!"consumer history: {detail}"
    | .ok opened => pure opened
  unless opened.durable.image.accepted.length ≤ 16 do
    return .error "bounded E1 consumer history exceeds 16 accepted events"
  return .ok (decide consumer.deployment.domain consumer.profile.semantics
    report receipt opened.durable.image.accepted)

end Minidregg.Kernel.FnConsumerOperation
