/-
Bounded local E1 consumer operation. The application/operation pair selects a
stable transaction nonce independent of fn source identity. The ordinary native
resource receiver remains the admission and atomic CAS owner. This module only
authors its command and interprets its historical signed event.

The first profile has one local consumer subject and one pre-birthed content
resource. The original synthetic route uses a trusted test adapter. The
portable fn route records a verified source identity with explicit absent-
Store sentinels until fn's native historical verdict connector is available.
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

/-- Exact portable article and independently verified public key context.
The fn Store receipt is absent; this record retains the input needed for a
later exact fetch join without treating the signature as Store admission. -/
structure PortableInbox where
  carrier : List UInt8
  sourceIdentity : List UInt8
  principal : List UInt8
  edPublicKey : List UInt8
  mlPublicKey : List UInt8
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
  portableInbox : Option PortableInbox := none
  deriving Repr

/-- Local operator selection. It is not accepted from the fetched fn article. -/
structure Policy where
  application : List UInt8
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  deriving DecidableEq, Repr

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

structure ConflictEvidence where
  application : List UInt8
  operation : List UInt8
  provenance : Provenance
  package : List UInt8
  deriving DecidableEq, Repr

def provenanceStream : StreamCodec Provenance :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream bytesStream)))
    (fun value => (value.history, value.incarnation,
      value.sourceIdentity, value.fnVerdictRef))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

def portableInboxStream : StreamCodec PortableInbox :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream))))
    (fun value => (value.carrier, value.sourceIdentity, value.principal,
      value.edPublicKey, value.mlPublicKey))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def portableInboxCodec : LawfulCodec PortableInbox :=
  NativeHostCodec.framed "DREGG/FN/PORTABLE-INBOX/v1".toUTF8.toList portableInboxStream

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

def conflictStream : StreamCodec ConflictEvidence :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product provenanceStream bytesStream)))
    (fun value => (value.application, value.operation, value.provenance, value.package))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

def conflictCodec : LawfulCodec ConflictEvidence :=
  NativeHostCodec.framed "DREGG/FN/CONFLICT-EVIDENCE/v1".toUTF8.toList conflictStream

def maxNameBytes : Nat := 64
def maxVerdictRefBytes : Nat := 256
def maxBindingBytes : Nat := 18432
def maxInboxBytes : Nat := 36864

def PortableInbox.valid (inbox : PortableInbox)
    (expectedSource : List UInt8) : Bool :=
  !inbox.carrier.isEmpty && inbox.carrier.length ≤ 32768 &&
  inbox.sourceIdentity.length == 48 &&
  inbox.sourceIdentity == expectedSource &&
  inbox.principal.length == 32 && inbox.edPublicKey.length == 32 &&
  inbox.mlPublicKey.length == 1952 &&
  (portableInboxCodec.encode inbox).length ≤ maxInboxBytes

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
  match report.portableInbox with
  | none => pure ()
  | some inbox =>
      unless inbox.valid report.provenance.sourceIdentity do
        throw "portable inbox is absent, mismatched, or oversized"

def checkPolicy (policy : Policy) (report : Report) : Except String Unit := do
  unless report.application == policy.application &&
      report.subject == policy.subject && report.target == policy.target &&
      report.capability == policy.capability do
    throw "report differs from operator-selected consumer namespace and grant"

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
      provenanceStream.encode report.provenance ++
      (match report.portableInbox with
       | none => []
       | some inbox => portableInboxCodec.encode inbox))).digest.value + 1

theorem operationNonce_ne_conflictNonce (domain semantics : Digest)
    (report : Report) :
    operationNonce domain semantics report.application report.operation ≠
      conflictNonce domain semantics report := by
  unfold operationNonce conflictNonce
  omega

def operationAtom (domain semantics : Digest) (application operation : List UInt8) : AtomId :=
  ⟨⟨2 * operationNonce domain semantics application operation⟩⟩

def replyAtom (domain semantics : Digest) (application operation : List UInt8) : AtomId :=
  ⟨⟨2 * operationNonce domain semantics application operation + 1⟩⟩

def conflictAtom (domain semantics : Digest) (report : Report) : AtomId :=
  ⟨⟨2 * conflictNonce domain semantics report⟩⟩

/-- Residue 3 is reserved for exact portable input. Its domain-separated
nonce distinguishes operation and conflict records up to hash collision. -/
def operationInboxAtom (domain semantics : Digest)
    (application operation : List UInt8) : AtomId :=
  ⟨⟨2 * operationNonce domain semantics application operation + 3⟩⟩

def conflictInboxAtom (domain semantics : Digest) (report : Report) : AtomId :=
  ⟨⟨2 * conflictNonce domain semantics report + 1⟩⟩

theorem operationAtom_ne_replyAtom (domain semantics : Digest)
    (application operation : List UInt8) :
    operationAtom domain semantics application operation ≠
      replyAtom domain semantics application operation := by
  intro equal
  have n : 2 * operationNonce domain semantics application operation =
    2 * operationNonce domain semantics application operation + 1 := by
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
  let base : List ContentResource.Action :=
    [.createAtom (operationAtom domain semantics report.application report.operation)
      (.inlineObject ⟨1⟩) bytes,
     .createAtom (replyAtom domain semantics report.application report.operation)
      (.inlineObject ⟨2⟩) (replyCodec.encode reply)]
  let actions := base ++ match report.portableInbox with
    | none => []
    | some inbox =>
        [.createAtom (operationInboxAtom domain semantics report.application report.operation)
          (.inlineObject ⟨4⟩) (portableInboxCodec.encode inbox)]
  pure ⟨report.subject, report.expectedAuthorityRoot,
    operationNonce domain semantics report.application report.operation,
    [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
      .content ⟨actions⟩, none⟩]⟩

def conflictCommand (domain semantics : Digest) (report : Report) :
    DeclaredResourceController.Command :=
  let base : List ContentResource.Action :=
    [.createAtom (conflictAtom domain semantics report)
      (.inlineObject ⟨3⟩) (conflictCodec.encode
        ⟨report.application, report.operation, report.provenance, report.package⟩)]
  let actions := base ++ match report.portableInbox with
    | none => []
    | some inbox =>
        [.createAtom (conflictInboxAtom domain semantics report)
          (.inlineObject ⟨4⟩) (portableInboxCodec.encode inbox)]
  ⟨report.subject, report.expectedAuthorityRoot,
   conflictNonce domain semantics report,
   [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
     .content ⟨actions⟩, none⟩]⟩

inductive Decision where
  | fresh (command : DeclaredResourceController.Command) (reply : Reply)
  | repeated (reply : Reply)
  | carrierVariation (command : DeclaredResourceController.Command) (reply : Reply)
  | carrierVariationRecorded (reply : Reply)
  | conflict (command : DeclaredResourceController.Command)
  | conflictRecorded
  | refused (detail : String)
  deriving Repr

/-- Inspect the original accepted call, rather than a mutable current atom.
The prior reply remains recoverable from the durable accepted event history. -/
def originalBindingWithInbox (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option (Binding × Option PortableInbox) := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  match command.targets with
  | [target] =>
      match target.payload with
      | .content content =>
          let (atom, bytes, outbox, replyBytes, inboxAction) ←
            match content.actions with
            | [.createAtom atom (.inlineObject ⟨1⟩) bytes,
               .createAtom outbox (.inlineObject ⟨2⟩) replyBytes] =>
                some (atom, bytes, outbox, replyBytes, none)
            | [.createAtom atom (.inlineObject ⟨1⟩) bytes,
               .createAtom outbox (.inlineObject ⟨2⟩) replyBytes,
               .createAtom inboxAtom (.inlineObject ⟨4⟩) inboxBytes] =>
                some (atom, bytes, outbox, replyBytes, some (inboxAtom, inboxBytes))
            | _ => none
          let binding ← bindingCodec.decode bytes
          let reply ← replyCodec.decode replyBytes
          let inbox ← match inboxAction with
            | none => some none
            | some (inboxAtom, inboxBytes) => do
                if inboxBytes.length > maxInboxBytes then none else
                let inbox ← portableInboxCodec.decode inboxBytes
                if inboxAtom == operationInboxAtom domain semantics
                    binding.application binding.operation &&
                    inbox.valid binding.provenance.sourceIdentity then
                  some (some inbox)
                else none
          if atom == operationAtom domain semantics binding.application binding.operation &&
              outbox == replyAtom domain semantics binding.application binding.operation &&
              reply == binding.reply &&
              reply.application == binding.application &&
              reply.operation == binding.operation &&
              reply.sourceIdentity == binding.provenance.sourceIdentity &&
              command.nonce == operationNonce domain semantics
                binding.application binding.operation then
            some (binding, inbox)
          else none
      | _ => none
  | _ => none

def originalBinding (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option Binding :=
  (originalBindingWithInbox domain semantics record).map Prod.fst

/-- A later operator policy cannot silently move an already bound operation
to another local subject, target, or capability. The original accepted
signed call, not caller metadata, supplies this historical grant context. -/
def originalBindingGrant (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) :
    Option (Binding × SubjectId × Nat × CapabilityId) := do
  let binding ← originalBinding domain semantics record
  let (_, _, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  some (binding, command.subject, target.target, target.capability)

def checkHistoricalPolicy (domain semantics : Digest) (policy : Policy)
    (report : Report) (accepted : List DurableReceiver.IntentRecord) :
    Except String Unit := do
  for record in accepted do
    match originalBindingGrant domain semantics record with
    | some (binding, subject, target, capability) =>
        if binding.application == report.application &&
            binding.operation == report.operation then
          unless subject == policy.subject && target == policy.target &&
              capability == policy.capability do
            throw "consumer operation already bound under another local grant"
    | none => pure ()

def originalConflictWithInbox (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) :
    Option (ConflictEvidence × Option PortableInbox) := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  match command.targets with
  | [target] =>
      match target.payload with
      | .content content =>
          let (atom, bytes, inboxAction) ← match content.actions with
            | [.createAtom atom (.inlineObject ⟨3⟩) bytes] =>
                some (atom, bytes, none)
            | [.createAtom atom (.inlineObject ⟨3⟩) bytes,
               .createAtom inboxAtom (.inlineObject ⟨4⟩) inboxBytes] =>
                some (atom, bytes, some (inboxAtom, inboxBytes))
            | _ => none
          let evidence ← conflictCodec.decode bytes
          let inbox ← match inboxAction with
            | none => some none
            | some (_, inboxBytes) => do
                if inboxBytes.length > maxInboxBytes then none else
                let inbox ← portableInboxCodec.decode inboxBytes
                if inbox.valid evidence.provenance.sourceIdentity then
                  some (some inbox)
                else none
          let report : Report :=
            { application := evidence.application, operation := evidence.operation,
              provenance := evidence.provenance, package := evidence.package,
              subject := command.subject, target := target.target,
              capability := target.capability,
              expectedAuthorityRoot := command.expectedAuthorityRoot,
              expectedTargetRoot := target.expectedTargetRoot,
              portableInbox := inbox }
          if atom == conflictAtom domain semantics report &&
              (inboxAction.isNone ||
                inboxAction.any (fun pair =>
                  pair.1 == conflictInboxAtom domain semantics report)) &&
              command.nonce == conflictNonce domain semantics report then
            some (evidence, inbox)
          else none
      | _ => none
  | _ => none

def originalConflict (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option ConflictEvidence :=
  (originalConflictWithInbox domain semantics record).map Prod.fst

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
      match originalBindingWithInbox domain semantics original with
      | none => .refused "operation marker occupied by nonconsumer transaction"
      | some (binding, originalInbox) =>
          if binding.application != report.application ||
              binding.operation != report.operation then
            .refused "operation marker collision or foreign binding"
          else if binding.provenance == report.provenance &&
              binding.package == report.package &&
              originalInbox == report.portableInbox then
            .repeated binding.reply
          else
            let sameSource := binding.provenance == report.provenance &&
              binding.package == report.package
            let conflictTransaction := marker domain semantics report.subject
              (conflictNonce domain semantics report)
            match accepted.find? (fun entry => entry.transactionId == conflictTransaction) with
            | none =>
                if sameSource then .carrierVariation
                  (conflictCommand domain semantics report) binding.reply
                else .conflict (conflictCommand domain semantics report)
            | some conflict =>
                if originalConflictWithInbox domain semantics conflict ==
                    some (⟨report.application, report.operation,
                      report.provenance, report.package⟩, report.portableInbox) then
                  if sameSource then .carrierVariationRecorded binding.reply
                  else .conflictRecorded
                else .refused "conflict marker occupied by different evidence"

def Decision.intent (report : Report) : Decision → Option NativeObservationCodec.Intent
  | .fresh command _ | .conflict command | .carrierVariation command _ =>
      some ⟨report.subject, command.nonce + 1,
        .prepare (.invoke (DeclaredResourceController.commandCodec.encode command)),
        [⟨.object, report.target, report.capability⟩]⟩
  | _ => none

def evaluateVerified (consumer : NativeHost.Config) (policy : Policy)
    (report : Report) (receipt : Receipt) (opened : NativeHost.Opened consumer) :
    Except String Decision := do
  checkReport report
  checkPolicy policy report
  unless opened.durable.image.accepted.length ≤ 16 do
    throw "bounded E1 consumer history exceeds 16 accepted events"
  checkHistoricalPolicy consumer.deployment.domain consumer.profile.semantics
    policy report opened.durable.image.accepted
  pure (decide consumer.deployment.domain consumer.profile.semantics
    report receipt opened.durable.image.accepted)

/-- The synthetic adapter independently verifies the origin and reopens
current consumer history. The portable native route passes those already
verified values to evaluateVerified without replaying either twice. -/
def evaluate (origin consumer : NativeHost.Config) (policy : Policy) (report : Report) :
    IO (Except String Decision) := do
  match checkReport report with
  | .error detail => return .error detail
  | .ok () => pure ()
  match checkPolicy policy report with
  | .error detail => return .error detail
  | .ok () => pure ()
  let receipt ← match ← FnEvidence.verify origin report.package with
    | .error detail => return .error s!"Mini evidence: {detail}"
    | .ok receipt => pure receipt
  let opened ← match ← NativeHost.openExisting consumer with
    | .error detail => return .error s!"consumer history: {detail}"
    | .ok opened => pure opened
  return evaluateVerified consumer policy report receipt opened

end Minidregg.Kernel.FnConsumerOperation
