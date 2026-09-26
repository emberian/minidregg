/-
The A-side result of observing Q is a local, durable Mini declaration. This
module consumes the already native-verified exact source and an authenticated
local fn Store poll; it does not turn a peer ARTICLE or a portable signature
into fn Store acceptance. The original R Mini package is independently
re-admitted by the host before it constructs this report.
-/
import Kernel.FnReplySource
import Kernel.FnConsumerOperation

namespace Minidregg.Kernel.FnReplyConsumption

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.FnConsumerOperation

set_option autoImplicit false

/-- Only locally selected context is outside the signed Q and native poll. -/
structure Policy where
  application : List UInt8
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  deriving DecidableEq, Repr

def Policy.matchesGateway (policy : Policy) (pin : FnGatewayPolicy.Pin) : Bool :=
  policy.application == pin.application && policy.subject == pin.subject &&
  policy.target == pin.target && policy.capability == pin.capability

structure Report where
  application : List UInt8
  operation : List UInt8
  parentSourceIdentity : List UInt8
  parentMessageId : List UInt8
  originReceipt : Receipt
  replySource : List UInt8
  replySourceIdentity : List UInt8
  replyMessageId : List UInt8
  portableInbox : PortableInbox
  storePoll : StorePollInbox
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  expectedAuthorityRoot : Digest
  expectedTargetRoot : Digest
  deriving Repr

/-- The result is one local observation of the exact Q in A's verified Store
history. It carries no claim that a remote or external effect ran once. -/
structure Result where
  application : List UInt8
  operation : List UInt8
  parentSourceIdentity : List UInt8
  parentMessageId : List UInt8
  replySourceIdentity : List UInt8
  replyMessageId : List UInt8
  originReceipt : Receipt
  reply : Reply
  deriving DecidableEq, Repr

def resultStream : StreamCodec Result :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream (StreamCodec.product bytesStream
          (StreamCodec.product receiptStream replyStream)))))))
    (fun x => (x.application, x.operation, x.parentSourceIdentity,
      x.parentMessageId, x.replySourceIdentity, x.replyMessageId,
      x.originReceipt, x.reply))
    (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
      x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2⟩)
    (by intro x; cases x; rfl)

def resultCodec : LawfulCodec Result :=
  NativeHostCodec.framed "DREGG/FN/A-REPLY-RESULT/v1".toUTF8.toList resultStream

def Report.result (report : Report) : Except String Result := do
  let parsed ← FnReplySource.extract report.replySource
  pure ⟨report.application, report.operation, report.parentSourceIdentity,
    report.parentMessageId, report.replySourceIdentity, report.replyMessageId,
    report.originReceipt, parsed.reply⟩

def check (policy : Policy) (report : Report) : Except String Result := do
  unless policy.application == report.application &&
      policy.subject == report.subject && policy.target == report.target &&
      policy.capability == report.capability &&
      validName report.application && validName report.operation &&
      report.parentSourceIdentity.length == 48 &&
      report.replySourceIdentity.length == 48 &&
      !report.parentMessageId.isEmpty && report.parentMessageId.length ≤ 256 &&
      !report.replyMessageId.isEmpty && report.replyMessageId.length ≤ 256 do
    throw "A reply report differs from local policy or bounded identity"
  unless report.portableInbox.valid report.replySourceIdentity &&
      report.storePoll.valid report.replySourceIdentity
        (storePollVerdictRef report.storePoll) &&
      report.storePoll.pollCallObserved &&
      report.storePoll.messageId == report.replyMessageId &&
      report.storePoll.verdictPrincipal == report.portableInbox.principal do
    throw "A reply lacks the native observed poll and exact verified carrier"
  let parsed ← FnReplySource.extract report.replySource
  unless parsed.messageId.toUTF8.toList == report.replyMessageId &&
      parsed.parentMessageId.toUTF8.toList == report.parentMessageId &&
      parsed.reply.application == report.application &&
      parsed.reply.operation == report.operation &&
      parsed.reply.sourceIdentity == report.parentSourceIdentity &&
      parsed.reply.miniReceipt == report.originReceipt &&
      (resultCodec.encode (← report.result)).length ≤ 2048 do
    throw "Q differs from the independent R identity, operation, or receipt"
  pure (← report.result)

def reportStream : StreamCodec Report :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream
        (StreamCodec.product receiptStream (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream (StreamCodec.product bytesStream
            (StreamCodec.product portableInboxStream (StreamCodec.product
              storePollStream (StreamCodec.product StreamCodec.nat
                (StreamCodec.product StreamCodec.nat (StreamCodec.product
                  StreamCodec.nat (StreamCodec.product digestStream digestStream))))))))))))))
    (fun x => (x.application, x.operation, x.parentSourceIdentity,
      x.parentMessageId, x.originReceipt, x.replySource,
      x.replySourceIdentity, x.replyMessageId, x.portableInbox,
      x.storePoll, x.subject.value, x.target, x.capability.value,
      x.expectedAuthorityRoot, x.expectedTargetRoot))
    (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
      x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
      x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
      ⟨x.2.2.2.2.2.2.2.2.2.2.1⟩,
      x.2.2.2.2.2.2.2.2.2.2.2.1,
      ⟨x.2.2.2.2.2.2.2.2.2.2.2.2.1⟩,
      x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      x.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    (by intro x; cases x; rfl)

def reportCodec : LawfulCodec Report :=
  NativeHostCodec.framed "DREGG/FN/A-REPLY-INBOX/v1".toUTF8.toList reportStream

/-- Current resource roots are CAS preconditions and change after acceptance.
They are retained in the signed call, but are not part of immutable Q input. -/
def Report.evidenceBytes (report : Report) : List UInt8 :=
  reportCodec.encode { report with
    expectedAuthorityRoot := ⟨0⟩, expectedTargetRoot := ⟨0⟩ }

def opHash (domain semantics : Digest) (application operation : List UInt8) : Nat :=
  (Sp800185Cshake256.hash "DREGG.FN.A-REPLY-OP/v1".toUTF8.toList
    (operationPreimage domain semantics application operation)).digest.value

def conflictHash (domain semantics : Digest) (report : Report) : Nat :=
  (Sp800185Cshake256.hash "DREGG.FN.A-REPLY-CONFLICT/v1".toUTF8.toList
    (operationPreimage domain semantics report.application report.operation ++
      report.evidenceBytes)).digest.value

/-- High ranges are disjoint from B's existing operation and poll atoms. -/
def resultAtom (domain semantics : Digest) (application operation : List UInt8) : AtomId :=
  ⟨⟨2 ^ 261 + 4 * opHash domain semantics application operation⟩⟩

def inboxAtom (domain semantics : Digest) (application operation : List UInt8) : AtomId :=
  ⟨⟨2 ^ 261 + 4 * opHash domain semantics application operation + 1⟩⟩

def conflictAtom (domain semantics : Digest) (report : Report) : AtomId :=
  ⟨⟨2 ^ 262 + 4 * conflictHash domain semantics report⟩⟩

def resultNonce (domain semantics : Digest) (application operation : List UInt8) : Nat :=
  2 ^ 261 + opHash domain semantics application operation

def conflictNonce (domain semantics : Digest) (report : Report) : Nat :=
  2 ^ 262 + conflictHash domain semantics report

def resultCommand (domain semantics : Digest) (report : Report) (result : Result) :
    Except String DeclaredResourceController.Command := do
  unless (reportCodec.encode report).length ≤ 110000 do
    throw "A reply retained inbox exceeds bound"
  pure ⟨report.subject, report.expectedAuthorityRoot,
    resultNonce domain semantics report.application report.operation,
    [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
      .content ⟨[.createAtom
        (resultAtom domain semantics report.application report.operation)
        (.inlineObject ⟨6⟩) (resultCodec.encode result),
        .createAtom (inboxAtom domain semantics report.application report.operation)
        (.inlineObject ⟨7⟩) (reportCodec.encode report)]⟩, none⟩]⟩

def conflictCommand (domain semantics : Digest) (report : Report) :
    DeclaredResourceController.Command :=
  ⟨report.subject, report.expectedAuthorityRoot,
    conflictNonce domain semantics report,
    [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
      .content ⟨[.createAtom (conflictAtom domain semantics report)
        (.inlineObject ⟨8⟩) (reportCodec.encode report)]⟩, none⟩]⟩

def originalConflict (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option Report := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  let .content content := target.payload | none
  let [.createAtom conflictId (.inlineObject ⟨8⟩) bytes] := content.actions | none
  let report ← reportCodec.decode bytes
  let .ok _ := check
      ⟨report.application, report.subject, report.target, report.capability⟩ report
    | none
  if report.application == pin.application &&
      command.subject == pin.subject && target.target == pin.target &&
      target.capability == pin.capability &&
      (reportCodec.encode report).length ≤ 110000 &&
      conflictId == conflictAtom domain semantics report &&
      command.nonce == conflictNonce domain semantics report &&
      command.subject == report.subject && target.target == report.target &&
      target.capability == report.capability &&
      command.expectedAuthorityRoot == report.expectedAuthorityRoot &&
      target.expectedTargetRoot == report.expectedTargetRoot &&
      FnConsumerOperation.exactSignedCommand signed.commandBytes
        (conflictCommand domain semantics report) then
    some report else none

/-- Reopen the original accepted result under the configured gateway identity.
Current mutation law is checked for a new result, not for reading or ACKing a
position already atomically retained in Mini's accepted history. -/
def originalResult (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option (Result × Report) := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  let .content content := target.payload | none
  let [.createAtom resultId (.inlineObject ⟨6⟩) resultBytes,
       .createAtom inboxId (.inlineObject ⟨7⟩) inboxBytes] := content.actions | none
  let result ← resultCodec.decode resultBytes
  let report ← reportCodec.decode inboxBytes
  let .ok checked := check
      ⟨report.application, report.subject, report.target, report.capability⟩ report
    | none
  let .ok expected := resultCommand domain semantics report result | none
  if report.application == pin.application &&
      command.subject == pin.subject && target.target == pin.target &&
      target.capability == pin.capability &&
      (reportCodec.encode report).length ≤ 110000 &&
      resultId == resultAtom domain semantics report.application report.operation &&
      inboxId == inboxAtom domain semantics report.application report.operation &&
      command.nonce == resultNonce domain semantics report.application report.operation &&
      command.subject == report.subject && target.target == report.target &&
      target.capability == report.capability &&
      command.expectedAuthorityRoot == report.expectedAuthorityRoot &&
      target.expectedTargetRoot == report.expectedTargetRoot &&
      checked == result &&
      FnConsumerOperation.exactSignedCommand signed.commandBytes expected then
    some (result, report) else none

inductive Decision where
  | fresh (command : DeclaredResourceController.Command) (result : Result)
  | repeated (result : Result)
  | conflict (command : DeclaredResourceController.Command)
  | conflictRecorded
  | refused (reason : String)
  deriving Repr

def decide (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (policy : Policy) (report : Report)
    (accepted : List DurableReceiver.IntentRecord) : Decision :=
  match (if policy.matchesGateway pin then check policy report
    else .error "A reply policy differs from independently pinned fn gateway") with
  | .error reason => .refused reason
  | .ok result =>
      let transaction := marker domain semantics report.subject
        (resultNonce domain semantics report.application report.operation)
      match accepted.find? (fun record => record.transactionId == transaction) with
      | none =>
          match resultCommand domain semantics report result with
          | .ok command => .fresh command result
          | .error reason => .refused reason
      | some record =>
          match originalResult pin domain semantics record with
          | none => .refused "A reply marker occupied by foreign transaction"
          | some (original, oldReport) =>
              if original.application != report.application ||
                  original.operation != report.operation then
                .refused "A reply operation marker collision"
              else if oldReport.evidenceBytes.toByteArray =
                  report.evidenceBytes.toByteArray then
                .repeated original
              else
                let conflictTx := marker domain semantics report.subject
                  (conflictNonce domain semantics report)
                match accepted.find? (fun item => item.transactionId == conflictTx) with
                | none => .conflict (conflictCommand domain semantics report)
                | some conflict =>
                    match originalConflict pin domain semantics conflict with
                    | some recorded =>
                        if recorded.evidenceBytes.toByteArray =
                            report.evidenceBytes.toByteArray then
                          .conflictRecorded
                        else .refused "A reply conflict marker occupied by other evidence"
                    | none => .refused "A reply conflict marker occupied by foreign transaction"

/-- Scan accepted history for the same application operation under any local
grant. A policy change cannot produce a second result under a new subject. -/
def evaluate (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (policy : Policy) (report : Report)
    (accepted : List DurableReceiver.IntentRecord) : Decision :=
  if (reportCodec.encode report).length > 110000 then
    .refused "A reply retained inbox exceeds bound"
  else if accepted.any (fun record =>
      match originalResult pin domain semantics record with
      | some (old, oldReport) =>
          old.application == report.application && old.operation == report.operation &&
          (oldReport.subject != policy.subject || oldReport.target != policy.target ||
            oldReport.capability != policy.capability)
      | none => false) then
    .refused "A reply operation already bound under another local grant"
  else decide pin domain semantics policy report accepted

/-- The host must use this entry point for fresh A-side decisions. Historical
recovery may decode an accepted event under its old law, while every new
proposal uses the independently pinned current gateway law. -/
def evaluateVerified (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (pin : FnGatewayPolicy.Pin) (policy : Policy) (report : Report) :
    Except String Decision := do
  FnGatewayPolicy.checkCurrent config opened pin
  pure (evaluate pin config.deployment.domain config.profile.semantics
    policy report opened.durable.image.accepted)

def Decision.intent (report : Report) : Decision → Option NativeObservationCodec.Intent
  | .fresh command _ | .conflict command =>
      some ⟨report.subject, command.nonce + 1,
        .prepare (.invoke (DeclaredResourceController.commandCodec.encode command)),
        [⟨.object, report.target, report.capability⟩]⟩
  | _ => none

end Minidregg.Kernel.FnReplyConsumption
