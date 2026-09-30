/-
An A catalog consumer may encounter its own already prepared R before Q.
The qualified fn poll scans at most sixteen consecutive Store events and
returns the first group-matching article; its cursor is the prefix through
that article. A local gateway records that exact observed R and cursor in
Mini before fn ACK. This record has no application result or reply effect.
The host, not this portable codec, establishes the trusted local poll and
native R verification against an accepted A outbox.
-/
import Kernel.FnConsumerProgress
import Kernel.FnOriginOutbox

namespace Minidregg.Kernel.FnCatalogOwnRProgress

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

structure Evidence where
  application : List UInt8
  scope : FnConsumerProgress.Scope
  fromPosition : Nat
  toPosition : Nat
  outboxTransaction : Digest
  portable : PortableInbox
  poll : StorePollInbox
  deriving DecidableEq, Repr

structure Report where
  evidence : Evidence
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  expectedTargetRoot : Digest
  deriving Repr

def evidenceStream : StreamCodec Evidence :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product FnConsumerProgress.scopeStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product digestStream
          (StreamCodec.product portableInboxStream storePollStream))))))
    (fun value => (value.application, value.scope, value.fromPosition,
      value.toPosition, value.outboxTransaction, value.portable, value.poll))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2.1, wire.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

/-- Distinct frame and nonce prevent interpreting a historical empty-page
tag-9 atom as an own-R article skip. -/
def evidenceCodec : LawfulCodec Evidence :=
  NativeHostCodec.framed "DREGG/FN/CATALOG-OWN-R-PROGRESS/v1".toUTF8.toList
    evidenceStream

def maxEvidenceBytes : Nat := FnEvidenceCodec.maxStorePollInboxBytes +
  FnEvidenceCodec.maxPortableInboxBytes + 8192

def Evidence.valid (evidence : Evidence) : Bool :=
  validName evidence.application && evidence.scope.valid &&
  evidence.fromPosition < evidence.toPosition &&
  evidence.toPosition ≤ evidence.fromPosition + FnConsumerProgress.maxPollScan &&
  evidence.toPosition ≤ 4294967295 &&
  evidence.poll.sequence + 1 == evidence.toPosition &&
  evidence.poll.pollCallObserved &&
  evidence.portable.valid evidence.poll.sourceIdentity &&
  evidence.poll.valid evidence.portable.sourceIdentity
    (storePollVerdictRef evidence.poll) &&
  evidence.portable.principal == evidence.poll.verdictPrincipal &&
  (evidenceCodec.encode evidence).length ≤ maxEvidenceBytes

def Evidence.matchesOutbox (evidence : Evidence)
    (prepared : FnOriginOutbox.Prepared) : Bool :=
  prepared.application == evidence.application &&
  prepared.messageId == evidence.poll.messageId &&
  prepared.sourceIdentity == evidence.portable.sourceIdentity &&
  prepared.principal == evidence.portable.principal &&
  prepared.edPublicKey == evidence.portable.edPublicKey &&
  prepared.mlPublicKey == evidence.portable.mlPublicKey

def originalOutbox (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (evidence : Evidence) (accepted : List DurableReceiver.IntentRecord) :
    Option FnOriginOutbox.Prepared := do
  let record ← accepted.find? (fun entry =>
    entry.transactionId == evidence.outboxTransaction)
  let prepared ← FnOriginOutbox.originalPrepared pin domain semantics record
  if evidence.matchesOutbox prepared then some prepared else none

def Report.matchesGateway (report : Report) (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) : Bool :=
  policy.matchesGateway pin &&
  report.evidence.application == policy.application &&
  report.subject == policy.subject && report.target == policy.target &&
  report.capability == policy.capability

def checkReport (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (scope : FnConsumerProgress.Scope)
    (domain semantics : Digest) (accepted : List DurableReceiver.IntentRecord)
    (report : Report) : Except String Unit := do
  if report.matchesGateway pin policy then
    unless report.evidence.scope == scope && report.evidence.valid do
      throw "own-R progress is unobserved, unscoped, or outside selected scan window"
    unless (originalOutbox pin domain semantics report.evidence accepted).isSome do
      throw "own-R progress has no matching accepted local R outbox"
  else throw "own-R progress differs from independently pinned gateway"

theorem checkReport_pinned (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (scope : FnConsumerProgress.Scope)
    (domain semantics : Digest) (accepted : List DurableReceiver.IntentRecord)
    (report : Report)
    (checked : checkReport pin policy scope domain semantics accepted report = .ok ()) :
    report.evidence.application = pin.application ∧
    report.subject = pin.subject ∧ report.target = pin.target ∧
    report.capability = pin.capability := by
  have matched : report.matchesGateway pin policy = true := by
    cases h : report.matchesGateway pin policy with
    | false => simp [checkReport, h] at checked
    | true => rfl
  simp [Report.matchesGateway, FnConsumerOperation.Policy.matchesGateway] at matched
  aesop

def progressPreimage (domain semantics : Digest) (evidence : Evidence) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream
    evidenceStream)).encode (domain, semantics, evidence)

def progressHash (domain semantics : Digest) (evidence : Evidence) : Nat :=
  (Sp800185Cshake256.hash "DREGG.FN.CATALOG-OWN-R-PROGRESS/v1".toUTF8.toList
    (progressPreimage domain semantics evidence)).digest.value

def progressNonce (domain semantics : Digest) (evidence : Evidence) : Nat :=
  2 ^ 276 + progressHash domain semantics evidence

def progressAtom (domain semantics : Digest) (evidence : Evidence) : AtomId :=
  ⟨⟨2 ^ 277 + progressHash domain semantics evidence⟩⟩

def marker (domain semantics : Digest) (subject : SubjectId)
    (evidence : Evidence) : Digest :=
  FnConsumerOperation.marker domain semantics subject
    (progressNonce domain semantics evidence)

def progressCommand (domain semantics : Digest) (report : Report) :
    DeclaredResourceController.Command :=
  ⟨report.subject,
    progressNonce domain semantics report.evidence,
    [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
      .content ⟨[.createAtom (progressAtom domain semantics report.evidence)
        (.inlineObject ⟨9⟩) (evidenceCodec.encode report.evidence)]⟩, none⟩]⟩

theorem progressCommand_exact_action (domain semantics : Digest) (report : Report) :
    (progressCommand domain semantics report).targets =
      [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
        .content ⟨[.createAtom (progressAtom domain semantics report.evidence)
          (.inlineObject ⟨9⟩) (evidenceCodec.encode report.evidence)]⟩, none⟩] := rfl

/-- Only the complete original signed command is historical evidence. Current
gateway mutation law is deliberately not needed to settle an accepted cursor. -/
def originalOwnR (pin : FnGatewayPolicy.Pin) (scope : FnConsumerProgress.Scope)
    (domain semantics : Digest) (record : DurableReceiver.IntentRecord)
    (accepted : List DurableReceiver.IntentRecord) : Option Evidence := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  let .content content := target.payload | none
  let [.createAtom atom (.inlineObject ⟨9⟩) bytes] := content.actions | none
  if bytes.length > maxEvidenceBytes then none else
  let evidence ← evidenceCodec.decode bytes
  let report : Report := ⟨evidence, command.subject, target.target,
    target.capability, target.expectedTargetRoot⟩
  if evidence.application == pin.application && evidence.scope == scope &&
      evidence.valid && command.subject == pin.subject &&
      target.target == pin.target && target.capability == pin.capability &&
      atom == progressAtom domain semantics evidence &&
      command.nonce == progressNonce domain semantics evidence &&
      record.transactionId == marker domain semantics command.subject evidence &&
      (originalOutbox pin domain semantics evidence accepted).isSome &&
      exactSignedCommand signed.commandBytes
        (progressCommand domain semantics report) then
    some evidence
  else none

inductive Decision where
  | fresh (command : DeclaredResourceController.Command)
  | repeated
  | refused (detail : String)
  deriving Repr

def decide (pin : FnGatewayPolicy.Pin) (scope : FnConsumerProgress.Scope)
    (domain semantics : Digest) (report : Report)
    (accepted : List DurableReceiver.IntentRecord) : Decision :=
  let transaction := marker domain semantics report.subject report.evidence
  match accepted.find? (fun entry => entry.transactionId == transaction) with
  | none => .fresh (progressCommand domain semantics report)
  | some original =>
      match originalOwnR pin scope domain semantics original accepted with
      | some previous =>
          if (evidenceCodec.encode previous).toByteArray =
              (evidenceCodec.encode report.evidence).toByteArray then .repeated
          else .refused "own-R progress marker occupied by other exact evidence"
      | none => .refused "own-R progress marker occupied by another transaction"

def Decision.intent (report : Report) : Decision → Option NativeObservationCodec.Intent
  | .fresh command =>
      some ⟨report.subject, command.nonce + 1,
        .prepare (.invoke (DeclaredResourceController.commandCodec.encode command)),
        [⟨.object, report.target, report.capability⟩]⟩
  | _ => none

def evaluateVerified (consumer : NativeHost.Config) (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (scope : FnConsumerProgress.Scope)
    (report : Report) (opened : NativeHost.Opened consumer) :
    Except String Decision := do
  checkReport pin policy scope consumer.deployment.domain
    consumer.profile.semantics opened.durable.image.accepted report
  FnGatewayPolicy.checkCurrent consumer opened pin
  pure (decide pin scope consumer.deployment.domain consumer.profile.semantics
    report opened.durable.image.accepted)

end Minidregg.Kernel.FnCatalogOwnRProgress
