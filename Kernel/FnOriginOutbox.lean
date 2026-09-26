/-
A-side local custody of a prepared R publication. The gateway records the
exact carrier and its independently re-admitted Mini origin before fn post.
This atom is never a claim of fn Store admission, posting, or remote receipt.
The host alone may turn a native verifier result and an original Mini replay
into the trusted-local assertions in Report; gateway subject law prevents a
resource user from submitting those assertions directly.
-/
import Kernel.FnConsumerOperation

namespace Minidregg.Kernel.FnOriginOutbox

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Hyperdocument
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

/-- The exact R carrier is retained once. The two digests bind the carried
FnEvidence package and its original signed call without duplicating the
megabyte-scale package already inside that carrier. -/
structure Prepared where
  application : List UInt8
  operation : List UInt8
  messageId : List UInt8
  sourceIdentity : List UInt8
  carrier : List UInt8
  packageIdentity : Digest
  originCallIdentity : Digest
  originReceipt : Receipt
  principal : List UInt8
  edPublicKey : List UInt8
  mlPublicKey : List UInt8
  deriving DecidableEq, Repr

def preparedStream : StreamCodec Prepared :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream (StreamCodec.product digestStream
          (StreamCodec.product digestStream (StreamCodec.product receiptStream
            (StreamCodec.product bytesStream (StreamCodec.product bytesStream
              bytesStream))))))))))
    (fun value => (value.application, value.operation, value.messageId,
      value.sourceIdentity, value.carrier, value.packageIdentity,
      value.originCallIdentity, value.originReceipt, value.principal,
      value.edPublicKey, value.mlPublicKey))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2.1, value.2.2.2.2.2.1, value.2.2.2.2.2.2.1,
      value.2.2.2.2.2.2.2.1, value.2.2.2.2.2.2.2.2.1,
      value.2.2.2.2.2.2.2.2.2.1,
      value.2.2.2.2.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def preparedCodec : LawfulCodec Prepared :=
  NativeHostCodec.framed "DREGG/FN/ORIGIN-OUTBOX/v1".toUTF8.toList preparedStream

def maxPreparedBytes : Nat := FnEvidenceCodec.maxCarrierBytes + 8192

def packageIdentity (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.FN.ORIGIN-PACKAGE/v1".toUTF8.toList bytes).digest

def callIdentity (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.FN.ORIGIN-CALL/v1".toUTF8.toList bytes).digest

def Prepared.valid (value : Prepared) : Bool :=
  FnConsumerOperation.validName value.application &&
  FnConsumerOperation.validName value.operation &&
  value.messageId.length ≥ 3 && value.messageId.length ≤ 256 &&
  value.messageId.head? == some 60 && value.messageId.getLast? == some 62 &&
  value.messageId.all (fun b => 33 ≤ b.toNat && b.toNat ≤ 126) &&
  value.sourceIdentity.length == 48 &&
  !value.carrier.isEmpty && value.carrier.length ≤ FnEvidenceCodec.maxCarrierBytes &&
  value.principal.length == 32 && value.edPublicKey.length == 32 &&
  value.mlPublicKey.length == 1952 && value.originReceipt.acceptedCount > 0 &&
  (preparedCodec.encode value).length ≤ maxPreparedBytes

/-- A trusted local gateway report. The Booleans label actual native carrier
verification and Mini origin replay performed by Host before constructing it;
they are not remote fn evidence and cannot be accepted from a user frame. -/
structure Report where
  prepared : Prepared
  package : List UInt8
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  expectedAuthorityRoot : Digest
  expectedTargetRoot : Digest
  nativeCarrierVerified : Bool
  originReadmitted : Bool
  deriving Repr

def Report.matchesGateway (report : Report) (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) : Bool :=
  policy.matchesGateway pin &&
  report.prepared.application == policy.application &&
  report.subject == policy.subject && report.target == policy.target &&
  report.capability == policy.capability

def checkReport (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (report : Report) : Except String Unit := do
  if report.matchesGateway pin policy then
    unless report.prepared.valid && report.nativeCarrierVerified &&
        report.originReadmitted && report.package.length ≤ FnEvidenceCodec.maxPackageBytes do
      throw "prepared R outbox lacks bounded verified local origin"
    let package ← FnEvidenceCodec.decodeChecked report.package
    unless FnConsumerOperation.originOperation package == report.prepared.operation &&
        package.originalReceipt == report.prepared.originReceipt &&
        packageIdentity report.package == report.prepared.packageIdentity &&
        callIdentity package.signedCall == report.prepared.originCallIdentity do
      throw "prepared R outbox differs from exact re-admitted Mini origin"
  else throw "prepared R outbox differs from independently pinned gateway"

theorem checkReport_pinned (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (report : Report)
    (accepted : checkReport pin policy report = .ok ()) :
    report.prepared.application = pin.application ∧
    report.subject = pin.subject ∧ report.target = pin.target ∧
    report.capability = pin.capability := by
  have matched : report.matchesGateway pin policy = true := by
    cases h : report.matchesGateway pin policy with
    | false => simp [checkReport, h] at accepted
    | true => rfl
  simp [Report.matchesGateway, FnConsumerOperation.Policy.matchesGateway] at matched
  aesop

def outboxPreimage (domain semantics : Digest) (application messageId : List UInt8) :
    List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, application, messageId)

def outboxHash (domain semantics : Digest) (application messageId : List UInt8) : Nat :=
  (Sp800185Cshake256.hash "DREGG.FN.ORIGIN-OUTBOX/v1".toUTF8.toList
    (outboxPreimage domain semantics application messageId)).digest.value

def outboxNonce (domain semantics : Digest) (value : Prepared) : Nat :=
  2 ^ 272 + outboxHash domain semantics value.application value.messageId

def outboxAtom (domain semantics : Digest) (value : Prepared) : AtomId :=
  ⟨⟨2 ^ 273 + outboxHash domain semantics value.application value.messageId⟩⟩

def marker (domain semantics : Digest) (subject : SubjectId) (value : Prepared) : Digest :=
  FnConsumerOperation.marker domain semantics subject (outboxNonce domain semantics value)

def outboxCommand (domain semantics : Digest) (report : Report) :
    DeclaredResourceController.Command :=
  ⟨report.subject, report.expectedAuthorityRoot,
    outboxNonce domain semantics report.prepared,
    [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
      .content ⟨[.createAtom (outboxAtom domain semantics report.prepared)
        (.inlineObject ⟨10⟩) (preparedCodec.encode report.prepared)]⟩, none⟩]⟩

theorem outboxCommand_exact_action (domain semantics : Digest) (report : Report) :
    (outboxCommand domain semantics report).targets =
      [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
        .content ⟨[.createAtom (outboxAtom domain semantics report.prepared)
          (.inlineObject ⟨10⟩) (preparedCodec.encode report.prepared)]⟩, none⟩] := rfl

/-- Reopen only a complete previously accepted signed outbox command. The
original signed roots are retained, and a later grant/policy revision does
not erase local custody of an already prepared R carrier. -/
def originalPrepared (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option Prepared := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  let .content content := target.payload | none
  let [.createAtom atom (.inlineObject ⟨10⟩) bytes] := content.actions | none
  if bytes.length > maxPreparedBytes then none else
  let prepared ← preparedCodec.decode bytes
  if prepared.valid && prepared.application == pin.application &&
      command.subject == pin.subject && target.target == pin.target &&
      target.capability == pin.capability &&
      atom == outboxAtom domain semantics prepared &&
      command.nonce == outboxNonce domain semantics prepared &&
      record.transactionId == marker domain semantics command.subject prepared &&
      FnConsumerOperation.exactSignedCommand signed.commandBytes
        (outboxCommand domain semantics
          ⟨prepared, [], command.subject, target.target, target.capability,
            command.expectedAuthorityRoot, target.expectedTargetRoot, true, true⟩) then
    some prepared
  else none

inductive Decision where
  | fresh (command : DeclaredResourceController.Command)
  | repeated
  | refused (detail : String)
  deriving Repr

def decide (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (report : Report) (accepted : List DurableReceiver.IntentRecord) : Decision :=
  let transaction := marker domain semantics report.subject report.prepared
  match accepted.find? (fun entry => entry.transactionId == transaction) with
  | none => .fresh (outboxCommand domain semantics report)
  | some original =>
      match originalPrepared pin domain semantics original with
      | some old =>
          if FnConsumerOperation.sameBytes (preparedCodec.encode old)
              (preparedCodec.encode report.prepared) then .repeated
          else .refused "R Message-ID already prepared with different exact content"
      | none => .refused "R Message-ID marker occupied by another transaction"

def Decision.intent (report : Report) : Decision → Option NativeObservationCodec.Intent
  | .fresh command =>
      some ⟨report.subject, command.nonce + 1,
        .prepare (.invoke (DeclaredResourceController.commandCodec.encode command)),
        [⟨.object, report.target, report.capability⟩]⟩
  | _ => none

def evaluateVerified (consumer : NativeHost.Config) (opened : NativeHost.Opened consumer)
    (pin : FnGatewayPolicy.Pin) (policy : FnConsumerOperation.Policy)
    (report : Report) : Except String Decision := do
  checkReport pin policy report
  FnGatewayPolicy.checkCurrent consumer opened pin
  pure (decide pin consumer.deployment.domain consumer.profile.semantics
    report opened.durable.image.accepted)

/-- The verified Q's In-Reply-To selects one historically accepted prepared
R, never an arbitrary config path or an unverified article claim. -/
def selectUniqueParent (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (parentMessageId : List UInt8) (accepted : List DurableReceiver.IntentRecord) :
    Except String (Prepared × DurableReceiver.IntentRecord) :=
  let candidates := accepted.filterMap fun record =>
    match originalPrepared pin domain semantics record with
    | some prepared =>
        if prepared.messageId == parentMessageId then some (prepared, record) else none
    | none => none
  match candidates with
  | [candidate] => .ok candidate
  | [] => .error "Q parent has no accepted prepared R outbox"
  | _ => .error "Q parent matches multiple accepted prepared R outboxes"

end Minidregg.Kernel.FnOriginOutbox
