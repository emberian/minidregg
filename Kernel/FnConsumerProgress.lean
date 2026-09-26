/-
Durable progress for an observed empty fn consumer page. This is a local
processing declaration, not an application operation or fn-issued evidence.
Only the pinned gateway may write the record. The host must have obtained the
cursor from an actual trusted local poll and checked its scope and positions
before calling evaluateVerified; a user-supplied Bool is not an attestation.
-/
import Kernel.FnConsumerOperation

namespace Minidregg.Kernel.FnConsumerProgress

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

structure Scope where
  history : List UInt8
  incarnation : List UInt8
  consumer : List UInt8
  principal : List UInt8
  query : List UInt8
  queryVersion : Nat
  viewVersion : Nat
  registrationEpoch : Nat
  deriving DecidableEq, Repr

/-- The atom carries the exact continuation from a locally observed poll.
There is deliberately no article, operation, result or reply field. -/
structure Evidence where
  application : List UInt8
  scope : Scope
  cursor : List UInt8
  fromPosition : Nat
  toPosition : Nat
  controlBinding : List UInt8
  pollCallObserved : Bool
  deriving DecidableEq, Repr

structure Report where
  evidence : Evidence
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  expectedAuthorityRoot : Digest
  expectedTargetRoot : Digest
  deriving Repr

def scopeStream : StreamCodec Scope :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))
    (fun scope => (scope.history, scope.incarnation, scope.consumer,
      scope.principal, scope.query, scope.queryVersion, scope.viewVersion,
      scope.registrationEpoch))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2.1, wire.2.2.2.2.2.2.1,
      wire.2.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def evidenceStream : StreamCodec Evidence :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product scopeStream
      (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product bytesStream StreamCodec.bool))))))
    (fun evidence => (evidence.application, evidence.scope, evidence.cursor,
      evidence.fromPosition, evidence.toPosition, evidence.controlBinding,
      evidence.pollCallObserved))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2.1, wire.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def evidenceCodec : LawfulCodec Evidence :=
  NativeHostCodec.framed "DREGG/FN/EMPTY-PAGE-PROGRESS/v1".toUTF8.toList
    evidenceStream

def maxEvidenceBytes : Nat := 4096
def maxPollScan : Nat := 16

def Scope.valid (scope : Scope) : Bool :=
  [scope.history, scope.incarnation, scope.consumer, scope.principal,
    scope.query].all FnConsumerOperation.validName &&
  scope.queryVersion ≤ 4294967295 && scope.viewVersion ≤ 4294967295 &&
  scope.registrationEpoch > 0 && scope.registrationEpoch ≤ 4294967295

def Evidence.valid (evidence : Evidence) : Bool :=
  FnConsumerOperation.validName evidence.application &&
  evidence.scope.valid &&
  !evidence.cursor.isEmpty && evidence.cursor.length ≤ 346 &&
  evidence.fromPosition < evidence.toPosition &&
  evidence.toPosition ≤ evidence.fromPosition + maxPollScan &&
  evidence.toPosition ≤ 4294967295 &&
  evidence.pollCallObserved &&
  !evidence.controlBinding.isEmpty && evidence.controlBinding.length ≤ 64 &&
  (evidenceCodec.encode evidence).length ≤ maxEvidenceBytes

/-- Every admissible empty page records actual forward scan progress within
the selected local fn poll window; an idle cursor is not a skip record. -/
theorem Evidence.valid_scan_window (evidence : Evidence)
    (valid : evidence.valid = true) :
    evidence.pollCallObserved = true ∧
    evidence.fromPosition < evidence.toPosition ∧
    evidence.toPosition ≤ evidence.fromPosition + maxPollScan := by
  simp only [Evidence.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  aesop

def Report.matchesGateway (report : Report) (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) : Bool :=
  policy.matchesGateway pin &&
  report.evidence.application == policy.application &&
  report.subject == policy.subject && report.target == policy.target &&
  report.capability == policy.capability

def checkReport (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (report : Report) : Except String Unit :=
  if report.matchesGateway pin policy then
    if report.evidence.valid then .ok ()
    else .error "empty-page progress is unobserved, unscoped, or outside selected scan bound"
  else .error "empty-page progress differs from independently pinned gateway"

/-- An accepted report cannot select its own subject or resource. -/
theorem checkReport_pinned (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (report : Report)
    (accepted : checkReport pin policy report = .ok ()) :
    report.evidence.application = pin.application ∧
    report.subject = pin.subject ∧ report.target = pin.target ∧
    report.capability = pin.capability := by
  have pinned : report.matchesGateway pin policy = true := by
    cases hval : report.matchesGateway pin policy with
    | false => simp [checkReport, hval] at accepted
    | true => rfl
  simp [Report.matchesGateway, FnConsumerOperation.Policy.matchesGateway] at pinned
  aesop

def progressPreimage (domain semantics : Digest) (evidence : Evidence) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream
    evidenceStream)).encode (domain, semantics, evidence)

def progressHash (domain semantics : Digest) (evidence : Evidence) : Nat :=
  (Sp800185Cshake256.hash "DREGG.FN.EMPTY-PAGE-PROGRESS/v1".toUTF8.toList
    (progressPreimage domain semantics evidence)).digest.value

/-- Above the earlier operation, conflict and A-result nonce namespaces. -/
def progressNonce (domain semantics : Digest) (evidence : Evidence) : Nat :=
  2 ^ 270 + progressHash domain semantics evidence

def progressAtom (domain semantics : Digest) (evidence : Evidence) : AtomId :=
  ⟨⟨2 ^ 271 + progressHash domain semantics evidence⟩⟩

def marker (domain semantics : Digest) (subject : SubjectId)
    (evidence : Evidence) : Digest :=
  FnConsumerOperation.marker domain semantics subject
    (progressNonce domain semantics evidence)

def progressCommand (domain semantics : Digest) (report : Report) :
    DeclaredResourceController.Command :=
  ⟨report.subject, report.expectedAuthorityRoot,
    progressNonce domain semantics report.evidence,
    [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
      .content ⟨[.createAtom (progressAtom domain semantics report.evidence)
        (.inlineObject ⟨9⟩) (evidenceCodec.encode report.evidence)]⟩, none⟩]⟩

/-- Historical recognition checks the entire signed command while taking
authority and target roots from that historical command, never the current
snapshot. In particular, target kind, schema, and observation grant cannot
be omitted by a command that merely carries the progress atom. -/
def matchesSignedShape (domain semantics : Digest)
    (signedBytes : List UInt8) (command : DeclaredResourceController.Command)
    (target : DeclaredResourceController.Target) (evidence : Evidence) : Bool :=
  FnConsumerOperation.exactSignedCommand signedBytes
    (progressCommand domain semantics
    ⟨evidence, command.subject, target.target, target.capability,
      command.expectedAuthorityRoot, target.expectedTargetRoot⟩)

theorem matchesSignedShape_sound (domain semantics : Digest)
    (signedBytes : List UInt8) (command : DeclaredResourceController.Command)
    (target : DeclaredResourceController.Target) (evidence : Evidence)
    (decoded : DeclaredResourceController.commandCodec.decode signedBytes = some command)
    (matched : matchesSignedShape domain semantics signedBytes command target evidence = true) :
    command = progressCommand domain semantics
      ⟨evidence, command.subject, target.target, target.capability,
        command.expectedAuthorityRoot, target.expectedTargetRoot⟩ := by
  exact FnConsumerOperation.exactSignedCommand_sound signedBytes command _
    decoded matched

/-- The entire native write is exactly one progress atom, with no application
operation, result, reply, or outbox action. -/
theorem progressCommand_exact_action (domain semantics : Digest) (report : Report) :
    (progressCommand domain semantics report).targets =
      [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
        .content ⟨[.createAtom (progressAtom domain semantics report.evidence)
          (.inlineObject ⟨9⟩) (evidenceCodec.encode report.evidence)]⟩, none⟩] := rfl

/-- Historical recovery derives gateway identity from the signed original
call, never a current mutable atom or an unauthenticated caller claim. The
current law is intentionally not rechecked for a previously accepted skip. -/
def originalSkip (pin : FnGatewayPolicy.Pin) (scope : Scope)
    (domain semantics : Digest) (record : DurableReceiver.IntentRecord) :
    Option Evidence := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  let .content content := target.payload | none
  let [.createAtom atom (.inlineObject ⟨9⟩) bytes] := content.actions | none
  if bytes.length > maxEvidenceBytes then none else
  let evidence ← evidenceCodec.decode bytes
  if evidence.application == pin.application && evidence.scope == scope &&
      evidence.valid && command.subject == pin.subject &&
      target.target == pin.target && target.capability == pin.capability &&
      matchesSignedShape domain semantics signed.commandBytes command target evidence &&
      command.nonce == progressNonce domain semantics evidence &&
      atom == progressAtom domain semantics evidence &&
      record.transactionId == marker domain semantics command.subject evidence then
    some evidence
  else none

inductive Decision where
  | fresh (command : DeclaredResourceController.Command)
  | repeated
  | refused (detail : String)
  deriving Repr

def decide (pin : FnGatewayPolicy.Pin) (scope : Scope)
    (domain semantics : Digest) (report : Report)
    (accepted : List DurableReceiver.IntentRecord) : Decision :=
  let transaction := marker domain semantics report.subject report.evidence
  match accepted.find? (fun entry => entry.transactionId == transaction) with
  | none => .fresh (progressCommand domain semantics report)
  | some original =>
      if originalSkip pin scope domain semantics original == some report.evidence then
        .repeated
      else .refused "empty-page progress marker occupied by another transaction"

def Decision.intent (report : Report) : Decision → Option NativeObservationCodec.Intent
  | .fresh command =>
      some ⟨report.subject, command.nonce + 1,
        .prepare (.invoke (DeclaredResourceController.commandCodec.encode command)),
        [⟨.object, report.target, report.capability⟩]⟩
  | _ => none

def evaluateVerified (consumer : NativeHost.Config) (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (scope : Scope) (report : Report)
    (opened : NativeHost.Opened consumer) : Except String Decision := do
  checkReport pin policy report
  unless report.evidence.scope == scope do
    throw "empty-page progress scope differs from independently selected fn consumer"
  FnGatewayPolicy.checkCurrent consumer opened pin
  pure (decide pin scope consumer.deployment.domain consumer.profile.semantics
    report opened.durable.image.accepted)

end Minidregg.Kernel.FnConsumerProgress
