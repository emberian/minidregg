/- Exact historical v1 empty-page codec and full signed-command selector,
   factored below NativeHostReplay without changing accepted bytes. -/
import Kernel.FnConsumerScope
import Kernel.FnGatewayPolicy
import Kernel.DeclaredResourceController
import Kernel.DurableReceiver

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

abbrev Scope := FnConsumerScope.Scope
def scopeStream : StreamCodec Scope := FnConsumerScope.scopeStream

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
  expectedTargetRoot : Digest
  deriving Repr

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
def maxPollScan : Nat := FnConsumerScope.maxPollScan

def Scope.valid (scope : Scope) : Bool := FnConsumerScope.Scope.valid scope

def Evidence.valid (evidence : Evidence) : Bool :=
  FnConsumerScope.validName evidence.application &&
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
  DeclaredResourceController.transactionId domain semantics
    ⟨subject, progressNonce domain semantics evidence, [], none⟩

def progressCommand (domain semantics : Digest) (report : Report) :
    DeclaredResourceController.Command :=
  ⟨report.subject,
    progressNonce domain semantics report.evidence,
    [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
      .content ⟨[.createAtom (progressAtom domain semantics report.evidence)
        (.inlineObject ⟨9⟩) (evidenceCodec.encode report.evidence)]⟩, none, none, none⟩], none⟩

/-- Exactly the prior operation helper's byte-array command comparison.
    It avoids recursive equality on a potentially large signed command. -/
def exactSignedCommand (signedBytes : List UInt8)
    (expected : DeclaredResourceController.Command) : Bool :=
  decide (signedBytes.toByteArray =
    (DeclaredResourceController.commandCodec.encode expected).toByteArray)

theorem exactSignedCommand_sound (signedBytes : List UInt8)
    (command expected : DeclaredResourceController.Command)
    (decoded : DeclaredResourceController.commandCodec.decode signedBytes = some command)
    (matched : exactSignedCommand signedBytes expected = true) :
    command = expected := by
  have bytesEq : signedBytes = DeclaredResourceController.commandCodec.encode expected := by
    simpa only [exactSignedCommand, decide_eq_true_eq,
      List.toByteArray_inj] using matched
  rw [bytesEq, DeclaredResourceController.command_decode_encode] at decoded
  exact (Option.some.inj decoded).symm

/-- Historical recognition checks the entire signed command while taking
authority and target roots from that historical command, never the current
snapshot. In particular, target kind, schema, and observation grant cannot
be omitted by a command that merely carries the progress atom. -/
def matchesSignedShape (domain semantics : Digest)
    (signedBytes : List UInt8) (command : DeclaredResourceController.Command)
    (target : DeclaredResourceController.Target) (evidence : Evidence) : Bool :=
  exactSignedCommand signedBytes
    (progressCommand domain semantics
    ⟨evidence, command.subject, target.target, target.capability,
      target.expectedTargetRoot⟩)

theorem matchesSignedShape_sound (domain semantics : Digest)
    (signedBytes : List UInt8) (command : DeclaredResourceController.Command)
    (target : DeclaredResourceController.Target) (evidence : Evidence)
    (decoded : DeclaredResourceController.commandCodec.decode signedBytes = some command)
    (matched : matchesSignedShape domain semantics signedBytes command target evidence = true) :
    command = progressCommand domain semantics
      ⟨evidence, command.subject, target.target, target.capability,
        target.expectedTargetRoot⟩ := by
  exact exactSignedCommand_sound signedBytes command _
    decoded matched

/-- The entire native write is exactly one progress atom, with no application
operation, result, reply, or outbox action. -/
theorem progressCommand_exact_action (domain semantics : Digest) (report : Report) :
    (progressCommand domain semantics report).targets =
      [⟨.object, report.target, report.capability, 1, report.expectedTargetRoot,
        .content ⟨[.createAtom (progressAtom domain semantics report.evidence)
          (.inlineObject ⟨9⟩) (evidenceCodec.encode report.evidence)]⟩, none, none, none⟩] := rfl

/-- Historical recovery derives gateway identity from the signed original
call, never a current mutable atom or an unauthenticated caller claim. The
current law is intentionally not rechecked for a previously accepted skip. -/
structure OriginalGateway where
  evidence : Evidence
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  deriving DecidableEq, Repr

def originalSkipAnyGatewayWithIdentity (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) :
    Option OriginalGateway := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  let .content content := target.payload | none
  let [.createAtom atom (.inlineObject ⟨9⟩) bytes] := content.actions | none
  if bytes.length > maxEvidenceBytes then none else
  let evidence ← evidenceCodec.decode bytes
  if evidence.valid &&
      matchesSignedShape domain semantics signed.commandBytes command target evidence &&
      command.nonce == progressNonce domain semantics evidence &&
      atom == progressAtom domain semantics evidence &&
      record.transactionId == marker domain semantics command.subject evidence then
    some ⟨evidence, command.subject, target.target, target.capability⟩
  else none

def originalSkipAnyGateway (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option Evidence :=
  (originalSkipAnyGatewayWithIdentity domain semantics record).map
    OriginalGateway.evidence

/-- The configured gateway and exact scope are needed when a historical skip
is selected for recovery. Replay can separately recognize an older gateway's
strict command after an operator pin rotation. -/
def originalSkip (pin : FnGatewayPolicy.Pin) (scope : Scope)
    (domain semantics : Digest) (record : DurableReceiver.IntentRecord) :
    Option Evidence := do
  let original ← originalSkipAnyGatewayWithIdentity domain semantics record
  let evidence := original.evidence
  if evidence.application == pin.application && evidence.scope == scope then
    if original.subject == pin.subject && original.target == pin.target &&
        original.capability == pin.capability then some evidence else none
  else none

/-- Recognize a complete historical v1 skip without a fabricated receipt.
This is a fresh-admission cutover classifier, not an authorization to admit a
new v1 skip. Arbitrary DRC writes containing tag-9-looking bytes remain
unrecognized unless the exact signed command, marker, and gateway all match. -/
def recognizedLegacyRecord? (pin : FnGatewayPolicy.Pin)
    (domain semantics : Digest) (record : DurableReceiver.IntentRecord) :
    Option Evidence := do
  let (_, _, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  let .content content := target.payload | none
  let [.createAtom _ (.inlineObject ⟨9⟩) bytes] := content.actions | none
  if bytes.length > maxEvidenceBytes then none else
  let evidence ← evidenceCodec.decode bytes
  originalSkip pin evidence.scope domain semantics record

/-- Strictly classify v1 progress even when its historical gateway differs
from the current operator pin. This does not authorize that old gateway now. -/
def recognizedLegacyRecordAnyGateway? (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option Evidence :=
  originalSkipAnyGateway domain semantics record

/-- Fresh generic invoke must refuse exactly recognized old progress. Historical
replay still calls `originalSkip` on its already accepted records. -/
def recognizedLegacyIntent? (pin : FnGatewayPolicy.Pin)
    (domain semantics : Digest)
    (intent : DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes) :
    Option Evidence :=
  recognizedLegacyRecord? pin domain semantics
    (DurableReceiver.IntentRecord.ofIntent intent)

def recognizedLegacyIntentAnyGateway? (domain semantics : Digest)
    (intent : DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes) :
    Option Evidence :=
  recognizedLegacyRecordAnyGateway? domain semantics
    (DurableReceiver.IntentRecord.ofIntent intent)


end Minidregg.Kernel.FnConsumerProgress
