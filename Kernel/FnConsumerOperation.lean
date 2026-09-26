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
import Kernel.FnGatewayPolicy
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

/-- Exact bytes returned by one local fn consumer poll, plus the ACL2-owned
projection that was joined to the independently verified carrier. These bytes
are retained as evidence in Mini's atomic operation or variation transaction;
only the authenticated local poll transport can establish Store provenance. -/
structure StorePollInbox where
  cursor : List UInt8
  event : List UInt8
  /-- Host observation of the actual trusted local-control poll route. This
  is not a portable cryptographic attestation of fn Store history. -/
  pollCallObserved : Bool
  sourceIdentity : List UInt8
  sequence : Nat
  transactionId : Nat
  messageId : List UInt8
  verdictPrincipal : List UInt8
  verdictEvent : List UInt8
  /-- Mini-owned binding to the operator-selected fn executable/transport and
  exact control endpoint observed by this process. Exact paths are retained
  separately in the run evidence; their hash is not remote authentication. -/
  controlBinding : List UInt8
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
  storePoll : Option StorePollInbox := none
  deriving Repr

/-- Local operator selection. It is not accepted from the fetched fn article. -/
structure Policy where
  application : List UInt8
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  deriving DecidableEq, Repr

def Policy.matchesGateway (policy : Policy) (pin : FnGatewayPolicy.Pin) : Bool :=
  policy.application == pin.application && policy.subject == pin.subject &&
  policy.target == pin.target && policy.capability == pin.capability

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

/-- Large retained package and carrier bytes are compared iteratively. The
ordinary list equality over a full portable article exhausts Lean's stack. -/
def sameBytes (left right : List UInt8) : Bool :=
  decide (left.toByteArray = right.toByteArray)

def PortableInbox.same (left right : PortableInbox) : Bool :=
  sameBytes left.carrier right.carrier &&
  left.sourceIdentity == right.sourceIdentity &&
  left.principal == right.principal &&
  left.edPublicKey == right.edPublicKey &&
  left.mlPublicKey == right.mlPublicKey

def samePortableInbox : Option PortableInbox → Option PortableInbox → Bool
  | none, none => true
  | some left, some right => left.same right
  | _, _ => false

def StorePollInbox.same (left right : StorePollInbox) : Bool :=
  left.cursor == right.cursor && sameBytes left.event right.event &&
  left.pollCallObserved == right.pollCallObserved &&
  left.sourceIdentity == right.sourceIdentity &&
  left.sequence == right.sequence && left.transactionId == right.transactionId &&
  left.messageId == right.messageId &&
  left.verdictPrincipal == right.verdictPrincipal &&
  sameBytes left.verdictEvent right.verdictEvent &&
  left.controlBinding == right.controlBinding

def sameStorePollInbox : Option StorePollInbox → Option StorePollInbox → Bool
  | none, none => true
  | some left, some right => left.same right
  | _, _ => false

def ConflictEvidence.same (left right : ConflictEvidence) : Bool :=
  left.application == right.application && left.operation == right.operation &&
  left.provenance == right.provenance && sameBytes left.package right.package

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

def storePollStream : StreamCodec StorePollInbox :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.bool (StreamCodec.product bytesStream
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
          (StreamCodec.product bytesStream
            (StreamCodec.product bytesStream
              (StreamCodec.product bytesStream bytesStream)))))))))
    (fun value => (value.cursor, value.event, value.pollCallObserved,
      value.sourceIdentity, value.sequence, value.transactionId,
      value.messageId, value.verdictPrincipal, value.verdictEvent,
      value.controlBinding))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2.1, value.2.2.2.2.2.1, value.2.2.2.2.2.2.1,
      value.2.2.2.2.2.2.2.1, value.2.2.2.2.2.2.2.2.1,
      value.2.2.2.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def storePollCodec : LawfulCodec StorePollInbox :=
  NativeHostCodec.framed "DREGG/FN/STORE-POLL-INBOX/v3".toUTF8.toList storePollStream

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
-- The native V2 binding retains the verified package; the portable inbox
-- retains the exact fn carrier. These ceilings derive from the same envelope
-- used by the host reader and are checked before historical atom decoding.
def maxBindingBytes : Nat := FnEvidenceCodec.maxPackageBytes + 16384
def maxInboxBytes : Nat := FnEvidenceCodec.maxPortableInboxBytes
-- This is Mini's selected qualified poll-reader profile. Current fn HEAD has
-- wider potential Store/operator limits; that does not silently enlarge this
-- Mini reader without a matching selected qualification.
def maxStoreEventBytes : Nat := FnEvidenceCodec.maxStorePollEventBytes
def maxStoreInboxBytes : Nat := FnEvidenceCodec.maxStorePollInboxBytes

/-- Mini's local reference to the exact retained fn verdict bytes and Store
coordinates. This is a content binding, not an fn-issued Store identifier. -/
def storePollVerdictRef (inbox : StorePollInbox) : List UInt8 :=
  let digest := Sp800185Cshake256.hash
    "DREGG.FN.STORE-VERDICT-REF/v1".toUTF8.toList
    ((StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat bytesStream)).encode
        (inbox.sequence, inbox.transactionId, inbox.verdictEvent))
  digestStream.encode digest.digest

/-- Bind the exact chosen control endpoint to the executable or transport
selection before writing Mini's accepted poll atom. -/
def pollControlBinding (fnBinary controlPath : String) : List UInt8 :=
  let digest := Sp800185Cshake256.hash
    "DREGG.FN.POLL-CONTROL/v1".toUTF8.toList
    ((StreamCodec.product bytesStream bytesStream).encode
      (fnBinary.toUTF8.toList, controlPath.toUTF8.toList))
  digestStream.encode digest.digest

def PortableInbox.valid (inbox : PortableInbox)
    (expectedSource : List UInt8) : Bool :=
  !inbox.carrier.isEmpty &&
  inbox.carrier.length ≤ FnEvidenceCodec.maxCarrierBytes &&
  inbox.sourceIdentity.length == 48 &&
  inbox.sourceIdentity == expectedSource &&
  inbox.principal.length == 32 && inbox.edPublicKey.length == 32 &&
  inbox.mlPublicKey.length == 1952 &&
  (portableInboxCodec.encode inbox).length ≤ maxInboxBytes

def StorePollInbox.valid (inbox : StorePollInbox)
    (expectedSource expectedVerdictRef : List UInt8) : Bool :=
  !inbox.cursor.isEmpty && inbox.cursor.length ≤ 346 &&
  !inbox.event.isEmpty && inbox.event.length ≤ maxStoreEventBytes &&
  inbox.sourceIdentity == expectedSource && inbox.sourceIdentity.length == 48 &&
  !inbox.messageId.isEmpty && inbox.messageId.length ≤ 256 &&
  inbox.verdictPrincipal.length == 32 &&
  !inbox.verdictEvent.isEmpty &&
  inbox.verdictEvent.length ≤ FnEvidenceCodec.maxHistoricalVerdictEventBytes &&
  (if inbox.pollCallObserved then
    !inbox.controlBinding.isEmpty && inbox.controlBinding.length ≤ 64
   else inbox.controlBinding.isEmpty) &&
  storePollVerdictRef inbox == expectedVerdictRef &&
  inbox.sequence ≤ 4294967295 && inbox.transactionId ≤ 4294967295 &&
  (storePollCodec.encode inbox).length ≤ maxStoreInboxBytes

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
  match report.storePoll with
  | none => pure ()
  | some inbox =>
      unless report.portableInbox.isSome &&
          inbox.valid report.provenance.sourceIdentity
            report.provenance.fnVerdictRef do
        throw "fn Store poll inbox is mismatched or outside Mini's bounded profile"

def checkPolicy (policy : Policy) (report : Report) : Except String Unit := do
  unless report.application == policy.application &&
      report.subject == policy.subject && report.target == policy.target &&
      report.capability == policy.capability do
    throw "report differs from operator-selected consumer namespace and grant"

def checkGateway (pin : FnGatewayPolicy.Pin) (policy : Policy)
    (report : Report) : Except String Unit := do
  unless policy.matchesGateway pin do
    throw "consumer policy differs from independently pinned fn gateway"
  checkPolicy policy report

def operationPreimage (domain semantics : Digest) (application operation : List UInt8) :
    List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product bytesStream bytesStream))).encode
    (domain, semantics, application, operation)

/-- Stable application operation derived once from the independently verified
Mini origin. Both the B request and A reply consumer use this same owner. -/
def originOperation (origin : FnEvidenceCodec.Package) : List UInt8 :=
  let originKey := (StreamCodec.product digestStream
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream digestStream))).encode
        (origin.domain, origin.semantics, origin.genesisPin,
          origin.originalReceipt.transactionId)
  let operationDigest := Sp800185Cshake256.hash
    "DREGG.FN.MINI-ORIGIN-OPERATION/v1".toUTF8.toList originKey
  (String.ofList (Nat.toDigits 16 operationDigest.digest.value)).toUTF8.toList

/-- Source identity is deliberately absent. The even tag is reserved for a
unique application effect; odd nonces are for distinct conflict evidence. -/
def operationNonce (domain semantics : Digest) (application operation : List UInt8) : Nat :=
  2 * (Sp800185Cshake256.hash "DREGG.FN.OPERATION/v1".toUTF8.toList
    (operationPreimage domain semantics application operation)).digest.value

def conflictPreimage (domain semantics : Digest) (report : Report) : List UInt8 :=
  operationPreimage domain semantics report.application report.operation ++
    provenanceStream.encode report.provenance ++
    (match report.portableInbox with
     | none => []
     | some inbox => portableInboxCodec.encode inbox) ++
    (match report.storePoll with
     | none => []
     | some inbox => storePollCodec.encode inbox)

def conflictNonce (domain semantics : Digest) (report : Report) : Nat :=
  2 * (Sp800185Cshake256.hash "DREGG.FN.CONFLICT/v1".toUTF8.toList
    (conflictPreimage domain semantics report)).digest.value + 1

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

/-- cSHAKE emits less than 2^256, so every older atom is below 2^259.
These high atom IDs preserve all previous operation/reply/inbox identities. -/
def storeOperationAtom (domain semantics : Digest)
    (application operation : List UInt8) : AtomId :=
  ⟨⟨2 ^ 259 + 4 *
    (Sp800185Cshake256.hash "DREGG.FN.STORE-POLL-OP/v1".toUTF8.toList
      (operationPreimage domain semantics application operation)).digest.value⟩⟩

def storeConflictAtom (domain semantics : Digest) (report : Report) : AtomId :=
  ⟨⟨2 ^ 259 + 4 *
    (Sp800185Cshake256.hash "DREGG.FN.STORE-POLL-CONFLICT/v1".toUTF8.toList
      (operationPreimage domain semantics report.application report.operation ++
        provenanceStream.encode report.provenance ++
        (match report.storePoll with
         | none => []
         | some inbox => storePollCodec.encode inbox))).digest.value + 1⟩⟩

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
  let actions := actions ++ match report.storePoll with
    | none => []
    | some inbox =>
        [.createAtom (storeOperationAtom domain semantics report.application report.operation)
          (.inlineObject ⟨5⟩) (storePollCodec.encode inbox)]
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
  let actions := actions ++ match report.storePoll with
    | none => []
    | some inbox =>
        [.createAtom (storeConflictAtom domain semantics report)
          (.inlineObject ⟨5⟩) (storePollCodec.encode inbox)]
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
The prior reply remains recoverable from durable history after a later Mini
grant or policy revision. This raw decoder is private: public recovery also
requires the independently configured gateway identity. -/
private def originalBindingWithInboxRaw (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) :
    Option (Binding × Option PortableInbox × Option StorePollInbox) := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  match command.targets with
  | [target] =>
      match target.payload with
      | .content content =>
          let (atom, bytes, outbox, replyBytes, inboxAction, storeAction) ←
            match content.actions with
            | [.createAtom atom (.inlineObject ⟨1⟩) bytes,
               .createAtom outbox (.inlineObject ⟨2⟩) replyBytes] =>
                some (atom, bytes, outbox, replyBytes, none, none)
            | [.createAtom atom (.inlineObject ⟨1⟩) bytes,
               .createAtom outbox (.inlineObject ⟨2⟩) replyBytes,
               .createAtom inboxAtom (.inlineObject ⟨4⟩) inboxBytes] =>
                some (atom, bytes, outbox, replyBytes,
                  some (inboxAtom, inboxBytes), none)
            | [.createAtom atom (.inlineObject ⟨1⟩) bytes,
               .createAtom outbox (.inlineObject ⟨2⟩) replyBytes,
               .createAtom inboxAtom (.inlineObject ⟨4⟩) inboxBytes,
               .createAtom storeAtom (.inlineObject ⟨5⟩) storeBytes] =>
                some (atom, bytes, outbox, replyBytes,
                  some (inboxAtom, inboxBytes), some (storeAtom, storeBytes))
            | _ => none
          if bytes.length > maxBindingBytes then none else
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
          let storeInbox ← match storeAction with
            | none => some none
            | some (storeAtom, storeBytes) => do
                if storeBytes.length > maxStoreInboxBytes || inbox.isNone then none else
                let storeInbox ← storePollCodec.decode storeBytes
                if storeAtom == storeOperationAtom domain semantics
                    binding.application binding.operation &&
                    storeInbox.valid binding.provenance.sourceIdentity
                      binding.provenance.fnVerdictRef then
                  some (some storeInbox)
                else none
          if atom == operationAtom domain semantics binding.application binding.operation &&
              outbox == replyAtom domain semantics binding.application binding.operation &&
              reply == binding.reply &&
              reply.application == binding.application &&
              reply.operation == binding.operation &&
              reply.sourceIdentity == binding.provenance.sourceIdentity &&
              command.nonce == operationNonce domain semantics
                binding.application binding.operation then
            some (binding, inbox, storeInbox)
          else none
      | _ => none
  | _ => none

/-- Historical recovery requires the signed subject, resource and capability
to match the configured gateway. It intentionally does not recheck the current
mutation law: an exact previously admitted fn position may still be ACKed
after the Mini gateway grant is revoked. -/
def originalBindingWithInbox (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) :
    Option (Binding × Option PortableInbox × Option StorePollInbox) := do
  let binding ← originalBindingWithInboxRaw domain semantics record
  let (_, _, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  if binding.1.application == pin.application && command.subject == pin.subject &&
      target.target == pin.target && target.capability == pin.capability then
    some binding
  else none

def originalBinding (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option Binding :=
  (originalBindingWithInbox pin domain semantics record).map Prod.fst

/-- A later operator policy cannot silently move an already bound operation
to another local subject, target, or capability. The original accepted
signed call, not caller metadata, supplies this historical grant context. -/
private def originalBindingGrant (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) :
    Option (Binding × SubjectId × Nat × CapabilityId) := do
  let binding ← (originalBindingWithInboxRaw domain semantics record).map Prod.fst
  let (_, _, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  some (binding, command.subject, target.target, target.capability)

private def checkHistoricalPolicy (domain semantics : Digest) (policy : Policy)
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

private def originalConflictWithInboxRaw (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) :
    Option (ConflictEvidence × Option PortableInbox × Option StorePollInbox) := do
  let (recordDomain, recordSemantics, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  if recordDomain != domain || recordSemantics != semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  match command.targets with
  | [target] =>
      match target.payload with
      | .content content =>
          let (atom, bytes, inboxAction, storeAction) ← match content.actions with
            | [.createAtom atom (.inlineObject ⟨3⟩) bytes] =>
                some (atom, bytes, none, none)
            | [.createAtom atom (.inlineObject ⟨3⟩) bytes,
               .createAtom inboxAtom (.inlineObject ⟨4⟩) inboxBytes] =>
                some (atom, bytes, some (inboxAtom, inboxBytes), none)
            | [.createAtom atom (.inlineObject ⟨3⟩) bytes,
               .createAtom inboxAtom (.inlineObject ⟨4⟩) inboxBytes,
               .createAtom storeAtom (.inlineObject ⟨5⟩) storeBytes] =>
                some (atom, bytes, some (inboxAtom, inboxBytes),
                  some (storeAtom, storeBytes))
            | _ => none
          if bytes.length > maxBindingBytes then none else
          let evidence ← conflictCodec.decode bytes
          let inbox ← match inboxAction with
            | none => some none
            | some (_, inboxBytes) => do
                if inboxBytes.length > maxInboxBytes then none else
                let inbox ← portableInboxCodec.decode inboxBytes
                if inbox.valid evidence.provenance.sourceIdentity then
                  some (some inbox)
                else none
          let storeInbox ← match storeAction with
            | none => some none
            | some (_, storeBytes) => do
                if storeBytes.length > maxStoreInboxBytes || inbox.isNone then none else
                let storeInbox ← storePollCodec.decode storeBytes
                if storeInbox.valid evidence.provenance.sourceIdentity
                    evidence.provenance.fnVerdictRef then
                  some (some storeInbox)
                else none
          let report : Report :=
            { application := evidence.application, operation := evidence.operation,
              provenance := evidence.provenance, package := evidence.package,
              subject := command.subject, target := target.target,
              capability := target.capability,
              expectedAuthorityRoot := command.expectedAuthorityRoot,
              expectedTargetRoot := target.expectedTargetRoot,
              portableInbox := inbox, storePoll := storeInbox }
          if atom == conflictAtom domain semantics report &&
              (inboxAction.isNone ||
                inboxAction.any (fun pair =>
                  pair.1 == conflictInboxAtom domain semantics report)) &&
              (storeAction.isNone ||
                storeAction.any (fun pair =>
                  pair.1 == storeConflictAtom domain semantics report)) &&
              command.nonce == conflictNonce domain semantics report then
            some (evidence, inbox, storeInbox)
          else none
      | _ => none
  | _ => none

def originalConflictWithInbox (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) :
    Option (ConflictEvidence × Option PortableInbox × Option StorePollInbox) := do
  let conflict ← originalConflictWithInboxRaw domain semantics record
  let (_, _, signed) ←
    DeclaredResourceController.decodeSignedBytes record.event.canonicalBytes
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  let [target] := command.targets | none
  if conflict.1.application == pin.application && command.subject == pin.subject &&
      target.target == pin.target && target.capability == pin.capability then
    some conflict
  else none

def originalConflict (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) : Option ConflictEvidence :=
  (originalConflictWithInbox pin domain semantics record).map Prod.fst

def decide (pin : FnGatewayPolicy.Pin) (domain semantics : Digest)
    (report : Report) (receipt : Receipt)
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
      match originalBindingWithInbox pin domain semantics original with
      | none => .refused "operation marker occupied by nonconsumer transaction"
      | some (binding, originalInbox, originalStore) =>
          if binding.application != report.application ||
              binding.operation != report.operation then
            .refused "operation marker collision or foreign binding"
          else if binding.provenance == report.provenance &&
              sameBytes binding.package report.package &&
              samePortableInbox originalInbox report.portableInbox &&
              sameStorePollInbox originalStore report.storePoll then
            .repeated binding.reply
          else
            let sameSource :=
              binding.provenance.sourceIdentity == report.provenance.sourceIdentity &&
              sameBytes binding.package report.package
            let conflictTransaction := marker domain semantics report.subject
              (conflictNonce domain semantics report)
            match accepted.find? (fun entry => entry.transactionId == conflictTransaction) with
            | none =>
                if sameSource then .carrierVariation
                  (conflictCommand domain semantics report) binding.reply
                else .conflict (conflictCommand domain semantics report)
            | some conflict =>
                if (match originalConflictWithInbox pin domain semantics conflict with
                    | some (evidence, inbox, store) =>
                        evidence.same ⟨report.application, report.operation,
                          report.provenance, report.package⟩ &&
                        samePortableInbox inbox report.portableInbox &&
                        sameStorePollInbox store report.storePoll
                    | none => false) then
                  if sameSource then .carrierVariationRecorded binding.reply
                  else .conflictRecorded
                else .refused "conflict marker occupied by different evidence"

def Decision.intent (report : Report) : Decision → Option NativeObservationCodec.Intent
  | .fresh command _ | .conflict command | .carrierVariation command _ =>
      some ⟨report.subject, command.nonce + 1,
        .prepare (.invoke (DeclaredResourceController.commandCodec.encode command)),
        [⟨.object, report.target, report.capability⟩]⟩
  | _ => none

def evaluateVerified (consumer : NativeHost.Config) (pin : FnGatewayPolicy.Pin)
    (policy : Policy)
    (report : Report) (receipt : Receipt) (opened : NativeHost.Opened consumer) :
    Except String Decision := do
  checkReport report
  checkGateway pin policy report
  FnGatewayPolicy.checkCurrent consumer opened pin
  checkHistoricalPolicy consumer.deployment.domain consumer.profile.semantics
    policy report opened.durable.image.accepted
  pure (decide pin consumer.deployment.domain consumer.profile.semantics
    report receipt opened.durable.image.accepted)

/-- The synthetic adapter independently verifies the origin and reopens
current consumer history. The portable native route passes those already
verified values to evaluateVerified without replaying either twice. -/
def evaluate (origin consumer : NativeHost.Config) (pin : FnGatewayPolicy.Pin)
    (policy : Policy) (report : Report) :
    IO (Except String Decision) := do
  match checkReport report with
  | .error detail => return .error detail
  | .ok () => pure ()
  match checkGateway pin policy report with
  | .error detail => return .error detail
  | .ok () => pure ()
  let receipt ← match ← FnEvidence.verify origin report.package with
    | .error detail => return .error s!"Mini evidence: {detail}"
    | .ok receipt => pure receipt
  let opened ← match ← NativeHost.openExisting consumer with
    | .error detail => return .error s!"consumer history: {detail}"
    | .ok opened => pure opened
  return evaluateVerified consumer pin policy report receipt opened

end Minidregg.Kernel.FnConsumerOperation
