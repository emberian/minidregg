/-
Canonical gateway testimony for one locally selected fn article. The fn poll is
an operator-pinned local observation, not a proof that a remote service offered
every article. Native Host authors the spec from the exact retained poll and
projection; Mini admission separately checks the configured gateway signature,
current gateway law, accepted owner release, and unified consumer frontier.
-/
import Kernel.FnConsumerFrontierCore
import Kernel.FnSelectiveReleaseIngress

namespace Minidregg.Kernel.FnSelectedPollCoverage

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.TypedAuthorizationRequestCodec
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Evidence where
  key : FnConsumerFrontierCore.Key
  fromPosition : Nat
  selectedSequence : Nat
  toPosition : Nat
  predecessor : Option NativeHostCodec.Receipt
  cursor : List UInt8
  reportDigest : Digest
  sourceDigest : Digest
  messageId : List UInt8
  releaseReceipt : NativeHostCodec.Receipt
  releaseKey : Digest
  deriving DecidableEq, Repr

def evidenceStream : StreamCodec Evidence :=
  StreamCodec.xmap
    (StreamCodec.product FnConsumerFrontierCore.keyStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product (StreamCodec.option NativeHostCodec.receiptStream)
              (StreamCodec.product bytesStream
                (StreamCodec.product digestStream
                  (StreamCodec.product digestStream
                    (StreamCodec.product bytesStream
                      (StreamCodec.product NativeHostCodec.receiptStream
                        digestStream))))))))))
    (fun e => (e.key, e.fromPosition, e.selectedSequence, e.toPosition,
      e.predecessor, e.cursor, e.reportDigest, e.sourceDigest, e.messageId,
      e.releaseReceipt, e.releaseKey))
    (fun (key, fromPosition, selectedSequence, toPosition, predecessor,
      cursor, reportDigest, sourceDigest, messageId, releaseReceipt,
      releaseKey) =>
      ⟨key, fromPosition, selectedSequence, toPosition, predecessor, cursor,
        reportDigest, sourceDigest, messageId, releaseReceipt, releaseKey⟩)
    (by intro e; cases e; rfl)

def evidenceCodec : LawfulCodec Evidence :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/SELECTED-POLL-COVERAGE/v2".toUTF8.toList
      evidenceStream)

def maxEvidenceBytes : Nat := 8192

def Evidence.valid (evidence : Evidence) : Bool :=
  FnConsumerScope.validName evidence.key.application &&
  evidence.key.scope.valid &&
  !evidence.key.controlBinding.isEmpty &&
  evidence.key.controlBinding.length ≤ 64 &&
  evidence.fromPosition ≤ evidence.selectedSequence &&
  evidence.selectedSequence + 1 == evidence.toPosition &&
  evidence.fromPosition < evidence.toPosition &&
  evidence.toPosition ≤ evidence.fromPosition + FnConsumerScope.maxPollScan &&
  evidence.toPosition ≤ 4294967295 &&
  !evidence.cursor.isEmpty && evidence.cursor.length ≤ 346 &&
  !evidence.messageId.isEmpty && evidence.messageId.length ≤ 512 &&
  evidence.releaseReceipt.acceptedCount > 0 &&
  (evidenceCodec.encode evidence).length ≤ maxEvidenceBytes

structure Spec where
  domain : Digest
  semantics : Digest
  evidence : Evidence
  registrationReceipt : NativeHostCodec.Receipt
  gatewaySubject : SubjectId
  gatewayTarget : Nat
  gatewayCapability : CapabilityId
  deriving DecidableEq, Repr

def Spec.keyMatchesGateway (spec : Spec) : Bool :=
  spec.evidence.key.gatewaySubject == spec.gatewaySubject &&
  spec.evidence.key.gatewayTarget == spec.gatewayTarget &&
  spec.evidence.key.gatewayCapability == spec.gatewayCapability

def specStream : StreamCodec Spec :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product evidenceStream
          (StreamCodec.product NativeHostCodec.receiptStream
            (StreamCodec.product subjectIdStream
              (StreamCodec.product StreamCodec.nat
                CredentialAuthorityEntryCodec.capabilityIdStream))))))
    (fun spec => (spec.domain, spec.semantics, spec.evidence,
      spec.registrationReceipt,
      spec.gatewaySubject, spec.gatewayTarget, spec.gatewayCapability))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2.1, wire.2.2.2.2.2.2⟩)
    (by intro spec; cases spec; rfl)

def specCodec : LawfulCodec Spec :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/SELECTED-POLL-SPEC/v2".toUTF8.toList
      specStream)

structure Ingress where
  spec : Spec
  gatewayEnvelope : List UInt8
  expectedAuthorityRoot : Digest
  expectedTargetRoot : Digest
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product specStream
      (StreamCodec.product bytesStream
        (StreamCodec.product digestStream digestStream)))
    (fun ingress => (ingress.spec, ingress.gatewayEnvelope,
      ingress.expectedAuthorityRoot, ingress.expectedTargetRoot))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/SELECTED-POLL-INGRESS/v2".toUTF8.toList
      ingressStream)

def transactionId (spec : Spec) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/FN/SELECTED-POLL-TRANSACTION/v2".toUTF8.toList
    (specCodec.encode spec)).digest

def event (ingress : Ingress) : StableEvent where
  codecVersion := 17
  domain := ingress.spec.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/FN/SELECTED-POLL-EVENT/v2".toUTF8.toList
    (ingressCodec.encode ingress)).digest
  canonicalBytes := ingressCodec.encode ingress

/-- The caller supplies the actual Mini deployment domain and semantics, not
an ingress-controlled release key. The same function is used for v2 empty-page
progress, so two decisions from one frontier tip conflict durably. -/
def frontierNullifier (spec : Spec) : StableNullifier :=
  FnConsumerFrontierCore.frontierNullifier spec.domain spec.semantics spec.evidence.key
    spec.evidence.fromPosition spec.evidence.predecessor

def candidate (spec : Spec) : FnConsumerFrontierCore.Candidate :=
  { key := spec.evidence.key
    kind := .selectedV2
    fromPosition := spec.evidence.fromPosition
    toPosition := spec.evidence.toPosition
    selectedSequence := some spec.evidence.selectedSequence
    predecessor := spec.evidence.predecessor }

def transition (spec : Spec) (receipt : NativeHostCodec.Receipt) :
    FnConsumerFrontierCore.Transition :=
  { key := spec.evidence.key
    kind := .selectedV2
    fromPosition := spec.evidence.fromPosition
    toPosition := spec.evidence.toPosition
    selectedSequence := some spec.evidence.selectedSequence
    predecessor := spec.evidence.predecessor
    receipt := receipt }

theorem transition_candidate (spec : Spec) (receipt : NativeHostCodec.Receipt) :
    (transition spec receipt).candidate = candidate spec := rfl

end Minidregg.Kernel.FnSelectedPollCoverage
