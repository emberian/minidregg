/-
Ordered empty-page progress after a locally authenticated fn poll. Unlike the
historical tag9 signed DRC atom, this is a special Mini event19 admission; it
shares the predecessor nullifier with selected coverage event17. A receipt for
the old tag9 may be an audited historical anchor, never a claim that the old
receiver enforced this order at its original admission.
-/
import Kernel.FnConsumerFrontierCore

namespace Minidregg.Kernel.FnEmptyPollProgressV2

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
  toPosition : Nat
  predecessor : Option NativeHostCodec.Receipt
  cursor : List UInt8
  reportDigest : Digest
  deriving DecidableEq, Repr

def evidenceStream : StreamCodec Evidence :=
  StreamCodec.xmap
    (StreamCodec.product FnConsumerFrontierCore.keyStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product (StreamCodec.option NativeHostCodec.receiptStream)
            (StreamCodec.product bytesStream digestStream)))))
    (fun e => (e.key, e.fromPosition, e.toPosition, e.predecessor,
      e.cursor, e.reportDigest))
    (fun (key, fromPosition, toPosition, predecessor, cursor, reportDigest) =>
      ⟨key, fromPosition, toPosition, predecessor, cursor, reportDigest⟩)
    (by intro e; cases e; rfl)

def evidenceCodec : LawfulCodec Evidence :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/EMPTY-POLL-PROGRESS/v2".toUTF8.toList
      evidenceStream)

def maxEvidenceBytes : Nat := 4096

def Evidence.valid (e : Evidence) : Bool :=
  FnConsumerScope.validName e.key.application &&
  e.key.scope.valid &&
  !e.key.controlBinding.isEmpty && e.key.controlBinding.length ≤ 64 &&
  e.fromPosition < e.toPosition &&
  e.toPosition ≤ e.fromPosition + FnConsumerScope.maxPollScan &&
  e.toPosition ≤ 4294967295 &&
  !e.cursor.isEmpty && e.cursor.length ≤ 346 &&
  (evidenceCodec.encode e).length ≤ maxEvidenceBytes

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
    (fun (domain, semantics, evidence, registrationReceipt, gatewaySubject, gatewayTarget,
      gatewayCapability) =>
      ⟨domain, semantics, evidence, registrationReceipt, gatewaySubject, gatewayTarget,
        gatewayCapability⟩)
    (by intro spec; cases spec; rfl)

def specCodec : LawfulCodec Spec :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/EMPTY-POLL-SPEC/v2".toUTF8.toList specStream)

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
    (fun (spec, gatewayEnvelope, expectedAuthorityRoot, expectedTargetRoot) =>
      ⟨spec, gatewayEnvelope, expectedAuthorityRoot, expectedTargetRoot⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/EMPTY-POLL-INGRESS/v2".toUTF8.toList
      ingressStream)

def transactionId (spec : Spec) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/FN/EMPTY-POLL-TRANSACTION/v2".toUTF8.toList
    (specCodec.encode spec)).digest

def event (ingress : Ingress) : StableEvent where
  codecVersion := 19
  domain := ingress.spec.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/FN/EMPTY-POLL-EVENT/v2".toUTF8.toList
    (ingressCodec.encode ingress)).digest
  canonicalBytes := ingressCodec.encode ingress

def frontierNullifier (spec : Spec) : StableNullifier :=
  FnConsumerFrontierCore.frontierNullifier spec.domain spec.semantics spec.evidence.key
    spec.evidence.fromPosition spec.evidence.predecessor

def candidate (spec : Spec) : FnConsumerFrontierCore.Candidate :=
  { key := spec.evidence.key
    kind := .emptyV2
    fromPosition := spec.evidence.fromPosition
    toPosition := spec.evidence.toPosition
    selectedSequence := none
    predecessor := spec.evidence.predecessor }

def transition (spec : Spec) (receipt : NativeHostCodec.Receipt) :
    FnConsumerFrontierCore.Transition :=
  { key := spec.evidence.key
    kind := .emptyV2
    fromPosition := spec.evidence.fromPosition
    toPosition := spec.evidence.toPosition
    selectedSequence := none
    predecessor := spec.evidence.predecessor
    receipt := receipt }

theorem transition_candidate (spec : Spec) (receipt : NativeHostCodec.Receipt) :
    (transition spec receipt).candidate = candidate spec := rfl

end Minidregg.Kernel.FnEmptyPollProgressV2
