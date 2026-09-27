/-
One durable owner for a qualified fn consumer namespace. This gateway-signed
special event binds the configured Mini gateway to the fn scope and control
binding before ordered event17/19 progress. The nullifier excludes the gateway
grant, so changing that grant cannot silently register the same namespace
again. Historical v1 adoption is explicit by exact predecessor receipt; this
record alone does not certify that v1 enforced ordering when admitted.
-/
import Kernel.FnConsumerFrontierCore

namespace Minidregg.Kernel.FnConsumerNamespaceRegistration

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.TypedAuthorizationRequestCodec
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Spec where
  domain : Digest
  semantics : Digest
  consumerNamespace : FnConsumerFrontierCore.Namespace
  gatewaySubject : SubjectId
  gatewayTarget : Nat
  gatewayCapability : CapabilityId
  initialPosition : Nat
  legacyAnchor : Option NativeHostCodec.Receipt
  deriving DecidableEq, Repr

def specStream : StreamCodec Spec :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product FnConsumerFrontierCore.namespaceStream
          (StreamCodec.product subjectIdStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.option NativeHostCodec.receiptStream))))))))
    (fun spec => (spec.domain, spec.semantics, spec.consumerNamespace,
      spec.gatewaySubject, spec.gatewayTarget, spec.gatewayCapability,
      spec.initialPosition, spec.legacyAnchor))
    (fun (domain, semantics, consumerNamespace, gatewaySubject, gatewayTarget,
      gatewayCapability, initialPosition, legacyAnchor) =>
      ⟨domain, semantics, consumerNamespace, gatewaySubject, gatewayTarget,
        gatewayCapability, initialPosition, legacyAnchor⟩)
    (by intro spec; cases spec; rfl)

def specCodec : LawfulCodec Spec :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/CONSUMER-NAMESPACE-SPEC/v1".toUTF8.toList
      specStream)

def Spec.valid (spec : Spec) : Bool :=
  FnConsumerScope.validName spec.consumerNamespace.application &&
  spec.consumerNamespace.scope.valid &&
  !spec.consumerNamespace.controlBinding.isEmpty &&
  spec.consumerNamespace.controlBinding.length ≤ 64 &&
  spec.initialPosition ≤ 4294967295 &&
  (if spec.legacyAnchor.isSome then spec.initialPosition > 0
    else spec.initialPosition == 0) &&
  (specCodec.encode spec).length ≤ 4096

def Spec.key (spec : Spec) : FnConsumerFrontierCore.Key :=
  ⟨spec.consumerNamespace.application, spec.consumerNamespace.scope,
    spec.consumerNamespace.controlBinding, spec.gatewaySubject,
    spec.gatewayTarget, spec.gatewayCapability⟩

theorem Spec.key_namespace (spec : Spec) :
    spec.key.namespace = spec.consumerNamespace := rfl

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
    (NativeHostCodec.framed "DREGG/FN/CONSUMER-NAMESPACE-INGRESS/v1".toUTF8.toList
      ingressStream)

def transactionId (spec : Spec) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/FN/CONSUMER-NAMESPACE-TRANSACTION/v1".toUTF8.toList
    (specCodec.encode spec)).digest

def event (ingress : Ingress) : StableEvent where
  codecVersion := 20
  domain := ingress.spec.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/FN/CONSUMER-NAMESPACE-EVENT/v1".toUTF8.toList
    (ingressCodec.encode ingress)).digest
  canonicalBytes := ingressCodec.encode ingress

def claimNullifier (spec : Spec) : StableNullifier :=
  FnConsumerFrontierCore.namespaceNullifier spec.domain spec.semantics spec.consumerNamespace

/-- Rotating a gateway grant cannot mint a fresh namespace claim for the same
deployment and consumer identity. A new scope/control registration or a
separately authorized migration is required. -/
theorem claimNullifier_gateway_independent (left right : Spec)
    (domain : left.domain = right.domain)
    (semantics : left.semantics = right.semantics)
    (sameNamespace : left.consumerNamespace = right.consumerNamespace) :
    claimNullifier left = claimNullifier right := by
  simp [claimNullifier, domain, semantics, sameNamespace]

end Minidregg.Kernel.FnConsumerNamespaceRegistration
