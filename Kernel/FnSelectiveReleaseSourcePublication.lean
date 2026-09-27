/-
Source-side publication authority for one selected release. This request is
distinct from a signed read: it asks the current content resource law for
`.delegateObject` over the exact owner packet and selected page root. A later
source receiver must verify the native envelope/current capability and record
one durable publication event before any fn POST claims source authorization.
-/
import Kernel.FnSelectiveReleaseIngress
import Kernel.ContentResource

namespace Minidregg.Kernel.FnSelectiveReleaseSourcePublication

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.FnSelectiveRelease
open Minidregg.Kernel.FnSelectiveReleaseSignature

set_option autoImplicit false

structure Spec where
  packet : Packet
  delegateCapability : CapabilityId
  deriving DecidableEq, Repr

def specStream : StreamCodec Spec :=
  StreamCodec.xmap
    (StreamCodec.product packetStream
      CredentialAuthorityEntryCodec.capabilityIdStream)
    (fun spec => (spec.packet, spec.delegateCapability))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro spec; cases spec; rfl)

def specCodec : LawfulCodec Spec :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/SELECTED-SOURCE-SPEC/v1".toUTF8.toList specStream)

def sourceBytes (spec : Spec) : List UInt8 :=
  specCodec.encode spec

structure Ingress where
  spec : Spec
  nativeEnvelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product specStream bytesStream)
    (fun ingress => (ingress.spec, ingress.nativeEnvelope))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/SELECTED-SOURCE-INGRESS/v1".toUTF8.toList
      ingressStream)

def keyBytes (spec : Spec) : List UInt8 :=
  (StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat digestStream)).encode
    (spec.packet.release.source.domain,
      spec.packet.release.source.resource, spec.packet.release.owner.nonce)

def transactionId (spec : Spec) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/FN/SELECTED-SOURCE-TRANSACTION/v1".toUTF8.toList
    (keyBytes spec)).digest

def nullifier (spec : Spec) : DurableDataIntent.StableNullifier where
  codecVersion := 14
  domain := spec.packet.release.source.domain
  nullifierId := transactionId spec
  canonicalBytes := "DREGG/FN/SELECTED-SOURCE-NULLIFIER/v1".toUTF8.toList ++
    keyBytes spec

def event (ingress : Ingress) : DurableDataIntent.StableEvent where
  codecVersion := 14
  domain := ingress.spec.packet.release.source.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/FN/SELECTED-SOURCE-EVENT/v1".toUTF8.toList
    (ingressCodec.encode ingress)).digest
  canonicalBytes := ingressCodec.encode ingress

def marker (spec : Spec) : Nat :=
  (Sp800185Cshake256.hash
    "DREGG/FN/SELECTED-SOURCE-PUBLICATION-MARKER/v1".toUTF8.toList
    (sourceBytes spec)).digest.value

/-- The existing object-delegation verb is the explicit source publication
authority; neither `.observeObject` nor `.mutateObject` is substituted. Both
args/effects digests commit the complete canonical packet, including its
owner-signed selected atom identifier. -/
def sourceRequest (domain semantics : Digest) (federation : FederationId)
    (authority : AuthState) (height : Nat) (spec : Spec) : Request .object where
  domain := domain
  semantics := semantics
  federation := federation
  subject := ⟨spec.packet.release.owner.subject⟩
  subjectKeyEpoch := authority.subjectKeyEpoch
    ⟨spec.packet.release.owner.subject⟩
  target := ⟨spec.packet.release.source.resource⟩
  verb := .delegateObject
  argsDigest := (Sp800185Cshake256.hash
    "DREGG/FN/SELECTED-SOURCE-PUBLICATION-ARGS/v1".toUTF8.toList
    (sourceBytes spec)).digest
  effectsDigest := (Sp800185Cshake256.hash
    "DREGG/FN/SELECTED-SOURCE-PUBLICATION-EFFECTS/v1".toUTF8.toList
    (sourceBytes spec)).digest
  nonce := spec.packet.release.owner.nonce.value
  height := height
  preStateRoot := spec.packet.release.source.parent
  policyId := ⟨spec.packet.release.source.resource⟩
  policyEpoch := authority.policyEpoch
    ⟨spec.packet.release.source.resource⟩
  policyRevision := authority.policyRevision
    ⟨spec.packet.release.source.resource⟩
  cost := (sourceBytes spec).length

theorem request_delegate (domain semantics : Digest) (federation : FederationId)
    (authority : AuthState) (height : Nat) (spec : Spec) :
    (sourceRequest domain semantics federation authority height spec).verb =
      .delegateObject := rfl

theorem request_source_target (domain semantics : Digest) (federation : FederationId)
    (authority : AuthState) (height : Nat) (spec : Spec) :
    (sourceRequest domain semantics federation authority height spec).target.value =
      spec.packet.release.source.resource := rfl

end Minidregg.Kernel.FnSelectiveReleaseSourcePublication
