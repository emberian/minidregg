/- Explicit reservation-capable factory authoring and signing method.
   The ordinary resource-birth authoring and assembly entrypoints stay unchanged. -/
import Kernel.NativeHost

namespace Minidregg.Kernel.NativeHostReserveBirth

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Theory
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ResourceBirthPolicyController.Concrete

set_option autoImplicit false

/-- Source authoring derives reservation from a checked owner template, never
from an arbitrary requested verb/target set. The native receiving method will
require independently signed owner consent and current creator law again. -/
def reserveGrant (owner : AuthorityGrant) (identifier : CapabilityId) : AuthorityGrant :=
  ⟨owner.kind, { owner.capability with head := { owner.capability.head with
    id := identifier
    root := identifier
    parent := none
    scope := { owner.capability.head.scope with
      targets := .explicit {⟨owner.capability.head.policyId.value⟩}
      verbs := {reserveVerb owner.kind} } } }⟩

theorem reserveGrant_for_birth (owner : AuthorityGrant) (identifier : CapabilityId)
    (item : BirthItem CanonicalCellRegistry.registry) (native : NativeOwnerGrant owner item) :
    ReserveOwnerGrant (reserveGrant owner identifier) item := by
  unfold ReserveOwnerGrant AuthorityGrant.NativeForBirth
  simp [reserveGrant, native.1.1, native.1.2.2.1, native.1.2.2.2, native.2.2]

def withReserveGrants
    (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (tariff : CreationTariff)
    (descriptor : Descriptor CanonicalCellRegistry.registry)
    (identifiers : List CapabilityId) : Except String (Descriptor CanonicalCellRegistry.registry) := do
  unless decide (TemplateBound template authority height descriptor) do
    throw "ordinary birth template required for explicit reserve authoring"
  unless identifiers.length == descriptor.births.length do
    throw "one reserve capability identity required for each birth"
  let reserves ← (descriptor.births.zip identifiers).mapM fun (item, identifier) => do
    let some owner := descriptor.grants.find? (fun grant => decide (NativeOwnerGrant grant item))
      | throw "ordinary owner template absent"
    pure (reserveGrant owner identifier)
  let unpriced := { descriptor with grants := descriptor.grants ++ reserves }
  let result := { unpriced with fee := { unpriced.fee with amount := unpriced.quotedFee tariff } }
  unless decide (ReserveTemplateBound template authority height result) do
    throw "reserve birth template refused"
  unless decide result.GrantIdsDistinct do
    throw "duplicate reserve birth capability identity"
  pure result

structure SigningPlan where
  base : NativeHostCodec.SigningPlan
  owners : List SigningSlot

open Minidregg.Compiler.Tower256ConcreteBackend in
def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap
    (StreamCodec.product NativeHostCodec.signingPlanStream
      (StreamCodec.list NativeHostCodec.signingSlotStream))
    (fun plan => (plan.base, plan.owners))
    (fun pair => ⟨pair.1, pair.2⟩) (by intro plan; cases plan; rfl)

def signingPlanCodec : LawfulCodec SigningPlan := NativeHostCodec.framed
  ("DREGG/RESOURCE-RESERVE-BIRTH/SIGNING-PLAN".toUTF8.toList ++ [1]) signingPlanStream

structure AuthorRequest where
  signedObservationBytes : List UInt8
  sourceBytes : List UInt8
  reserveCapabilityIds : List CapabilityId

open Minidregg.Compiler.Tower256ConcreteBackend in
def authorRequestStream : StreamCodec AuthorRequest :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.list CredentialAuthorityEntryCodec.capabilityIdStream)))
    (fun request => (request.signedObservationBytes, request.sourceBytes, request.reserveCapabilityIds))
    (fun triple => ⟨triple.1, triple.2.1, triple.2.2⟩)
    (by intro request; cases request; rfl)

def authorRequestCodec : LawfulCodec AuthorRequest := NativeHostCodec.framed
  ("DREGG/RESOURCE-RESERVE-BIRTH/AUTHOR-REQUEST".toUTF8.toList ++ [1]) authorRequestStream

/-- A distinct factory method, requiring the reservation template rather than
an ordinary write flag. Complete old-image preparation remains the shared
resource-birth lowering and all existing source branches are signed unchanged. -/
def prepareLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (descriptorBytes : List UInt8) (sourceCapabilities : List CapabilityId) :
    Except String SigningPlan := do
  let plan ← NativeHost.prepareLoaded config opened (.birth descriptorBytes sourceCapabilities)
  let .birth finalized _ := plan.finalizedDraft | throw "reserve birth expected"
  let some descriptor := CanonicalCellRegistry.sourceEncoding.codec.decode finalized
    | throw "noncanonical reserve birth descriptor"
  let prepared ← (ResourceBirthController.Concrete.prepareBirth config.profile.compilerProfile
    config.profile.disabledEvaluators config.deployment opened.pins opened.durable descriptor plan.height).mapError
      (fun reason => s!"reserve birth preparation: {repr reason}")
  let _pending ← (preparePending (profile := config.profile) prepared plan.height .reserve).mapError
    (fun reason => s!"reserve factory method refused: {repr reason}")
  let owners ← (List.finRange descriptor.births.length).mapM fun position => do
    let request := ownerConsentRequest (profile := config.profile) prepared plan.height position
    let header ← (CredentialSignatureAdmission.signingHeader prepared.authority.snapshot
      descriptor.authorityNullifier request).mapError
        (fun reason => s!"reserve owner key selection: {repr reason}")
    pure (SigningSlot.mk 10 position.val
      (CredentialSignedEnvelopeController.headerCodec.encode header))
  pure ⟨plan, owners⟩

/-- Owner and creator/debit signers are independent. Assembly issues no rights;
the existing native birth receiver rechecks all signatures on its own image. -/
def assemble (plan : SigningPlan)
    (sourceSignatures ownerSignatures : List (List UInt8)) : Except String SignedCall := do
  let .birth ordinary := ← NativeHost.assemble plan.base sourceSignatures
    | throw "reserve birth source signatures expected"
  unless ownerSignatures.length == plan.owners.length do
    throw "reserve owner signature count mismatch"
  let owners ← (plan.owners.zip ownerSignatures).mapM fun (slot, signature) => do
    unless signature.length == 64 do throw "reserve owner signature must be 64 bytes"
    let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
      | throw "noncanonical reserve owner header"
    pure (CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩)
  let some decoded := decodeOrdinaryIngress ordinary
    | throw "noncanonical reserve birth source ingress"
  pure (.birth (reserveIngressCodec.encode (decoded.ingress, owners)))

structure AssembleRequest where
  planBytes : List UInt8
  sourceSignatures : List (List UInt8)
  ownerSignatures : List (List UInt8)

open Minidregg.Compiler.Tower256ConcreteBackend in
def assembleRequestStream : StreamCodec AssembleRequest :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product
      (StreamCodec.list bytesStream) (StreamCodec.list bytesStream)))
    (fun request => (request.planBytes, request.sourceSignatures, request.ownerSignatures))
    (fun triple => ⟨triple.1, triple.2.1, triple.2.2⟩)
    (by intro request; cases request; rfl)

def assembleRequestCodec : LawfulCodec AssembleRequest := NativeHostCodec.framed
  ("DREGG/RESOURCE-RESERVE-BIRTH/ASSEMBLE-REQUEST".toUTF8.toList ++ [1]) assembleRequestStream

def assembleWire (bytes : List UInt8) : Except String (List UInt8) := do
  let some request := assembleRequestCodec.decode bytes
    | throw "noncanonical reserve birth assemble request"
  let some plan := signingPlanCodec.decode request.planBytes
    | throw "noncanonical reserve birth signing plan"
  let call ← assemble plan request.sourceSignatures request.ownerSignatures
  pure (NativeHostCodec.callCodec.encode call)

end Minidregg.Kernel.NativeHostReserveBirth
