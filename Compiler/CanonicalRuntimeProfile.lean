/-
# One source-owned semantics for native birth, invocation and policy replacement

A stored policy's semantics must remain the same across these operations. The
runtime identity therefore commits the complete shared codec and projection
contract plus the full factory grant template. Each receiver consumes the same
`Profile`; a request cannot choose a template, field, order width or compiler.

The exported framing/root constants below are read from their owning modules.
Projection versions are the shared receiving contract and must change whenever
their source-owned predicate views change. Hash collision resistance remains a
cryptographic assumption; canonical encoding, profile construction and arithmetic
premises are explicit here. Concrete native field/range selection lives in
`NativeHostProfile`; this shared profile remains parameterized.
-/
import Compiler.CanonicalPolicyAdmission
import Compiler.CanonicalCellRegistry
import Compiler.CredentialAuthorityDomain
import Compiler.CredentialAuthorityReplay
import Compiler.CredentialSignatureAdmission
import Compiler.DeclaredEffectPageMaterializer
import Compiler.PolicyRecordCodec
import Compiler.ResourceBirthCodec

namespace Minidregg.Compiler.CanonicalRuntimeProfile

open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- First-order factory parameters are part of the one compatible runtime identity. -/
structure FactoryTemplate where
  issuer : IssuerId
  ownerBudget : Nat
  lifetime : Nat
  deriving DecidableEq, Repr

def FactoryTemplate.tuple (template : FactoryTemplate) : Nat × (Nat × Nat) :=
  (template.issuer.value, template.ownerBudget, template.lifetime)

def FactoryTemplate.ofTuple (tuple : Nat × (Nat × Nat)) : FactoryTemplate :=
  ⟨⟨tuple.1⟩, tuple.2.1, tuple.2.2⟩

@[simp] theorem FactoryTemplate.ofTuple_tuple (template : FactoryTemplate) :
    ofTuple template.tuple = template := by
  cases template with
  | mk issuer budget lifetime => cases issuer; rfl

def factoryTemplateStream : StreamCodec FactoryTemplate :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat StreamCodec.nat))
    FactoryTemplate.tuple FactoryTemplate.ofTuple FactoryTemplate.ofTuple_tuple

def FactoryTemplate.encode (template : FactoryTemplate) : List UInt8 :=
  factoryTemplateStream.encode template

/-- Complete-authority old/candidate views for policy replacement. -/
def installProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.POLICY-INSTALL.PRESERVE-GRANTS-ADVANCE-REVISION/v2".toUTF8.toList

/-- The same source declaration produces request fields, old/post views and effects. -/
def invocationProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.DECLARED-INVOCATION.SOURCE-BOUND/v1".toUTF8.toList

/-- Factory, initial policy, authority grants and resource post-state share one tuple. -/
def birthProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.RESOURCE-BIRTH.JOINT-FACTORY-ROLES/v1".toUTF8.toList

def delegationProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.CAPABILITY-DELEGATION.AUTHORIZED-PARENT-FULL-REQUEST/v1".toUTF8.toList

/-- Exact request fields and request-bound capability possession are part of this epoch. -/
def authorizationVersion : List UInt8 :=
  "DREGG.RUNTIME.AUTHORIZATION.REVISION-AND-GRANT-GENERATION/v2".toUTF8.toList

/-- Native logical time is derived from the very image admitted and CASed.
Its genesis offset belongs to the source-owned receiver parameters below. -/
def nativeClockVersion : List UInt8 :=
  "DREGG.RUNTIME.CLOCK.GENESIS-PLUS-ACCEPTED-COUNT.EXACT-IMAGE/v1".toUTF8.toList

def nativeHostWireVersion : List UInt8 :=
  "DREGG.NATIVE.HOST.STRICT-OPERATIONS-AND-SIGNING-PLAN/v1".toUTF8.toList

/-- Reuse the canonical kind encoder; there is no second ordinal table in the views. -/
def requestKindTag (kind : ResourceKind) : Nat :=
  ((ResourceBirthCodec.resourceKindStream.encode kind).head (by
    cases kind <;> decide)).toNat

/-- Shared scalar header for every native operation's predicate view. Digest fields
remain bound by the complete authorization request and the source-derived context.
The target resource and selected policy are distinct coordinates. Grant
generation and current source revision are also distinct signed coordinates. -/
def requestSlots {kind : ResourceKind} (request : Request kind) : List (String × Int) :=
  [("request/kind", Int.ofNat (requestKindTag kind)),
   ("request/verb", Int.ofNat (CredentialAuthorityEntryCodec.verbTag request.verb)),
   ("request/subject", Int.ofNat request.subject.value),
   ("request/subjectKeyEpoch", Int.ofNat request.subjectKeyEpoch),
   ("request/federation", Int.ofNat request.federation.value),
   ("request/height", Int.ofNat request.height),
   ("request/policyEpoch", Int.ofNat request.policyEpoch),
   ("request/policyRevision", Int.ofNat request.policyRevision),
   ("request/nonce", Int.ofNat request.nonce),
   ("request/target", Int.ofNat request.target.value),
   ("target/policyId", Int.ofNat request.policyId.value),
   ("request/cost", Int.ofNat request.cost)]

theorem request_kind_exact {kind : ResourceKind} (request : Request kind) :
    (⟨requestSlots request⟩ : Minidregg.Pred.State).get "request/kind" =
      some (Int.ofNat (requestKindTag kind)) := by
  simp [Minidregg.Pred.State.get, requestSlots]

theorem request_verb_exact {kind : ResourceKind} (request : Request kind) :
    (⟨requestSlots request⟩ : Minidregg.Pred.State).get "request/verb" =
      some (Int.ofNat (CredentialAuthorityEntryCodec.verbTag request.verb)) := by
  simp [Minidregg.Pred.State.get, requestSlots]

theorem request_target_and_policy_exact {kind : ResourceKind} (request : Request kind) :
    (⟨requestSlots request⟩ : Minidregg.Pred.State).get "request/target" =
        some (Int.ofNat request.target.value) ∧
      (⟨requestSlots request⟩ : Minidregg.Pred.State).get "target/policyId" =
        some (Int.ofNat request.policyId.value) := by
  simp [Minidregg.Pred.State.get, requestSlots]

/-- Fixed components use a framed list: component boundaries cannot collide by concatenation.
The receiving registry contributes every actual tag, schema, version and resource
role. Codec/root epochs are read from their actual exported identities, without
a separately maintained blanket version label. -/
def sourceComponents : List (List UInt8) :=
  [authorizationVersion, nativeClockVersion, nativeHostWireVersion,
   CredentialSignatureAdmission.signatureDomain,
   CredentialSignatureAdmission.requestFrame,
   (StreamCodec.list StreamCodec.nat).encode
     [CredentialSignatureAdmission.ed25519Algorithm,
      Minidregg.Kernel.CredentialSignedEnvelopeController.envelopeCodecVersion],
   CredentialAuthorityReplay.frame,
   CredentialAuthorityReplay.birthIdentityFrame,
   CredentialAuthorityReplay.birthIdentityCustomization,
   CredentialAuthorityStateCodec.wireFrame,
   CredentialAuthorityStateCodec.rootCustomization,
   CredentialAuthorityPageMaterializer.wireFrame,
   CredentialAuthorityPageMaterializer.rootCustomization,
   CredentialAuthorityDomain.catalogueFrame,
   CredentialAuthorityDomain.catalogueRootCustomization,
   PolicyRecordCodec.wireFrame,
   PolicyRecordCodec.customization,
   PolicySourceCell.wireFrame,
   PolicySourceCell.rootCustomization,
   PolicySourceCell.idCustomization,
   (StreamCodec.list StreamCodec.nat).encode
     [PolicySourceCell.registryTag.toNat, PolicySourceCell.schemaId,
      PolicySourceCell.wireVersion],
   DeclaredEffectPageMaterializer.wireFrame,
   DeclaredEffectPageMaterializer.rootCustomization,
   CanonicalResourcePageMaterializer.wireFrame,
   CanonicalResourcePageMaterializer.rootCustomization,
   StreamCodec.nat.encode CanonicalResourcePageMaterializer.wireVersion,
   HyperdocumentContentPageMaterializer.wireFrame,
   HyperdocumentContentPageMaterializer.rootCustomization,
   HyperdocumentEventPageMaterializer.wireFrame,
   HyperdocumentEventPageMaterializer.rootCustomization,
   HyperdocumentEventPageMaterializer.eventCustomization,
   ResourceBirthCodec.descriptorFrame,
   ResourceBirthCodec.rootCustomization,
   (StreamCodec.list (StreamCodec.list StreamCodec.nat)).encode
     (CanonicalCellRegistry.Kind.all.map fun kind =>
       [kind.tag.toNat, (CanonicalCellRegistry.schemaRef kind).schemaId.value,
        (CanonicalCellRegistry.schemaRef kind).version,
        requestKindTag (CanonicalCellRegistry.resourceKindOf kind)]),
   StreamCodec.nat.encode CanonicalCellRegistry.factoryKind.tag.toNat,
   installProjectionVersion, invocationProjectionVersion, birthProjectionVersion,
   delegationProjectionVersion,
   (StreamCodec.list (StreamCodec.list StreamCodec.nat)).encode
     [[requestKindTag .object,
       CredentialAuthorityEntryCodec.verbTag (.observeObject),
       CredentialAuthorityEntryCodec.verbTag (.mutateObject),
       CredentialAuthorityEntryCodec.verbTag (.delegateObject)],
      [requestKindTag .account,
       CredentialAuthorityEntryCodec.verbTag (.observeAccount),
       CredentialAuthorityEntryCodec.verbTag (.transfer),
       CredentialAuthorityEntryCodec.verbTag (.delegateAccount)],
      [requestKindTag .program,
       CredentialAuthorityEntryCodec.verbTag (.observeProgram),
       CredentialAuthorityEntryCodec.verbTag (.installProgram),
       CredentialAuthorityEntryCodec.verbTag (.delegateProgram),
       CredentialAuthorityEntryCodec.verbTag (.installPolicy)]]]

def runtimeStream : StreamCodec (List (List UInt8) × FactoryTemplate) :=
  StreamCodec.product (StreamCodec.list bytesStream) factoryTemplateStream

def encode (template : FactoryTemplate) : List UInt8 :=
  runtimeStream.encode (sourceComponents, template)

/-- The exact full template is retained before hashing; no independent summary can replace it. -/
theorem encode_injective : Function.Injective encode := by
  intro left right same
  have decoded := congrArg runtimeStream.toLawful.decode same
  have leftDecoded := runtimeStream.toLawful.decode_encode (sourceComponents, left)
  have rightDecoded := runtimeStream.toLawful.decode_encode (sourceComponents, right)
  change runtimeStream.toLawful.decode (runtimeStream.encode (sourceComponents, left)) =
    some (sourceComponents, left) at leftDecoded
  change runtimeStream.toLawful.decode (runtimeStream.encode (sourceComponents, right)) =
    some (sourceComponents, right) at rightDecoded
  change runtimeStream.toLawful.decode (runtimeStream.encode (sourceComponents, left)) =
    runtimeStream.toLawful.decode (runtimeStream.encode (sourceComponents, right)) at decoded
  rw [leftDecoded, rightDecoded] at decoded
  exact (Prod.mk.inj (Option.some.inj decoded)).2

def receiverSemantics (template : FactoryTemplate) (parameters : List UInt8 := []) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE.RUNTIME.SEMANTICS/v2".toUTF8.toList
    ((StreamCodec.product bytesStream bytesStream).encode (encode template, parameters))).digest

/-- Native runtime profiles always enable scalar order with its actual arithmetic
premises. The common compiler bundle is derived below, so a template/profile
disagreement or research fallback cannot be stored in this type. -/
structure Profile (F : Type) [Field F] where
  template : FactoryTemplate
  fieldIdentity : Digest
  characteristic : Nat
  characteristicCorrect : CharP F characteristic
  orderWidth : Nat
  orderNoWrap : PredOrder.NoWrap F orderWidth
  /-- Source-owned deployment parameters, never selected by an operation. -/
  receiverParameters : List UInt8 := []

def Profile.source {F : Type} [Field F] (template : FactoryTemplate)
    (fieldIdentity : Digest) (characteristic : Nat)
    (characteristicCorrect : CharP F characteristic) (orderWidth : Nat)
    (orderNoWrap : PredOrder.NoWrap F orderWidth) (receiverParameters : List UInt8 := []) : Profile F :=
  ⟨template, fieldIdentity, characteristic, characteristicCorrect, orderWidth, orderNoWrap,
    receiverParameters⟩

def Profile.compilerProfile {F : Type} [Field F] (profile : Profile F) :
    PolicyCompilerProfile F :=
  .source (receiverSemantics profile.template profile.receiverParameters) profile.fieldIdentity
    profile.characteristic profile.characteristicCorrect
    (.scalar profile.orderWidth) profile.orderNoWrap

def Profile.semantics {F : Type} [Field F] (profile : Profile F) : Digest :=
  profile.compilerProfile.semantics

theorem Profile.receiverSemantics_exact {F : Type} [Field F] (profile : Profile F) :
    profile.compilerProfile.descriptor?.map (·.receiverSemantics) =
      some (receiverSemantics profile.template profile.receiverParameters) := rfl

theorem Profile.order_enabled {F : Type} [Field F] (profile : Profile F) :
    profile.compilerProfile.compiler = .scalar profile.orderWidth := rfl

theorem Profile.canonical_compatible {F : Type} [Field F] (profile : Profile F)
    (context : PolicyStepContext) :
    profile.compilerProfile.compatible (.canonical context) = true := rfl

theorem Profile.actual_characteristic {F : Type} [Field F] (profile : Profile F) :
    CharP F profile.characteristic := profile.characteristicCorrect

/-- Ordinary program editing and policy replacement remain distinct committed actions. -/
theorem edit_and_policy_verbs_distinct :
    CredentialAuthorityEntryCodec.verbTag (.installProgram) ≠
      CredentialAuthorityEntryCodec.verbTag (.installPolicy) := by decide

/-- info: 'Minidregg.Compiler.CanonicalRuntimeProfile.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encode_injective

end Minidregg.Compiler.CanonicalRuntimeProfile
