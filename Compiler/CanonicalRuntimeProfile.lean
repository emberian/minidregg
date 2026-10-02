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
import Compiler.NativeProtocolFrames
import Compiler.WorldExecutionContract
import Compiler.ObjectAudienceRoster
import Compiler.WorldKindDescriptor
import Compiler.WorldKindCell
import Kernel.WorldKindInstance
import Compiler.CanonicalCellRegistry
import Compiler.CredentialAuthorityDomain
import Compiler.CredentialAuthorityReplay
import Compiler.CredentialSignatureAdmission
import Compiler.DeclaredEffectCell
import Compiler.CredentialAuthorityCell
import Compiler.HyperdocumentCell
import Compiler.PolicyRecordCodec
import Compiler.ResourceBirthCodec
import Compiler.Evaluator

namespace Minidregg.Compiler.CanonicalRuntimeProfile

open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- The admission lag a birth may carry, in heights: the longest honest
authoring-to-admission gap the deployment tolerates. Every admission advances
the height (`nativeClockVersion`), so this counts other admissions, not
seconds: a birth authored at `H0` stays admissible through the next 64
admissions anyone makes. The deployed clock ticks once a minute and a busy
room adds a handful more per birth window (10-40 s measured), so 64 is an
order of magnitude over the honest gap and far under every owner grant
`lifetime`. -/
def defaultBirthSlack : Nat := 64

/-- First-order factory parameters are part of the one compatible runtime identity.
`birthSlack` is how many heights after its authored `notBefore` a birth may
still be admitted (`ResourceBirthPolicyController.Concrete.BirthWindow`). -/
structure FactoryTemplate where
  issuer : IssuerId
  ownerBudget : Nat
  lifetime : Nat
  birthSlack : Nat := defaultBirthSlack
  deriving DecidableEq, Repr

def FactoryTemplate.tuple (template : FactoryTemplate) : Nat × (Nat × (Nat × Nat)) :=
  (template.issuer.value, template.ownerBudget, template.lifetime, template.birthSlack)

def FactoryTemplate.ofTuple (tuple : Nat × (Nat × (Nat × Nat))) : FactoryTemplate :=
  ⟨⟨tuple.1⟩, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩

@[simp] theorem FactoryTemplate.ofTuple_tuple (template : FactoryTemplate) :
    ofTuple template.tuple = template := by
  cases template with
  | mk issuer budget lifetime slack => cases issuer; rfl

def factoryTemplateStream : StreamCodec FactoryTemplate :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    FactoryTemplate.tuple FactoryTemplate.ofTuple FactoryTemplate.ofTuple_tuple

def FactoryTemplate.encode (template : FactoryTemplate) : List UInt8 :=
  factoryTemplateStream.encode template

/-- Policy replacement keeps current-law composition and its authenticated dependency guards;
the audience phase change and any roster/catalog preimage are checked against the same image. -/
def installProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.POLICY-INSTALL.PRESERVE-GRANTS-ADVANCE-REVISION.CURRENT-COMPOSED-LAW-CANDIDATE-GRAPH-AUDIENCE-CATALOG-GUARDS/v3".toUTF8.toList

/-- One source-owned preparation supplies exact old/final views, clock/run/stream and
target/index joint slots, semantic world-kind fields and composed-law dependencies.
Protected objects bind the fresh epoch and complete roster at the same receiving image. -/
def invocationProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.JOINT-INVOCATION.EXACT-TARGETS-FINAL-POSTS-CURRENT-SIGNED-READS-CLOCK-SLOTS-RUN-SLOTS.TARGET-AND-INDEX-KEYED-JOINT-SLOTS.STREAM-APPEND-SLOTS.WORLD-KIND-SEMANTIC-FIELDS.COMPOSED-GUARDS-AUDIENCE-ROSTER.ROM-METHOD-OUTPUTS-ATOMIC-QUOTA-BOOK-COMPUTE-FUNDING/v10".toUTF8.toList

/-- Content uses the complete typed document tree, revisioned atoms, ordered marks,
transclusion read guards, event/history/link indexes and live shared-name uniqueness.
Committed hiding-key material is excluded from the predicate view. -/
def contentProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.CONTENT.FULL-DOCUMENT-TREE-REVISIONED-ATOMS-MARKS-TRANSCLUSION-HISTORY-LINKS.STORE-CELL.LIVE-SHARED-NAME-UNIQUENESS.NO-HIDING-KEY-PROJECTION/v5".toUTF8.toList

/-- Factory, initial source, grants and newborn share one prepared tuple. The authored
height window, inherited lineage, current kind/descriptor/ROM guards and composed
exports all contribute; a newborn local law is installed without self-gating birth. -/
def birthProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.RESOURCE-BIRTH.SCOPED-ACCOUNT-FACTORY-USER-COMMAND.AUTHORED-WINDOW-BOUNDED-LAG.INHERITED-LINEAGE.CURRENT-KIND-ROOT-DESCRIPTOR-ROM-GUARDS.COMPOSED-EXPORTS/v4".toUTF8.toList

/-- Delegation checks current composed resource law and exact parent/child authority
against authenticated dependencies from the same image. -/
def delegationProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.CAPABILITY-DELEGATION.SCOPED-PARENT-CHILD-AUTHORITY.CURRENT-COMPOSED-LAW-DEPENDENCY-GUARDS/v3".toUTF8.toList

/-- Revocation checks current composed resource law, the exact control grant
and authenticated dependencies from the same image. -/
def revocationProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.CAPABILITY-REVOCATION.SCOPED-VICTIM-CONTROL-AUTHORITY.CURRENT-COMPOSED-LAW-DEPENDENCY-GUARDS/v3".toUTF8.toList

/-- K-RENOUNCE: the holder a capability names revokes it, signed by its
current key; no management grant and no policy participate; the holder gate
runs after the signature, and only its refusal is disclosed to the signer. -/
def renounceVersion : List UInt8 :=
  "DREGG.RUNTIME.CAPABILITY-RENOUNCE.HOLDER-SIGNED-NO-POLICY-GATE-AFTER-SIGNATURE/v1".toUTF8.toList

/-- Signed queries use committed clock slots, current composed law, semantic world
fields, exact observe-grant footprints and independently authorized document/index
views. Protected release binds current epoch and complete roster/catalog guards. -/
def observationProjectionVersion : List UInt8 :=
  "observe/v7:clock-slots-first;exact-ordered-joint-targets;object=declaredObject|content|stream|worldKind|worldInstance;account=accountMetadata;program=declaredProgram;shared-resource-local-noop-admission;context-bytes;scalar-content-tree-and-subject-bound-world-kind-slots;document-history-marks-links-query-sum;current-kind-export-descriptor-and-composed-law-guards;sparse-account-cut;same-image-intent-signatures;submit-foreign-view-read-gate;audience-epoch-complete-roster-catalog;reader-subject-clockday-compute-quote-book-root".toUTF8.toList

/-- Authorization binds exact inner semantic field footprints, current key and
policy revision, separate grant generation, and current authenticated composed dependencies. -/
def authorizationVersion : List UInt8 :=
  "DREGG.RUNTIME.AUTHORIZATION.REVISION-GRANT-GENERATION-DISTINCT-REVOCATION.EXACT-INNER-SEMANTIC-FIELD-FOOTPRINT.CURRENT-COMPOSED-DEPENDENCIES/v5".toUTF8.toList

/-- Native logical time is derived from the very image admitted and CASed.
Its genesis offset belongs to the source-owned receiver parameters below. -/
def nativeClockVersion : List UInt8 :=
  "DREGG.RUNTIME.CLOCK.GENESIS-PLUS-ACCEPTED-COUNT.EXACT-IMAGE/v1".toUTF8.toList

/-- The authority domain is one cell; its clock is the spent-nullifier count. -/
def authorityDomainVersion : List UInt8 :=
  "DREGG.RUNTIME.AUTHORITY-DOMAIN.ONE-CELL.SPENT-NULLIFIER-CLOCK/v1".toUTF8.toList

/-- The actual current codec frames, with explicit component boundaries. This
replaces the old descriptive host-version label: changing a receiving frame now
changes the semantics identity through the same definition used by its decoder. -/
def nativeHostWireVersion : List UInt8 :=
  (StreamCodec.list bytesStream).encode
    [NativeHostCodec.callFrame, NativeHostCodec.draftFrame,
     NativeHostCodec.signingPlanFrame, NativeHostCodec.outcomeFrame,
     NativeObservationCodec.intentFrame, NativeObservationCodec.challengeFrame,
     NativeObservationCodec.signedFrame,
     Kernel.PolicyInstallReceiver.ingressFrame,
     Kernel.DeclaredResourceController.commandFrame]

/-- Audience state uses the exact combined v6 source and structural active/frozen
mode. Enrollment/resume authenticates the complete ordered roster against a
separate content catalog's live atom zero and exact current root. Fresh receiving
and policy installation retain their source-owned phase checks. -/
def audienceProjectionVersion : List UInt8 :=
  "DREGG.RUNTIME.OBJECT-AUDIENCE/v1:state=object,epoch,parent,transition,audience,devices,history,manifest,mode,authoritySnapshot,deviceSnapshot;mode=active|frozen;complete-ordered-roster=subject,capability,deviceSource,deviceGeneration,keyCommitment;catalog=separate-content-live-atom-zero-exact-entry-bytes-and-root;enroll-resume-current-authority;fresh-current-active-epoch;manifest-and-all-holder-post-binding;program-descriptor-not-world-layout".toUTF8.toList

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
   WorldExecutionContract.methodTableMeaning.toUTF8.toList,
   WorldExecutionContract.methodTableFrame, WorldExecutionContract.resourceViewFrame,
   WorldExecutionContract.freshActivationCustomization,
   StreamCodec.nat.encode WorldExecutionContract.freeStepsPerDay,
   WorldExecutionContract.receivingContract,
   CanonicalCellRegistry.logicalLawVersion, observationProjectionVersion,
   CredentialSignatureAdmission.signatureDomain,
   CredentialSignatureAdmission.requestFrame,
   (StreamCodec.list StreamCodec.nat).encode
     [CredentialSignatureAdmission.ed25519Algorithm,
      Minidregg.Kernel.CredentialSignedEnvelopeController.envelopeCodecVersion],
   CredentialAuthorityReplay.frame,
   CredentialAuthorityReplay.birthIdentityFrame,
   CredentialAuthorityReplay.birthIdentityCustomization,
   StoreCodec.frame CredentialAuthorityCell.wire,
   authorityDomainVersion,
   PolicyRecordCodec.wireFrame,
   PolicyRecordCodec.customization,
   PolicyRecordCodec.semanticLawCustomization,
   StreamCodec.nat.encode PolicyRecordCodec.semanticLawVersion,
   Minidregg.Theory.LawComposition.receivingContract,
   Minidregg.Theory.LawComposition.closureCustomization,
   Minidregg.Theory.LawComposition.birthProjectionContract,
   audienceProjectionVersion,
   ObjectAudienceRoster.digestCustomization,
   ObjectAudienceRoster.deviceCustomization,
   PolicySourceCell.wireFrame,
   PolicySourceCell.rootCustomization,
   PolicySourceCell.idCustomization,
   (StreamCodec.list StreamCodec.nat).encode
     [PolicySourceCell.registryTag.toNat, PolicySourceCell.schemaId,
      PolicySourceCell.wireVersion],
   NockProgramCodec.wireFrame,
   NockProgramCodec.programFrame,
   NockProgramCodec.abiFrame,
   NockProgramCodec.codeCustomization,
   NockProgramCodec.programCustomization,
   NockProgramCodec.rootCustomization,
   NockProgramCodec.idCustomization,
   (StreamCodec.list StreamCodec.nat).encode
     [NockProgramCodec.registryTag.toNat, NockProgramCodec.schemaId,
      NockProgramCodec.wireVersion, NockProgramCodec.abiVersion],
   Evaluator.idCustomization,
   (StreamCodec.list bytesStream).encode Evaluator.registryManifest,
   StoreCodec.frame DeclaredEffectCell.wire,
   StoreCodec.frame Kernel.PayCell.wire,
   Kernel.PayCell.idCustomization,
   StoreCodec.frame Kernel.ClockCell.wire,
   Kernel.ClockCell.idCustomization,
   StoreCodec.frame Kernel.SystemCell.wire,
   Kernel.SystemCell.idCustomization,
   "DREGG.RUNTIME.TAIL-BOUND.HEAD-LE-CERTIFIED-PLUS-L.EVERY-NON-CERTIFY-RECORD/v1".toUTF8.toList,
   StoreCodec.rootCustomization,
   StoreCodec.saltCustomization,
   StoreCodec.leafCustomization,
   StoreCodec.ratchetCustomization,
   CanonicalResourcePageMaterializer.wireFrame,
   CanonicalResourcePageMaterializer.rootCustomization,
   StreamCodec.nat.encode CanonicalResourcePageMaterializer.wireVersion,
   WorldKindDescriptor.identityCustomization,
   WorldKindDescriptor.descriptorContract,
   (StreamCodec.list bytesStream).encode
     ([WorldKindDescriptor.ScalarCodec.natural, .integer, .bytes].map fun codec =>
       codec.codecId.toUTF8.toList),
   Kernel.WorldKindInstance.frame,
   StoreCodec.frame WorldKindCell.definitionWire,
   StoreCodec.frame WorldKindCell.instanceWire,
   StoreCodec.frame HyperdocumentCell.contentWire,
   StoreCodec.frame HyperdocumentCell.eventWire,
   ResourceBirthCodec.descriptorFrame,
   ResourceBirthCodec.rootCustomization,
   (StreamCodec.list (StreamCodec.list StreamCodec.nat)).encode
     (CanonicalCellRegistry.Kind.all.map fun kind =>
       [kind.tag.toNat, (CanonicalCellRegistry.schemaRef kind).schemaId.value,
        (CanonicalCellRegistry.schemaRef kind).version,
        requestKindTag (CanonicalCellRegistry.resourceKindOf kind)]),
   StreamCodec.nat.encode CanonicalCellRegistry.factoryKind.tag.toNat,
   installProjectionVersion, invocationProjectionVersion, birthProjectionVersion,
   delegationProjectionVersion, revocationProjectionVersion, renounceVersion, contentProjectionVersion,
   (StreamCodec.list (StreamCodec.list StreamCodec.nat)).encode
     [[requestKindTag .object,
       CredentialAuthorityEntryCodec.verbTag (.observeObject),
       CredentialAuthorityEntryCodec.verbTag (.mutateObject),
       CredentialAuthorityEntryCodec.verbTag (.delegateObject),
       CredentialAuthorityEntryCodec.verbTag (.appendObject),
       CredentialAuthorityEntryCodec.verbTag (.placeObject)],
      [requestKindTag .account,
       CredentialAuthorityEntryCodec.verbTag (.observeAccount),
       CredentialAuthorityEntryCodec.verbTag (.transfer),
       CredentialAuthorityEntryCodec.verbTag (.delegateAccount),
       CredentialAuthorityEntryCodec.verbTag (.mintAsset),
       CredentialAuthorityEntryCodec.verbTag (.burnAsset)],
      [requestKindTag .program,
       CredentialAuthorityEntryCodec.verbTag (.observeProgram),
       CredentialAuthorityEntryCodec.verbTag (.installProgram),
       CredentialAuthorityEntryCodec.verbTag (.delegateProgram),
       CredentialAuthorityEntryCodec.verbTag (.installPolicy),
       CredentialAuthorityEntryCodec.verbTag (.revokeCapability),
       CredentialAuthorityEntryCodec.verbTag (.observePayment),
       CredentialAuthorityEntryCodec.verbTag (.tickClock)]]]

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

/-- The runtime semantics: the template (its source components include the compiled-in
evaluator registry), the deployment parameters, and the evaluators the operator disabled
(K-EVAL: what a run may execute on is part of what admission means, so two nodes that
disagree on it disagree on the semantics digest, never silently on a verdict). -/
def receiverSemantics (template : FactoryTemplate) (parameters : List UInt8 := [])
    (disabled : List Digest := []) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE.RUNTIME.SEMANTICS/v3".toUTF8.toList
    ((StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.list digestStream))).encode
      (encode template, parameters, disabled))).digest

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
  /-- Compiled-in evaluators (`Evaluator.registry`) this deployment's operator disabled,
  by id: a run on one refuses `evaluatorDisabled` (`Kernel.Run.resolve`). Committed in
  `semantics`. -/
  disabledEvaluators : List Digest := []

def Profile.source {F : Type} [Field F] (template : FactoryTemplate)
    (fieldIdentity : Digest) (characteristic : Nat)
    (characteristicCorrect : CharP F characteristic) (orderWidth : Nat)
    (orderNoWrap : PredOrder.NoWrap F orderWidth) (receiverParameters : List UInt8 := [])
    (disabledEvaluators : List Digest := []) : Profile F :=
  ⟨template, fieldIdentity, characteristic, characteristicCorrect, orderWidth, orderNoWrap,
    receiverParameters, disabledEvaluators⟩

def Profile.compilerProfile {F : Type} [Field F] (profile : Profile F) :
    PolicyCompilerProfile F :=
  .source (receiverSemantics profile.template profile.receiverParameters profile.disabledEvaluators)
    profile.fieldIdentity
    profile.characteristic profile.characteristicCorrect
    (.scalar profile.orderWidth) profile.orderNoWrap

def Profile.semantics {F : Type} [Field F] (profile : Profile F) : Digest :=
  profile.compilerProfile.semantics

theorem Profile.receiverSemantics_exact {F : Type} [Field F] (profile : Profile F) :
    profile.compilerProfile.descriptor?.map (·.receiverSemantics) =
      some (receiverSemantics profile.template profile.receiverParameters
        profile.disabledEvaluators) := rfl

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
