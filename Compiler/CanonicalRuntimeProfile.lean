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
import Theory.PersistedCodecTags
import Compiler.CanonicalRuntimeProfileCore
import Compiler.NativeProtocolFrames
import Compiler.WorldExecutionContract
import Compiler.ApplicationReceivingDomain
import Kernel.PayReceivingContract
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

/-- Policy replacement keeps current-law composition and its authenticated dependency guards;
the audience phase change and any roster/catalog preimage are checked against the same image. -/
def installProjectionVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.runtime_policy_install_preserve_grants_advance_revision_current_c_c1f9612f7f373edc.toUTF8.toList

/-- One source-owned preparation supplies exact old/final views, clock/run/stream and
target/index joint slots, semantic world-kind fields and composed-law dependencies.
Protected objects bind the fresh epoch and complete roster at the same receiving image. -/
def invocationProjectionVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.runtime_joint_invocation_exact_targets_final_posts_current_signed_e349850bee868e43.toUTF8.toList

/-- Content uses the complete typed document tree, revisioned atoms, ordered marks,
transclusion read guards, event/history/link indexes and live shared-name uniqueness.
Committed hiding-key material is excluded from the predicate view. -/
def contentProjectionVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.runtime_content_full_document_tree_revisioned_atoms_marks_transcl_2e227868b68b93a4.toUTF8.toList

/-- The initial next-key commitment is an explicit current-key-authorized
admission with a separate next-key possession signature and exact record pin. -/
def keyCommitmentAdoptionVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.subject_key_adopt_next_current_live_exact_record_two_signatures_f_aacd68f55051a9ed.toUTF8.toList

/-- Factory, initial source, grants and newborn share one prepared tuple. The authored
height window, inherited lineage, current kind/descriptor/ROM guards and composed
exports all contribute; a newborn local law is installed without self-gating birth. -/
def birthProjectionVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.runtime_resource_birth_scoped_account_factory_user_command_author_5431c31fcc5e0a63.toUTF8.toList

/-- Delegation checks current composed resource law and exact parent/child authority
against authenticated dependencies from the same image. -/
def delegationProjectionVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.runtime_capability_delegation_scoped_parent_child_authority_curre_5e6893b4cf528357.toUTF8.toList

/-- Revocation checks current composed resource law, the exact control grant
and authenticated dependencies from the same image. -/
def revocationProjectionVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.runtime_capability_revocation_scoped_victim_control_authority_cur_25765520cfcff3b0.toUTF8.toList

/-- K-RENOUNCE: the holder a capability names revokes it, signed by its
current key; no management grant and no policy participate; the holder gate
runs after the signature, and only its refusal is disclosed to the signer. -/
def renounceVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.runtime_capability_renounce_holder_signed_no_policy_gate_after_signature_v1.toUTF8.toList

/-- Signed queries use committed clock slots, current composed law, semantic world
fields, exact observe-grant footprints and independently authorized document/index
views. Protected release binds current epoch and complete roster/catalog guards. -/
def observationProjectionVersion : List UInt8 :=
  "observe/v7:clock-slots-first;exact-ordered-joint-targets;object=declaredObject|content|stream|worldKind|worldInstance;account=accountMetadata;program=declaredProgram;shared-resource-local-noop-admission;context-bytes;scalar-content-tree-and-subject-bound-world-kind-slots;document-history-marks-links-query-sum;current-kind-export-descriptor-and-composed-law-guards;sparse-account-cut;same-image-intent-signatures;submit-foreign-view-read-gate;audience-epoch-complete-roster-catalog;reader-subject-clockday-compute-quote-book-root".toUTF8.toList

/-- Authorization binds exact inner semantic field footprints, current key and
policy revision, separate grant generation, and current authenticated composed dependencies. -/
def authorizationVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.runtime_authorization_revision_grant_generation_distinct_revocati_c1bfcb32cefcf6ea.toUTF8.toList

/-- Native logical time is derived from the very image admitted and CASed.
Its genesis offset belongs to the source-owned receiver parameters below. -/
def nativeClockVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.runtime_clock_genesis_plus_accepted_count_exact_image_v1.toUTF8.toList

/-- The authority domain is one cell; its clock is the spent-nullifier count. -/
def authorityDomainVersion : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.runtime_authority_domain_one_cell_spent_nullifier_clock_v1.toUTF8.toList

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
  Minidregg.Theory.PersistedCodecTags.runtime_object_audience_v1_state_object_epoch_parent_transition_a_e2d12c4bacbda5e1.toUTF8.toList

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
   -- Actual paid codec/policy constants share an Init-only leaf with receivers.
   (StreamCodec.list bytesStream).encode Kernel.PayReceivingContract.frames,
   (StreamCodec.list StreamCodec.nat).encode Kernel.PayReceivingContract.parameters,
   -- Application frames are the very values used by their receiving codecs.
   ApplicationReceivingDomain.receivingContract,
   (StreamCodec.list bytesStream).encode
     [ApplicationReceivingDomain.streamContinuityChallengeFrame,
      ApplicationReceivingDomain.streamContinuityRequestFrame,
      ApplicationReceivingDomain.streamContinuityAttestationFrame,
      ApplicationReceivingDomain.routeAdmissionChallengeFrame,
      ApplicationReceivingDomain.routeAdmissionRequestFrame,
      ApplicationReceivingDomain.routeAdmissionAttestationFrame,
      ApplicationReceivingDomain.routeBoundDispatchFrame,
      ApplicationReceivingDomain.noRecordRefusalFrame,
      ApplicationReceivingDomain.dispatchCommittedPermitFrame,
      ApplicationReceivingDomain.agentDispatchCommittedPermitFrame,
      ApplicationReceivingDomain.streamContinuityProbeProtocol,
      ApplicationReceivingDomain.routeAdmissionProbeProtocol],
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
   Minidregg.Theory.PersistedCodecTags.runtime_tail_bound_head_le_certified_plus_l_every_non_certify_record_v1.toUTF8.toList,
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
   installProjectionVersion, invocationProjectionVersion, birthProjectionVersion, keyCommitmentAdoptionVersion,
   delegationProjectionVersion, revocationProjectionVersion, renounceVersion, contentProjectionVersion,
   (StreamCodec.list (StreamCodec.list StreamCodec.nat)).encode
     [[requestKindTag .object,
       CredentialAuthorityEntryCodec.verbTag (.observeObject),
       CredentialAuthorityEntryCodec.verbTag (.mutateObject),
       CredentialAuthorityEntryCodec.verbTag (.delegateObject),
       CredentialAuthorityEntryCodec.verbTag (.appendObject),
       CredentialAuthorityEntryCodec.verbTag (.placeObject),
       CredentialAuthorityEntryCodec.verbTag (.reserveObject)],
      [requestKindTag .account,
       CredentialAuthorityEntryCodec.verbTag (.observeAccount),
       CredentialAuthorityEntryCodec.verbTag (.transfer),
       CredentialAuthorityEntryCodec.verbTag (.delegateAccount),
       CredentialAuthorityEntryCodec.verbTag (.mintAsset),
       CredentialAuthorityEntryCodec.verbTag (.burnAsset),
       CredentialAuthorityEntryCodec.verbTag (.reserveAccount)],
      [requestKindTag .program,
       CredentialAuthorityEntryCodec.verbTag (.observeProgram),
       CredentialAuthorityEntryCodec.verbTag (.installProgram),
       CredentialAuthorityEntryCodec.verbTag (.delegateProgram),
       CredentialAuthorityEntryCodec.verbTag (.installPolicy),
       CredentialAuthorityEntryCodec.verbTag (.revokeCapability),
       CredentialAuthorityEntryCodec.verbTag (.observePayment),
       CredentialAuthorityEntryCodec.verbTag (.tickClock),
       CredentialAuthorityEntryCodec.verbTag (.reserveProgram)]]]

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

/-- The current source-owned manifest is injected here, outside receiver imports. -/
def Profile.source {F : Type} [Field F] (template : FactoryTemplate)
    (fieldIdentity : Digest) (characteristic : Nat)
    (characteristicCorrect : CharP F characteristic) (orderWidth : Nat)
    (orderNoWrap : PredOrder.NoWrap F orderWidth) (receiverParameters : List UInt8 := [])
    (disabledEvaluators : List Digest := []) : Profile F :=
  .fromComponents sourceComponents template fieldIdentity characteristic characteristicCorrect
    orderWidth orderNoWrap receiverParameters disabledEvaluators

/-- Ordinary program editing and policy replacement remain distinct committed actions. -/
theorem edit_and_policy_verbs_distinct :
    CredentialAuthorityEntryCodec.verbTag (.installProgram) ≠
      CredentialAuthorityEntryCodec.verbTag (.installPolicy) := by decide

/-- info: 'Minidregg.Compiler.CanonicalRuntimeProfile.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encode_injective

end Minidregg.Compiler.CanonicalRuntimeProfile
