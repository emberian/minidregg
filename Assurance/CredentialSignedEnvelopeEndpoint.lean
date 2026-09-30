/-
# Assurance.CredentialSignedEnvelopeEndpoint -- signature admission reaches semantics

This module instantiates `CredentialSignedEnvelopeController` at the deployed
credential lifecycle's exact authority root and request.  It exhibits:

* a committed key-registry projection and one current key;
* an exact signed frame for the canonical request bytes;
* opaque/fallible native verification followed by nullifier consumption;
* a request-indexed signature `AcceptedCredential`; and
* a semantic join parameterized by explicit verifier-refinement and
  EUF-CMA/key-custody premises.

Negative witnesses cover wrong key, rotated epoch, algorithm, domain, message,
stale key, replay, malformed input, false verification, and native error.
A revoked or unregistered key version is refused before this controller, by
`CredentialSignatureAdmission.select` reading the authority cell's presence
planes (`select_revoked_refused`, `select_unregistered_refused`).  The demo verifier is only an executable control witness.  No theorem
claims it implements public-key cryptography or that the registry digest is
collision resistant.
-/
import Assurance.DeployedCredentialLifecycle
import Kernel.CredentialSignedEnvelopeController

namespace Minidregg.Assurance.CredentialSignedEnvelopeEndpoint

open Minidregg.Assurance.DeployedCredentialLifecycle
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.CredentialSignedEnvelopeController
open Minidregg.Theory
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.CredentialAuthorityFamily
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## One exact committed registry and envelope -/

def credentialDomain : List UInt8 :=
  [76, 79, 79, 77, 47, 67, 82, 69, 68, 69, 78, 84, 73, 65, 76, 47, 86, 49]

def ed25519Algorithm : Nat := 1

def canonicalKey : KeyRecord where
  keyId := 7001
  keyEpoch := 0
  algorithm := ed25519Algorithm
  subject := useRequest.subject.value
  publicKey := [11, 22, 33, 44, 55, 66, 77, 88]
  activeFrom := 4
  activeUntil := 8

def canonicalRegistry : KeyRegistryProjection where
  codecVersion := registryCodecVersion
  authorityRoot := attenuatedCell.root
  registryEpoch := 5
  keys := [canonicalKey]

def canonicalRegistryBytes : List UInt8 :=
  registryCodec.encode canonicalRegistry

def canonicalRegistryCommitment : Digest :=
  registryDigest canonicalRegistryBytes

/-- The plan's authority footprint bytes, as the controller sees them at
admission; the signed header must carry exactly these. -/
def canonicalFootprint : List UInt8 := [3, 1, 4]

/-- The admission height. -/
def canonicalHeight : Nat := 6

def canonicalState : ControllerState where
  codecVersion := stateCodecVersion
  authorityRoot := attenuatedCell.root
  registryCommitment := canonicalRegistryCommitment
  registryEpoch := canonicalRegistry.registryEpoch
  footprint := canonicalFootprint
  height := canonicalHeight
  consumedNullifiers := []

def canonicalStateBytes : List UInt8 := stateCodec.encode canonicalState

/-- Lossless first-order request bytes in the exact field order pinned by
`AuthorizationDeclaration.requestFieldOrder`. -/
def requestWireBytes (wire : AuthorizationDeclaration.RequestWire) : List UInt8 :=
  StreamCodec.nat.encode wire.domain ++
  StreamCodec.nat.encode wire.semantics ++
  StreamCodec.nat.encode wire.federation ++
  StreamCodec.nat.encode wire.resourceKind ++
  StreamCodec.nat.encode wire.subject ++
  StreamCodec.nat.encode wire.subjectKeyEpoch ++
  StreamCodec.nat.encode wire.target ++
  StreamCodec.nat.encode wire.verb ++
  StreamCodec.nat.encode wire.argsDigest ++
  StreamCodec.nat.encode wire.effectsDigest ++
  StreamCodec.nat.encode wire.nonce ++
  StreamCodec.nat.encode wire.height ++
  StreamCodec.nat.encode wire.preStateRoot ++
  StreamCodec.nat.encode wire.policyId ++
  StreamCodec.nat.encode wire.policyEpoch ++
  StreamCodec.nat.encode wire.policyRevision ++
  StreamCodec.nat.encode wire.cost

def canonicalRequestWire : AuthorizationDeclaration.RequestWire :=
  encodeRequest ⟨.object, useRequest⟩

def canonicalMessage : List UInt8 :=
  requestWireBytes canonicalRequestWire

def signatureNullifier : Nat := 44001

def canonicalHeader : SignedHeader where
  codecVersion := envelopeCodecVersion
  footprint := canonicalFootprint
  validUntil := canonicalHeight + 1
  keyId := canonicalKey.keyId
  keyEpoch := canonicalKey.keyEpoch
  algorithm := canonicalKey.algorithm
  domain := credentialDomain
  message := canonicalMessage
  nullifier := signatureNullifier

def canonicalEnvelope : SignedEnvelope where
  header := canonicalHeader
  signature := [90, 91, 92, 93, 94, 95]

def canonicalEnvelopeBytes : List UInt8 :=
  envelopeCodec.encode canonicalEnvelope

def canonicalPrepared : Prepared where
  state := canonicalState
  registry := canonicalRegistry
  envelope := canonicalEnvelope
  key := canonicalKey
  frame := canonicalEnvelope.frame
  frameExact := rfl

def canonicalNextState : ControllerState := canonicalPrepared.nextState

def canonicalAdmission : Admission where
  keyId := canonicalKey.keyId
  keyEpoch := canonicalKey.keyEpoch
  algorithm := canonicalKey.algorithm
  message := canonicalMessage
  nullifier := signatureNullifier
  nextStateBytes := stateCodec.encode canonicalNextState

@[simp] theorem canonical_registry_decodes :
    registryCodec.decode canonicalRegistryBytes = some canonicalRegistry :=
  registryCodec.decode_encode canonicalRegistry

@[simp] theorem canonical_envelope_decodes :
    envelopeCodec.decode canonicalEnvelopeBytes = some canonicalEnvelope :=
  envelopeCodec.decode_encode canonicalEnvelope

@[simp] theorem canonical_state_decodes :
    stateCodec.decode canonicalStateBytes = some canonicalState :=
  stateCodec.decode_encode canonicalState

theorem canonical_projection_is_committed :
    registryDigest canonicalRegistryBytes = canonicalState.registryCommitment :=
  rfl

@[simp] theorem canonical_key_selected :
    canonicalRegistry.findKey canonicalKey.keyId = some canonicalKey := by
  rfl

/-- The key projection is anchored to the same root used by the canonical
policy registry and common authorization state. -/
theorem canonical_projection_root_join :
    canonicalRegistry.authorityRoot =
        (authState attenuatedCell).policyRoot /\
      canonicalState.authorityRoot = attenuatedCell.root := by
  exact ⟨rfl, rfl⟩

@[simp] theorem canonical_prepare {NativeError : Type} :
    prepare (NativeError := NativeError) useRequest.subject.value
      credentialDomain canonicalMessage canonicalStateBytes
      canonicalRegistryBytes canonicalEnvelopeBytes =
      .ok canonicalPrepared := by
  unfold prepare
  simp only [canonicalStateBytes, canonicalRegistryBytes,
    canonicalEnvelopeBytes]
  rw [stateCodec.decode_encode, registryCodec.decode_encode,
    envelopeCodec.decode_encode]
  have committed :
      registryDigest (registryCodec.encode canonicalRegistry) =
        canonicalState.registryCommitment := by
    rfl
  simp [committed, canonicalState, canonicalRegistry, canonicalEnvelope,
    canonicalHeader, canonicalKey, canonicalRegistryCommitment,
    canonicalRegistryBytes, canonicalPrepared, credentialDomain, stateCodecVersion,
    registryCodecVersion, envelopeCodecVersion, ed25519Algorithm,
    KeyRegistryProjection.findKey]

/-! ## Opaque native verification and persistent success -/

/-- Executable control verifier.  Its equality tests are useful for integration
tests, but carry no cryptographic authenticity claim. -/
def demoVerifier : OpaqueVerifier Nat :=
  fun publicKey frame signature =>
    if publicKey = canonicalKey.publicKey &&
        frame = canonicalEnvelope.frame &&
        signature = canonicalEnvelope.signature then
      .ok true
    else
      .ok false

@[simp] theorem demo_verifier_accepts_exact_triple :
    demoVerifier canonicalKey.publicKey canonicalEnvelope.frame
        canonicalEnvelope.signature = .ok true := by
  simp [demoVerifier]

@[simp] theorem canonical_native_admission :
    runNative demoVerifier useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes
      canonicalEnvelopeBytes = .ok canonicalAdmission := by
  unfold runNative
  rw [canonical_prepare]
  change finish canonicalPrepared
    (demoVerifier canonicalKey.publicKey canonicalEnvelope.frame
      canonicalEnvelope.signature) = .ok canonicalAdmission
  rw [demo_verifier_accepts_exact_triple]
  rfl

@[simp] theorem successful_admission_consumes_exact_nullifier :
    stateCodec.decode canonicalAdmission.nextStateBytes =
      some canonicalNextState /\
    canonicalNextState.consumedNullifiers = [signatureNullifier] := by
  constructor
  · exact stateCodec.decode_encode canonicalNextState
  · rfl

/-! ## Existing request-indexed signature semantics -/

/-- A signature witness contains the controller preparation and the exact
native-success equation.  Lean can construct it after the opaque call; native
code cannot return one over its byte boundary. -/
structure VerifiedWitness (verify : OpaqueVerifier Nat) where
  prepared : Prepared
  nativeVerified :
    verify prepared.key.publicKey prepared.frame
      prepared.envelope.signature = .ok true

def signaturePortal (verify : OpaqueVerifier Nat) : Portal where
  SignatureWitness := VerifiedWitness verify
  ProofWitness := Unit
  CapabilityCommitmentWitness := Unit
  CapabilityUseWitness := PEmpty
  MembershipWitness := Unit
  IssuerWitness := Unit
  NonRevocationWitness := Unit
  PolicyWitness := Digest
  policyAddress := id
  verifySignature := fun request witness =>
    witness.prepared.envelope.header.message ==
      requestWireBytes (encodeRequest ⟨_, request⟩)
  verifyProof := fun _ _ => true
  verifyCapabilityCommitment := fun _ _ _ => true
  verifyCapabilityUse := fun _ _ _ witness => PEmpty.elim witness
  verifyMembership := fun _ _ _ => true
  verifyIssuer := fun _ _ _ _ => true
  verifyNonRevocation := fun _ _ _ => true
  verifyCommittedPolicy := fun _ _ _ _ => true

def canonicalWitness : VerifiedWitness demoVerifier where
  prepared := canonicalPrepared
  nativeVerified := demo_verifier_accepts_exact_triple

theorem attenuated_subject_key_epoch_zero :
    subjectKeyEpochAt attenuatedCell useRequest.subject = 0 := by
  show subjectKeyEpochAt attenuatedCell ⟨41⟩ = 0
  decide

def signedAuthorization :
    Authorized (signaturePortal demoVerifier)
      (authState attenuatedCell) useRequest where
  evidence := .signature canonicalWitness
    (by
      change useRequest.subjectKeyEpoch =
        subjectKeyEpochAt attenuatedCell useRequest.subject
      rw [attenuated_subject_key_epoch_zero]
      rfl)
    (by
      simp [signaturePortal, canonicalWitness, canonicalPrepared,
        canonicalEnvelope, canonicalHeader, canonicalMessage,
        canonicalRequestWire])
  policyWitness := ⟨2200⟩
  policyMembershipWitness := ()
  policyEpochExact := by simp [useRequest, adminRequest]
  policyRevisionExact := rfl
  policyAddressExact := by
    change ⟨2200⟩ = policyAddressAt attenuatedCell
      Minidregg.Assurance.DeployedCredentialLifecycle.examplePolicy
      (policyRevisionAt attenuatedCell
        Minidregg.Assurance.DeployedCredentialLifecycle.examplePolicy)
    rw [attenuated_policy_revision_two]
    exact attenuated_policy_address_two.symm
  policyMembershipVerified := rfl
  policyVerified := rfl

noncomputable def acceptedSignature :
    AcceptedCredential requestDigestScheme (signaturePortal demoVerifier)
      (authState attenuatedCell) useRequest where
  authorization := signedAuthorization
  carrier := .signature
  carrierSupported := rfl
  requestBinding := .canonical requestDigestScheme useRequest
  lineage := PUnit.unit

theorem accepted_signature_binds_exact_message :
    canonicalPrepared.envelope.header.message =
        requestWireBytes
          acceptedSignature.requestBinding.wire /\
      acceptedSignature.carrier = .signature := by
  constructor
  · simp [acceptedSignature, RequestBinding.canonical, canonicalPrepared,
      canonicalEnvelope, canonicalHeader, canonicalMessage,
      canonicalRequestWire]
  · rfl

/-- The full positive seam.  Controller success and Lean authorization are
constructive, but signer attribution is available only when callers supply the
native-refinement and EUF-CMA/key-custody premises. -/
structure SemanticPath
    (SignerIssued : Nat -> Nat -> List UInt8 -> List UInt8 -> Prop) : Prop where
  controllerAccepted :
    runNative demoVerifier useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes
      canonicalEnvelopeBytes = .ok canonicalAdmission
  credential :
    Nonempty (AcceptedCredential requestDigestScheme
      (signaturePortal demoVerifier)
      (authState attenuatedCell) useRequest)
  signerIssued :
    SignerIssued canonicalKey.keyId canonicalKey.keyEpoch
      canonicalEnvelope.frame canonicalEnvelope.signature
  nullifierConsumed :
    canonicalNextState.consumedNullifiers = [signatureNullifier]

theorem semantic_path_of_completion
    (Authenticates : List UInt8 -> List UInt8 -> List UInt8 -> Prop)
    (SignerIssued : Nat -> Nat -> List UInt8 -> List UInt8 -> Prop)
    (completion :
      SignatureCompletion demoVerifier Authenticates SignerIssued) :
    SemanticPath SignerIssued := by
  refine
    { controllerAccepted := canonical_native_admission
      credential := ⟨acceptedSignature⟩
      signerIssued := ?_
      nullifierConsumed := rfl }
  exact completion.issued_of_verified canonicalPrepared
    demo_verifier_accepts_exact_triple

/-! ## Rotation, revocation, substitution, replay, and native failure teeth -/

def withCommitment (registry : KeyRegistryProjection) :
    ControllerState × Digest :=
  let commitment := registryDigest (registryCodec.encode registry)
  ({ canonicalState with
      registryCommitment := commitment
      registryEpoch := registry.registryEpoch }, commitment)


@[simp] theorem malformed_state_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage [] canonicalRegistryBytes canonicalEnvelopeBytes =
      .error .malformedState := by
  rfl

@[simp] theorem malformed_registry_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes [] canonicalEnvelopeBytes =
      .error .malformedRegistry := by
  unfold prepare
  rw [canonical_state_decodes]
  rfl

/-- **Refuted pole.**  A header whose footprint differs from the values the
controller reads at admission (a read address moved) is refused. -/
def staleFootprintEnvelope : SignedEnvelope :=
  { canonicalEnvelope with
    header := { canonicalHeader with footprint := [3, 1, 5] } }

@[simp] theorem stale_footprint_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes
      (envelopeCodec.encode staleFootprintEnvelope) =
      .error .footprintStale := by
  unfold prepare
  rw [canonical_state_decodes, canonical_registry_decodes,
    envelopeCodec.decode_encode]
  simp [canonicalStateBytes, canonicalState, canonicalRegistry, staleFootprintEnvelope,
    canonicalEnvelope, canonicalHeader, canonicalKey, canonicalFootprint,
    canonicalRegistryCommitment, canonicalRegistryBytes, stateCodecVersion,
    registryCodecVersion, envelopeCodecVersion,
    KeyRegistryProjection.findKey]

def expiredEnvelope : SignedEnvelope :=
  { canonicalEnvelope with
    header := { canonicalHeader with validUntil := canonicalHeight - 1 } }

/-- A plan admitted past its signed `validUntil` is refused. -/
@[simp] theorem expired_plan_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes
      (envelopeCodec.encode expiredEnvelope) =
      .error .expired := by
  unfold prepare
  rw [canonical_state_decodes, canonical_registry_decodes,
    envelopeCodec.decode_encode]
  simp [canonicalStateBytes, canonicalState, canonicalRegistry, expiredEnvelope,
    canonicalEnvelope, canonicalHeader, canonicalKey, canonicalFootprint, canonicalHeight,
    canonicalRegistryCommitment, canonicalRegistryBytes, stateCodecVersion,
    registryCodecVersion, envelopeCodecVersion,
    KeyRegistryProjection.findKey]

def unknownKeyEnvelope : SignedEnvelope :=
  { canonicalEnvelope with
    header := { canonicalHeader with keyId := canonicalKey.keyId + 1 } }

@[simp] theorem wrong_key_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes
      (envelopeCodec.encode unknownKeyEnvelope) = .error .unknownKey := by
  unfold prepare
  rw [canonical_state_decodes, canonical_registry_decodes,
    envelopeCodec.decode_encode]
  simp [canonicalStateBytes, canonicalState, canonicalRegistry, unknownKeyEnvelope,
    canonicalEnvelope, canonicalHeader, canonicalKey,
    canonicalRegistryCommitment, canonicalRegistryBytes, stateCodecVersion,
    registryCodecVersion, envelopeCodecVersion, credentialDomain,
    KeyRegistryProjection.findKey]

def wrongDomainEnvelope : SignedEnvelope :=
  { canonicalEnvelope with
    header := { canonicalHeader with domain := 0 :: credentialDomain } }

@[simp] theorem wrong_domain_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes
      (envelopeCodec.encode wrongDomainEnvelope) = .error .wrongDomain := by
  unfold prepare
  rw [canonical_state_decodes, canonical_registry_decodes,
    envelopeCodec.decode_encode]
  simp [canonicalStateBytes, canonicalState, canonicalRegistry, wrongDomainEnvelope,
    canonicalEnvelope, canonicalHeader, canonicalKey,
    canonicalRegistryCommitment, canonicalRegistryBytes, stateCodecVersion,
    registryCodecVersion, envelopeCodecVersion, credentialDomain,
    KeyRegistryProjection.findKey]

def wrongMessageEnvelope : SignedEnvelope :=
  { canonicalEnvelope with
    header := { canonicalHeader with message := 0 :: canonicalMessage } }

@[simp] theorem wrong_message_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes
      (envelopeCodec.encode wrongMessageEnvelope) = .error .wrongMessage := by
  unfold prepare
  rw [canonical_state_decodes, canonical_registry_decodes,
    envelopeCodec.decode_encode]
  simp [canonicalStateBytes, canonicalState, canonicalRegistry, wrongMessageEnvelope,
    canonicalEnvelope, canonicalHeader, canonicalKey,
    canonicalRegistryCommitment, canonicalRegistryBytes, stateCodecVersion,
    registryCodecVersion, envelopeCodecVersion, credentialDomain,
    KeyRegistryProjection.findKey]

def wrongAlgorithmEnvelope : SignedEnvelope :=
  { canonicalEnvelope with
    header := { canonicalHeader with algorithm := ed25519Algorithm + 1 } }

@[simp] theorem wrong_algorithm_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes
      (envelopeCodec.encode wrongAlgorithmEnvelope) = .error .wrongAlgorithm := by
  unfold prepare
  rw [canonical_state_decodes, canonical_registry_decodes,
    envelopeCodec.decode_encode]
  simp [canonicalStateBytes, canonicalState, canonicalRegistry, wrongAlgorithmEnvelope,
    canonicalEnvelope, canonicalHeader, canonicalKey,
    canonicalRegistryCommitment, canonicalRegistryBytes, stateCodecVersion,
    registryCodecVersion, envelopeCodecVersion, credentialDomain,
    ed25519Algorithm, KeyRegistryProjection.findKey]

def rotatedKey : KeyRecord :=
  { keyId := canonicalKey.keyId
    keyEpoch := canonicalKey.keyEpoch + 1
    algorithm := canonicalKey.algorithm
    subject := canonicalKey.subject
    publicKey := canonicalKey.publicKey
    activeFrom := 6
    activeUntil := 10 }

def rotatedRegistry : KeyRegistryProjection :=
  { canonicalRegistry with registryEpoch := 6, keys := [rotatedKey] }

def rotatedState : ControllerState := (withCommitment rotatedRegistry).1
def rotatedCommitment : Digest := (withCommitment rotatedRegistry).2
def oldEpochAfterRotation : SignedEnvelope :=
  canonicalEnvelope

@[simp] theorem rotated_key_selected :
    rotatedRegistry.findKey canonicalKey.keyId = some rotatedKey := by
  rfl

@[simp] theorem rotated_epoch_rejects_old_key :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage (stateCodec.encode rotatedState)
      (registryCodec.encode rotatedRegistry)
      (envelopeCodec.encode oldEpochAfterRotation) =
      .error .wrongKeyEpoch := by
  unfold prepare
  rw [stateCodec.decode_encode, registryCodec.decode_encode,
    envelopeCodec.decode_encode]
  simp [rotatedState, rotatedCommitment, withCommitment, rotatedRegistry,
    rotatedKey, oldEpochAfterRotation, canonicalState, canonicalRegistry, canonicalEnvelope, canonicalHeader,
    canonicalKey, canonicalRegistryCommitment, stateCodecVersion,
    registryCodecVersion, envelopeCodecVersion, credentialDomain,
    KeyRegistryProjection.findKey]

def staleKey : KeyRecord := { canonicalKey with activeUntil := 4 }
def staleRegistry : KeyRegistryProjection :=
  { canonicalRegistry with keys := [staleKey] }
def staleState : ControllerState := (withCommitment staleRegistry).1
def staleCommitment : Digest := (withCommitment staleRegistry).2
def staleEnvelope : SignedEnvelope := canonicalEnvelope

@[simp] theorem stale_key_selected :
    staleRegistry.findKey canonicalKey.keyId = some staleKey := by
  rfl

@[simp] theorem stale_key_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage (stateCodec.encode staleState)
      (registryCodec.encode staleRegistry)
      (envelopeCodec.encode staleEnvelope) = .error .staleKey := by
  unfold prepare
  rw [stateCodec.decode_encode, registryCodec.decode_encode,
    envelopeCodec.decode_encode]
  simp [staleState, staleCommitment, withCommitment, staleRegistry, staleKey,
    staleEnvelope, canonicalState, canonicalRegistry,
    canonicalEnvelope, canonicalHeader, canonicalKey,
    canonicalRegistryCommitment, stateCodecVersion, registryCodecVersion,
    envelopeCodecVersion, credentialDomain, KeyRegistryProjection.findKey]

@[simp] theorem replayed_nullifier_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage (stateCodec.encode canonicalNextState)
      canonicalRegistryBytes canonicalEnvelopeBytes =
      .error .replayedNullifier := by
  unfold prepare
  rw [stateCodec.decode_encode, canonical_registry_decodes,
    canonical_envelope_decodes]
  simp [canonicalNextState, Prepared.nextState, canonicalPrepared,
    canonicalState, canonicalRegistry, canonicalEnvelopeBytes, canonicalEnvelope, canonicalHeader,
    canonicalKey, canonicalRegistryCommitment, canonicalRegistryBytes,
    stateCodecVersion, registryCodecVersion, envelopeCodecVersion,
    credentialDomain, KeyRegistryProjection.findKey]

@[simp] theorem malformed_envelope_rejected :
    prepare (NativeError := Unit) useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes [] =
      .error .malformedEnvelope := by
  unfold prepare
  rw [canonical_state_decodes, canonical_registry_decodes]
  rfl

def rejectingVerifier : OpaqueVerifier Nat := fun _ _ _ => .ok false
def failingVerifier : OpaqueVerifier Nat := fun _ _ _ => .error 503

@[simp] theorem false_signature_rejected :
    runNative rejectingVerifier useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes
      canonicalEnvelopeBytes = .error .invalidSignature := by
  unfold runNative
  rw [canonical_prepare]
  rfl

@[simp] theorem native_error_remains_opaque :
    runNative failingVerifier useRequest.subject.value credentialDomain
      canonicalMessage canonicalStateBytes canonicalRegistryBytes
      canonicalEnvelopeBytes = .error (.nativeVerify 503) := by
  unfold runNative
  rw [canonical_prepare]
  rfl

/-! ## Trust audit -/

/-- Production completion additionally needs collision resistance for the
registry commitment and a physical persistence/refinement theorem.  They are
kept beside, not hidden inside, the signature completion premise. -/
structure ProductionCompletion
    (Authenticates : List UInt8 -> List UInt8 -> List UInt8 -> Prop)
    (SignerIssued : Nat -> Nat -> List UInt8 -> List UInt8 -> Prop)
    (RegistryCollisionResistant PersistentStateRefinement : Prop) : Prop where
  signature : SignatureCompletion demoVerifier Authenticates SignerIssued
  registryCollisionResistant : RegistryCollisionResistant
  persistentStateRefinement : PersistentStateRefinement

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.CredentialSignedEnvelopeEndpoint.semantic_path_of_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms semantic_path_of_completion
/-- info: 'Minidregg.Assurance.CredentialSignedEnvelopeEndpoint.rotated_epoch_rejects_old_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms rotated_epoch_rejects_old_key

end

end Minidregg.Assurance.CredentialSignedEnvelopeEndpoint
