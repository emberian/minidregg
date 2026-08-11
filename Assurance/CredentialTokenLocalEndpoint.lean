/-
# Assurance.CredentialTokenLocalEndpoint -- token bytes reach guarded use

`DeployedCredentialLifecycle` closes the logical issue, strict attenuation,
use, revocation, epoch rotation, and durable-intent story.  This module adds the
smallest consumer-shaped boundary on top of that result:

* stable, versioned codecs for the token, use request, revocation request,
  persistent authority record, and endpoint response;
* one byte-to-byte controller whose successful use is possible only for the
  exact request-indexed `AcceptedCredential` already constructed by Lean;
* a bounded stage/install/crash model showing lost-response restart and exact
  retry without a second logical use;
* rejection teeth for attenuation-field substitution, retargeting, stale
  authority roots, channel revocation, and policy-epoch rotation; and
* an opaque, fallible native read/replace boundary.  Native code receives and
  returns bytes only; it cannot mint an authorization or semantic response.

The local store below is a control model.  No theorem asserts POSIX atomicity,
`fsync`, stable media, key custody, signature soundness, an authenticated
network transport, or refinement of a Rust implementation.  Those ceilings
remain explicit at the end of the file.
-/
import Assurance.DeployedCredentialLifecycle
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Assurance.CredentialTokenLocalEndpoint

open Minidregg.Assurance.DeployedCredentialLifecycle
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.CredentialAuthorityFamily
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## Stable first-order wire codecs -/

def tokenCodecVersion : Nat := 1
def endpointVersion : Nat := 1
def persistentCodecVersion : Nat := 1

/-- A token is transport data, never a new authorization mode.  Every field
needed to identify the strict child, its parent/root, its request scope and
epochs, and the exact request digest is explicit on the wire. -/
structure TokenWire where
  codecVersion : Nat
  authorityRoot : Digest
  capabilityId : Nat
  rootId : Nat
  parentId : Nat
  issuerId : Nat
  holderSubject : Nat
  targetId : Nat
  verbTag : Nat
  maxCost : Nat
  notBefore : Nat
  notAfter : Nat
  issuerEpoch : Nat
  policyId : Nat
  policyEpoch : Nat
  channelId : Nat
  requestDigest : Digest
  deriving DecidableEq, Repr

abbrev TokenTuple :=
  Nat × Digest × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat ×
    Nat × Nat × Nat × Nat × Nat × Digest

def tokenTupleStream : StreamCodec TokenTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product StreamCodec.nat
                    (StreamCodec.product StreamCodec.nat
                      (StreamCodec.product StreamCodec.nat
                        (StreamCodec.product StreamCodec.nat
                          (StreamCodec.product StreamCodec.nat
                            (StreamCodec.product StreamCodec.nat
                              (StreamCodec.product StreamCodec.nat
                                (StreamCodec.product StreamCodec.nat
                                  digestStream)))))))))))))))

def TokenWire.toTuple (token : TokenWire) : TokenTuple :=
  (token.codecVersion, token.authorityRoot, token.capabilityId, token.rootId,
    token.parentId, token.issuerId, token.holderSubject, token.targetId,
    token.verbTag, token.maxCost, token.notBefore, token.notAfter,
    token.issuerEpoch, token.policyId, token.policyEpoch, token.channelId,
    token.requestDigest)

def TokenWire.ofTuple : TokenTuple -> TokenWire
  | (codecVersion, authorityRoot, capabilityId, rootId, parentId, issuerId,
      holderSubject, targetId, verbTag, maxCost, notBefore, notAfter,
      issuerEpoch, policyId, policyEpoch, channelId, requestDigest) =>
    { codecVersion
      authorityRoot
      capabilityId
      rootId
      parentId
      issuerId
      holderSubject
      targetId
      verbTag
      maxCost
      notBefore
      notAfter
      issuerEpoch
      policyId
      policyEpoch
      channelId
      requestDigest }

@[simp] theorem TokenWire.ofTuple_toTuple (token : TokenWire) :
    TokenWire.ofTuple token.toTuple = token := by
  cases token
  rfl

def tokenStream : StreamCodec TokenWire :=
  StreamCodec.xmap tokenTupleStream TokenWire.toTuple TokenWire.ofTuple
    TokenWire.ofTuple_toTuple

def tokenCodec : LawfulCodec TokenWire := tokenStream.toLawful

/- The complete lossless `RequestWire`, in the field order already pinned by
`AuthorizationDeclaration.requestFieldOrder`. -/
abbrev RequestTuple :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat ×
    Nat × Nat × Nat × Nat

def requestTupleStream : StreamCodec RequestTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product StreamCodec.nat
                    (StreamCodec.product StreamCodec.nat
                      (StreamCodec.product StreamCodec.nat
                        (StreamCodec.product StreamCodec.nat
                          (StreamCodec.product StreamCodec.nat
                            (StreamCodec.product StreamCodec.nat
                              (StreamCodec.product StreamCodec.nat
                                StreamCodec.nat))))))))))))))

def requestTuple (request : RequestWire) : RequestTuple :=
  (request.domain, request.semantics, request.federation,
    request.resourceKind, request.subject, request.subjectKeyEpoch,
    request.target, request.verb, request.argsDigest, request.effectsDigest,
    request.nonce, request.height, request.preStateRoot, request.policyId,
    request.policyEpoch, request.cost)

def requestOfTuple : RequestTuple -> RequestWire
  | (domain, semantics, federation, resourceKind, subject, subjectKeyEpoch,
      target, verb, argsDigest, effectsDigest, nonce, height, preStateRoot,
      policyId, policyEpoch, cost) =>
    { domain
      semantics
      federation
      resourceKind
      subject
      subjectKeyEpoch
      target
      verb
      argsDigest
      effectsDigest
      nonce
      height
      preStateRoot
      policyId
      policyEpoch
      cost }

@[simp] theorem requestOfTuple_tuple (request : RequestWire) :
    requestOfTuple (requestTuple request) = request := by
  cases request
  rfl

def requestWireStream : StreamCodec RequestWire :=
  StreamCodec.xmap requestTupleStream requestTuple requestOfTuple
    requestOfTuple_tuple

def requestWireCodec : LawfulCodec RequestWire := requestWireStream.toLawful

/-- One use request carries the token bytes and the entire canonical request
word.  The authority root is repeated deliberately: admission checks all
three copies (store, token, request header) against one another. -/
structure UseWire where
  endpointVersion : Nat
  expectedAuthorityRoot : Digest
  tokenBytes : List UInt8
  request : RequestWire
  deriving DecidableEq, Repr

abbrev UseTuple := Nat × Digest × List UInt8 × RequestWire

def useTupleStream : StreamCodec UseTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
      (StreamCodec.product bytesStream requestWireStream))

def UseWire.toTuple (request : UseWire) : UseTuple :=
  (request.endpointVersion, request.expectedAuthorityRoot,
    request.tokenBytes, request.request)

def UseWire.ofTuple : UseTuple -> UseWire
  | (version, root, token, request) =>
      ⟨version, root, token, request⟩

@[simp] theorem UseWire.ofTuple_toTuple (request : UseWire) :
    UseWire.ofTuple request.toTuple = request := by
  cases request
  rfl

def useStream : StreamCodec UseWire :=
  StreamCodec.xmap useTupleStream UseWire.toTuple UseWire.ofTuple
    UseWire.ofTuple_toTuple

def useCodec : LawfulCodec UseWire := useStream.toLawful

/-- Administrative close request.  This narrow endpoint revokes the one
transport channel and advances the policy epoch in the same installed local
record.  The semantic effects themselves are the already accepted `revoked`
and `rotated` values in `DeployedCredentialLifecycle`. -/
structure RevokeWire where
  endpointVersion : Nat
  expectedAuthorityRoot : Digest
  channelId : Nat
  expectedPolicyEpoch : Nat
  nextPolicyEpoch : Nat
  revokeNullifier : Nat
  rotateNullifier : Nat
  deriving DecidableEq, Repr

abbrev RevokeTuple := Nat × Digest × Nat × Nat × Nat × Nat × Nat

def revokeTupleStream : StreamCodec RevokeTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))

def RevokeWire.toTuple (request : RevokeWire) : RevokeTuple :=
  (request.endpointVersion, request.expectedAuthorityRoot, request.channelId,
    request.expectedPolicyEpoch, request.nextPolicyEpoch,
    request.revokeNullifier, request.rotateNullifier)

def RevokeWire.ofTuple : RevokeTuple -> RevokeWire
  | (version, root, channel, expectedEpoch, nextEpoch, revokeNul, rotateNul) =>
      ⟨version, root, channel, expectedEpoch, nextEpoch, revokeNul, rotateNul⟩

@[simp] theorem RevokeWire.ofTuple_toTuple (request : RevokeWire) :
    RevokeWire.ofTuple request.toTuple = request := by
  cases request
  rfl

def revokeStream : StreamCodec RevokeWire :=
  StreamCodec.xmap revokeTupleStream RevokeWire.toTuple RevokeWire.ofTuple
    RevokeWire.ofTuple_toTuple

def revokeCodec : LawfulCodec RevokeWire := revokeStream.toLawful

inductive EndpointRequest where
  | use (request : UseWire)
  | revoke (request : RevokeWire)
  deriving DecidableEq, Repr

def endpointRequestStream : StreamCodec EndpointRequest :=
  StreamCodec.xmap (StreamCodec.sum useStream revokeStream)
    (fun request => match request with
      | .use value => .inl value
      | .revoke value => .inr value)
    (fun wire => match wire with
      | .inl value => .use value
      | .inr value => .revoke value)
    (by intro request; cases request <;> rfl)

def endpointRequestCodec : LawfulCodec EndpointRequest :=
  endpointRequestStream.toLawful

/-! ## Canonical deployed token and request binding -/

def canonicalRequestWire : RequestWire :=
  encodeRequest ⟨.object, useRequest⟩

def canonicalRequestDigest : Digest :=
  requestDigestScheme.digestWire canonicalRequestWire

def canonicalToken : TokenWire where
  codecVersion := tokenCodecVersion
  authorityRoot := attenuatedCell.root
  capabilityId := childCapability.id.value
  rootId := childCapability.root.value
  parentId := rootCapability.id.value
  issuerId := childCapability.issuer.value
  holderSubject := useRequest.subject.value
  targetId := useRequest.target.value
  verbTag := AuthorizationDeclaration.verbTag useRequest.verb
  maxCost := childCapability.scope.maxCost
  notBefore := childCapability.notBefore
  notAfter := childCapability.notAfter
  issuerEpoch := childCapability.issuerEpoch
  policyId := childCapability.policyId.value
  policyEpoch := childCapability.policyEpoch
  channelId := 9
  requestDigest := canonicalRequestDigest

def canonicalTokenBytes : List UInt8 := tokenCodec.encode canonicalToken

def canonicalUse : UseWire where
  endpointVersion := endpointVersion
  expectedAuthorityRoot := attenuatedCell.root
  tokenBytes := canonicalTokenBytes
  request := canonicalRequestWire

def canonicalRevoke : RevokeWire where
  endpointVersion := endpointVersion
  expectedAuthorityRoot := attenuatedCell.root
  channelId := 9
  expectedPolicyEpoch := 2
  nextPolicyEpoch := 3
  revokeNullifier := revokeDeclaration.operationNullifier
  rotateNullifier := rotateDeclaration.operationNullifier

@[simp] theorem canonical_token_decodes :
    tokenCodec.decode canonicalTokenBytes = some canonicalToken :=
  tokenCodec.decode_encode canonicalToken

@[simp] theorem canonical_request_decodes :
    requestWireCodec.decode (requestWireCodec.encode canonicalRequestWire) =
      some canonicalRequestWire :=
  requestWireCodec.decode_encode canonicalRequestWire

@[simp] theorem canonical_request_pre_state_root :
    canonicalRequestWire.preStateRoot = attenuatedCell.root.value := by
  rfl

@[simp] theorem canonical_token_policy_epoch :
    canonicalToken.policyEpoch = 2 := by
  rfl

@[simp] theorem canonical_token_authority_root :
    canonicalToken.authorityRoot = attenuatedCell.root := by
  rfl

@[simp] theorem canonical_token_request_digest :
    canonicalToken.requestDigest = canonicalRequestDigest := by
  rfl

@[simp] theorem canonical_use_endpoint_version :
    canonicalUse.endpointVersion = endpointVersion := by
  rfl

/-- The token digest is not independently supplied authority: it is exactly
the digest retained by the existing request-indexed accepted credential. -/
theorem canonical_token_request_binding :
    canonicalToken.requestDigest = acceptedToken.requestBinding.digest := by
  rw [acceptedToken.requestBinding.digest_is_canonical]
  rfl

/-- The successful wire names the same child whose proof-relevant lineage
contains the strict attenuation edge. -/
theorem canonical_token_strict_attenuation :
    childCapability.StrictAttenuates rootCapability :=
  strict_edge

/-! ## Persistent local authority record -/

/-- This is the entire restart record interpreted by the endpoint.  It is not
the canonical authority cell itself; its root/epoch/revocation fields are
guards checked against the Lean-owned deployed values. -/
structure PersistentRecord where
  codecVersion : Nat
  authorityRoot : Digest
  policyEpoch : Nat
  channelRevoked : Bool
  acceptedRequest : Option Digest
  deriving DecidableEq, Repr

abbrev PersistentTuple := Nat × Digest × Nat × Bool × Option Digest

def persistentTupleStream : StreamCodec PersistentTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.bool
          (StreamCodec.option digestStream))))

def PersistentRecord.toTuple (record : PersistentRecord) : PersistentTuple :=
  (record.codecVersion, record.authorityRoot, record.policyEpoch,
    record.channelRevoked, record.acceptedRequest)

def PersistentRecord.ofTuple : PersistentTuple -> PersistentRecord
  | (version, root, epoch, revoked, accepted) =>
      ⟨version, root, epoch, revoked, accepted⟩

@[simp] theorem PersistentRecord.ofTuple_toTuple (record : PersistentRecord) :
    PersistentRecord.ofTuple record.toTuple = record := by
  cases record
  rfl

def persistentStream : StreamCodec PersistentRecord :=
  StreamCodec.xmap persistentTupleStream PersistentRecord.toTuple
    PersistentRecord.ofTuple PersistentRecord.ofTuple_toTuple

def persistentCodec : LawfulCodec PersistentRecord := persistentStream.toLawful

def initialRecord : PersistentRecord where
  codecVersion := persistentCodecVersion
  authorityRoot := attenuatedCell.root
  policyEpoch := 2
  channelRevoked := false
  acceptedRequest := none

def usedRecord : PersistentRecord :=
  { initialRecord with acceptedRequest := some canonicalRequestDigest }

def revokedRecord : PersistentRecord where
  codecVersion := persistentCodecVersion
  authorityRoot := finalCell.root
  policyEpoch := 3
  channelRevoked := true
  acceptedRequest := some canonicalRequestDigest

def revokedOnlyRecord : PersistentRecord :=
  { usedRecord with channelRevoked := true }

def rotatedOnlyRecord : PersistentRecord :=
  { usedRecord with policyEpoch := 3 }

def initialRecordBytes : List UInt8 := persistentCodec.encode initialRecord
def usedRecordBytes : List UInt8 := persistentCodec.encode usedRecord
def revokedRecordBytes : List UInt8 := persistentCodec.encode revokedRecord

/-! ## Response bytes and Lean-owned admission -/

inductive EndpointResponse where
  | used (requestDigest : Digest) (replayed : Bool)
  | revoked (newAuthorityRoot : Digest) (newPolicyEpoch : Nat)
  deriving DecidableEq, Repr

abbrev ResponseWire := Sum (Digest × Bool) (Digest × Nat)

def responseWireStream : StreamCodec ResponseWire :=
  StreamCodec.sum
    (StreamCodec.product digestStream StreamCodec.bool)
    (StreamCodec.product digestStream StreamCodec.nat)

def responseStream : StreamCodec EndpointResponse :=
  StreamCodec.xmap responseWireStream
    (fun response => match response with
      | .used digest replayed => .inl (digest, replayed)
      | .revoked root epoch => .inr (root, epoch))
    (fun wire => match wire with
      | .inl (digest, replayed) => .used digest replayed
      | .inr (root, epoch) => .revoked root epoch)
    (by intro response; cases response <;> rfl)

def responseCodec : LawfulCodec EndpointResponse := responseStream.toLawful

inductive Failure (NativeError : Type) where
  | nativeRead (error : NativeError)
  | nativeWrite (error : NativeError)
  | malformedRequest
  | malformedStore
  | wrongPersistentVersion
  | wrongEndpointVersion
  | malformedToken
  | wrongToken
  | wrongRequest
  | staleAuthority
  | revoked
  | staleEpoch
  | replayConflict
  | wrongRevocation
  deriving DecidableEq, Repr

structure Plan where
  responseBytes : List UInt8
  nextRecordBytes : List UInt8
  deriving DecidableEq, Repr

def usedResponse (replayed : Bool) : EndpointResponse :=
  .used canonicalRequestDigest replayed

def usePlan {NativeError : Type} (record : PersistentRecord)
    (request : UseWire) : Except (Failure NativeError) Plan :=
  if record.codecVersion != persistentCodecVersion then
    .error .wrongPersistentVersion
  else if request.endpointVersion != endpointVersion then
    .error .wrongEndpointVersion
  else
    match tokenCodec.decode request.tokenBytes with
    | none => .error .malformedToken
    | some token =>
        if token != canonicalToken then .error .wrongToken
        else if request.request != canonicalRequestWire then .error .wrongRequest
        else if record.channelRevoked then .error .revoked
        else if request.expectedAuthorityRoot != record.authorityRoot then
          .error .staleAuthority
        else if token.authorityRoot != record.authorityRoot then
          .error .staleAuthority
        else if request.request.preStateRoot != record.authorityRoot.value then
          .error .staleAuthority
        else if record.policyEpoch != token.policyEpoch then .error .staleEpoch
        else
          match record.acceptedRequest with
          | none =>
              .ok
                { responseBytes := responseCodec.encode (usedResponse false)
                  nextRecordBytes := usedRecordBytes }
          | some digest =>
              if digest = token.requestDigest then
                .ok
                  { responseBytes := responseCodec.encode (usedResponse true)
                    nextRecordBytes := persistentCodec.encode record }
              else .error .replayConflict

def revokePlan {NativeError : Type} (record : PersistentRecord)
    (request : RevokeWire) : Except (Failure NativeError) Plan :=
  if record.codecVersion != persistentCodecVersion then
    .error .wrongPersistentVersion
  else if request.endpointVersion != endpointVersion then
    .error .wrongEndpointVersion
  else if record != usedRecord then .error .wrongRevocation
  else if request != canonicalRevoke then .error .wrongRevocation
  else
    .ok
      { responseBytes := responseCodec.encode
          (.revoked finalCell.root 3)
        nextRecordBytes := revokedRecordBytes }

/-- Decode store and request bytes before any semantic branch.  All authority
meaning and every success byte are minted on the Lean side. -/
def plan {NativeError : Type} (recordBytes requestBytes : List UInt8) :
    Except (Failure NativeError) Plan :=
  match persistentCodec.decode recordBytes with
  | none => .error .malformedStore
  | some record =>
      match endpointRequestCodec.decode requestBytes with
      | none => .error .malformedRequest
      | some (.use request) => usePlan record request
      | some (.revoke request) => revokePlan record request

def canonicalUseBytes : List UInt8 :=
  endpointRequestCodec.encode (.use canonicalUse)

def canonicalRevokeBytes : List UInt8 :=
  endpointRequestCodec.encode (.revoke canonicalRevoke)

def firstUsePlan : Plan where
  responseBytes := responseCodec.encode (usedResponse false)
  nextRecordBytes := usedRecordBytes

def retryUsePlan : Plan where
  responseBytes := responseCodec.encode (usedResponse true)
  nextRecordBytes := usedRecordBytes

def canonicalRevokePlan : Plan where
  responseBytes := responseCodec.encode (.revoked finalCell.root 3)
  nextRecordBytes := revokedRecordBytes

@[simp] theorem first_use_response_decodes :
    responseCodec.decode firstUsePlan.responseBytes =
      some (usedResponse false) := by
  simp [firstUsePlan, responseCodec.decode_encode]

@[simp] theorem retry_response_decodes :
    responseCodec.decode retryUsePlan.responseBytes =
      some (usedResponse true) := by
  simp [retryUsePlan, responseCodec.decode_encode]

@[simp] theorem used_persistence_decodes :
    persistentCodec.decode firstUsePlan.nextRecordBytes = some usedRecord := by
  simp [firstUsePlan, usedRecordBytes, persistentCodec.decode_encode]

@[simp] theorem revoked_persistence_decodes :
    persistentCodec.decode canonicalRevokePlan.nextRecordBytes =
      some revokedRecord := by
  simp [canonicalRevokePlan, revokedRecordBytes, persistentCodec.decode_encode]

@[simp] theorem first_use_accepted {NativeError : Type} :
    plan (NativeError := NativeError) initialRecordBytes canonicalUseBytes =
      .ok firstUsePlan := by
  unfold plan
  simp only [initialRecordBytes, canonicalUseBytes]
  rw [persistentCodec.decode_encode, endpointRequestCodec.decode_encode]
  simp only
  unfold usePlan
  simp only [canonicalUse, canonicalTokenBytes]
  rw [tokenCodec.decode_encode]
  simp [initialRecord, usedRecord, usedRecordBytes, firstUsePlan,
    endpointVersion, persistentCodecVersion]

@[simp] theorem exact_retry_is_idempotent {NativeError : Type} :
    plan (NativeError := NativeError) usedRecordBytes canonicalUseBytes =
      .ok retryUsePlan := by
  unfold plan
  simp only [usedRecordBytes, canonicalUseBytes]
  rw [persistentCodec.decode_encode, endpointRequestCodec.decode_encode]
  simp only
  unfold usePlan
  simp only [canonicalUse, canonicalTokenBytes]
  rw [tokenCodec.decode_encode]
  simp [usedRecordBytes, usedRecord, initialRecord, retryUsePlan, endpointVersion,
    persistentCodecVersion]

@[simp] theorem canonical_revocation_accepted {NativeError : Type} :
    plan (NativeError := NativeError) usedRecordBytes canonicalRevokeBytes =
      .ok canonicalRevokePlan := by
  unfold plan
  simp only [usedRecordBytes, canonicalRevokeBytes]
  rw [persistentCodec.decode_encode, endpointRequestCodec.decode_encode]
  simp only
  simp [revokePlan, usedRecord, initialRecord, canonicalRevokePlan,
    canonicalRevoke, endpointVersion, persistentCodecVersion]

/-- Endpoint use is joined to the existing proof-relevant authorization and
guarded durable intent, including its exact authority read guard and accepted
payload installation. -/
theorem first_use_semantic_join :
    plan (NativeError := Unit) initialRecordBytes canonicalUseBytes =
        .ok firstUsePlan /\
      acceptedToken.carrier = .token /\
      childCapability.StrictAttenuates rootCapability /\
      acceptedToken.requestBinding.wire = canonicalRequestWire /\
      guardedUseIntent.readGuards =
        [{ cellId := authorityCellId, expectedRoot := attenuatedCell.root }] /\
      Minidregg.Kernel.DurableDataIntent.execute .complete durableBefore
          guardedUseIntent =
        .accepted
          (Minidregg.Kernel.DurableDataIntent.DataSnapshot.install
            durableBefore guardedUseIntent) := by
  exact ⟨first_use_accepted, rfl, strict_edge, rfl,
    guarded_use_observes_exact_authority_root, guarded_use_installs_payload⟩

/-! ## Executable rejection teeth -/

def widenedToken : TokenWire :=
  { canonicalToken with maxCost := rootCapability.scope.maxCost }

theorem widenedToken_ne : widenedToken ≠ canonicalToken := by
  intro equal
  have costEqual := congrArg TokenWire.maxCost equal
  norm_num [widenedToken, canonicalToken, rootCapability, rootScope,
    childCapability, childScope] at costEqual

def widenedUse : UseWire :=
  { canonicalUse with tokenBytes := tokenCodec.encode widenedToken }

@[simp] theorem authority_widening_rejected :
    plan (NativeError := Unit) initialRecordBytes
        (endpointRequestCodec.encode (.use widenedUse)) =
      .error .wrongToken := by
  unfold plan
  simp only [initialRecordBytes]
  rw [persistentCodec.decode_encode, endpointRequestCodec.decode_encode]
  simp only
  unfold usePlan
  simp only [widenedUse]
  rw [tokenCodec.decode_encode]
  simp [widenedToken_ne, canonicalUse, endpointVersion,
    persistentCodecVersion, initialRecord]

def retargetedUse : UseWire :=
  { canonicalUse with
    request := encodeRequest ⟨.object, useRequest.retarget ⟨701⟩⟩ }

theorem retargetedRequest_ne :
    retargetedUse.request ≠ canonicalRequestWire := by
  exact retarget_changes_wire useRequest ⟨701⟩ (by decide)

@[simp] theorem retargeted_request_rejected :
    plan (NativeError := Unit) initialRecordBytes
        (endpointRequestCodec.encode (.use retargetedUse)) =
      .error .wrongRequest := by
  unfold plan
  simp only [initialRecordBytes]
  rw [persistentCodec.decode_encode, endpointRequestCodec.decode_encode]
  simp only
  unfold usePlan
  simp only [retargetedUse, canonicalUse, canonicalTokenBytes]
  rw [tokenCodec.decode_encode]
  have different :
      encodeRequest ⟨.object, useRequest.retarget ⟨701⟩⟩ ≠
        canonicalRequestWire :=
    retargetedRequest_ne
  simp [different, endpointVersion, persistentCodecVersion, initialRecord]

def staleRootUse : UseWire :=
  { canonicalUse with
    expectedAuthorityRoot := ⟨attenuatedCell.root.value + 1⟩ }

theorem staleRootUse_ne :
    staleRootUse.expectedAuthorityRoot ≠ initialRecord.authorityRoot := by
  intro equal
  have values := congrArg Digest.value equal
  simp [staleRootUse, initialRecord] at values

@[simp] theorem stale_authority_rejected :
    plan (NativeError := Unit) initialRecordBytes
        (endpointRequestCodec.encode (.use staleRootUse)) =
      .error .staleAuthority := by
  unfold plan
  simp only [initialRecordBytes]
  rw [persistentCodec.decode_encode, endpointRequestCodec.decode_encode]
  simp only
  unfold usePlan
  simp only [staleRootUse, canonicalUse, canonicalTokenBytes]
  rw [tokenCodec.decode_encode]
  have different :
      (⟨attenuatedCell.root.value + 1⟩ : Digest) ≠
        initialRecord.authorityRoot :=
    staleRootUse_ne
  have rootDifferent :
      (⟨attenuatedCell.root.value + 1⟩ : Digest) ≠ attenuatedCell.root := by
    simpa [initialRecord] using different
  simp [endpointVersion, persistentCodecVersion, initialRecord]
  intro equal
  exact rootDifferent equal

@[simp] theorem revoked_channel_rejects_use :
    plan (NativeError := Unit) (persistentCodec.encode revokedOnlyRecord)
        canonicalUseBytes = .error .revoked := by
  unfold plan
  simp only [canonicalUseBytes]
  rw [persistentCodec.decode_encode, endpointRequestCodec.decode_encode]
  simp only
  unfold usePlan
  simp only [canonicalUse, canonicalTokenBytes]
  rw [tokenCodec.decode_encode]
  simp [revokedOnlyRecord, usedRecord, initialRecord,
    endpointVersion, persistentCodecVersion]

@[simp] theorem rotated_epoch_rejects_old_token :
    plan (NativeError := Unit) (persistentCodec.encode rotatedOnlyRecord)
        canonicalUseBytes = .error .staleEpoch := by
  unfold plan
  simp only [canonicalUseBytes]
  rw [persistentCodec.decode_encode, endpointRequestCodec.decode_encode]
  simp only
  unfold usePlan
  simp only [canonicalUse, canonicalTokenBytes]
  rw [tokenCodec.decode_encode]
  simp [rotatedOnlyRecord, usedRecord, initialRecord, endpointVersion,
    persistentCodecVersion]

@[simp] theorem closed_record_rejects_use :
    plan (NativeError := Unit) revokedRecordBytes canonicalUseBytes =
      .error .revoked := by
  unfold plan
  simp only [revokedRecordBytes, canonicalUseBytes]
  rw [persistentCodec.decode_encode, endpointRequestCodec.decode_encode]
  simp only
  unfold usePlan
  simp only [canonicalUse, canonicalTokenBytes]
  rw [tokenCodec.decode_encode]
  simp [revokedRecord, endpointVersion,
    persistentCodecVersion]

/-! ## Restart-safe local replacement control model -/

def maxPersistentBytes : Nat :=
  max usedRecordBytes.length revokedRecordBytes.length + 1

namespace LocalStore

inductive Failure where
  | tooLarge
  | noStage
  deriving DecidableEq, Repr

structure State where
  live : List UInt8
  staged : Option (List UInt8)
  deriving DecidableEq, Repr

def initial : State := ⟨initialRecordBytes, none⟩

def stage (state : State) (bytes : List UInt8) : Except Failure State :=
  if maxPersistentBytes < bytes.length then .error .tooLarge
  else .ok { state with staged := some bytes }

/-- The model's single visibility point.  A physical implementation must
separately refine this transition. -/
def install (state : State) : Except Failure State :=
  match state.staged with
  | none => .error .noStage
  | some bytes => .ok ⟨bytes, none⟩

def crash (state : State) : State :=
  { state with staged := none }

def stagedUse : State :=
  match stage initial usedRecordBytes with
  | .ok state => state
  | .error _ => initial

def installedUse : State :=
  match install stagedUse with
  | .ok state => state
  | .error _ => initial

def stagedRevocation : State :=
  match stage installedUse revokedRecordBytes with
  | .ok state => state
  | .error _ => installedUse

def installedRevocation : State :=
  match install stagedRevocation with
  | .ok state => state
  | .error _ => installedUse

@[simp] theorem crash_before_use_install_preserves_old_record :
    (crash stagedUse).live = initialRecordBytes := by
  have bounded : ¬ maxPersistentBytes < usedRecordBytes.length := by
    simp [maxPersistentBytes]
    omega
  simp [stagedUse, stage, bounded, crash, initial]

@[simp] theorem use_install_survives_restart :
    (crash installedUse).live = usedRecordBytes := by
  have bounded : ¬ maxPersistentBytes < usedRecordBytes.length := by
    simp [maxPersistentBytes]
    omega
  simp [installedUse, stagedUse, stage, bounded, install, crash, initial]

@[simp] theorem restarted_exact_retry_is_idempotent :
    plan (NativeError := Unit) (crash installedUse).live canonicalUseBytes =
      .ok retryUsePlan := by
  rw [use_install_survives_restart]
  exact exact_retry_is_idempotent

@[simp] theorem crash_before_revocation_install_retains_live_use :
    (crash stagedRevocation).live = usedRecordBytes := by
  have useBounded : ¬ maxPersistentBytes < usedRecordBytes.length := by
    simp [maxPersistentBytes]
    omega
  have revokeBounded : ¬ maxPersistentBytes < revokedRecordBytes.length := by
    simp [maxPersistentBytes]
    omega
  simp [stagedRevocation, installedUse, stagedUse, stage, install,
    useBounded, revokeBounded, crash, initial]

@[simp] theorem revocation_install_survives_restart :
    (crash installedRevocation).live = revokedRecordBytes := by
  have useBounded : ¬ maxPersistentBytes < usedRecordBytes.length := by
    simp [maxPersistentBytes]
    omega
  have revokeBounded : ¬ maxPersistentBytes < revokedRecordBytes.length := by
    simp [maxPersistentBytes]
    omega
  simp [installedRevocation, stagedRevocation, installedUse, stagedUse,
    stage, install, useBounded, revokeBounded, crash, initial]

@[simp] theorem restarted_closed_record_rejects_old_use :
    plan (NativeError := Unit) (crash installedRevocation).live
        canonicalUseBytes = .error .revoked := by
  rw [revocation_install_survives_restart]
  exact closed_record_rejects_use

end LocalStore

/-! ## Opaque and fallible native boundary -/

abbrev OpaqueRead (Error : Type) := Unit -> Except Error (List UInt8)
abbrev OpaqueReplace (Error : Type) := List UInt8 -> Except Error Unit

/-- Native code may read and replace bytes or fail opaquely.  It never sees a
capability, request, policy, proof, or `AcceptedCredential`. -/
def runNative {Error : Type} (read : OpaqueRead Error)
    (replace : OpaqueReplace Error) (requestBytes : List UInt8) :
    Except (Failure Error) (List UInt8) :=
  match read () with
  | .error error => .error (.nativeRead error)
  | .ok recordBytes =>
      match plan recordBytes requestBytes with
      | .error reason => .error reason
      | .ok accepted =>
          match replace accepted.nextRecordBytes with
          | .error error => .error (.nativeWrite error)
          | .ok () => .ok accepted.responseBytes

def honestRead (_ : Unit) : Except Nat (List UInt8) :=
  .ok initialRecordBytes

def honestReplace (_ : List UInt8) : Except Nat Unit := .ok ()

@[simp] theorem opaque_honest_use_returns_only_response_bytes :
    runNative honestRead honestReplace canonicalUseBytes =
      .ok firstUsePlan.responseBytes := by
  unfold runNative honestRead
  simp only
  rw [first_use_accepted]
  rfl

def failedRead (_ : Unit) : Except Nat (List UInt8) := .error 404
def failedReplace (_ : List UInt8) : Except Nat Unit := .error 507

@[simp] theorem native_read_failure_is_opaque :
    runNative failedRead honestReplace canonicalUseBytes =
      .error (.nativeRead 404) := by
  rfl

@[simp] theorem native_write_failure_is_opaque :
    runNative honestRead failedReplace canonicalUseBytes =
      .error (.nativeWrite 507) := by
  unfold runNative honestRead
  simp only
  rw [first_use_accepted]
  rfl

/-! ## Explicit uninhabited deployment ceilings -/

/-- These propositions are required before the local control model may be
advertised as a secure, physically durable, remotely delivered credential
service.  This module deliberately constructs no inhabitant. -/
structure ExternalCompletion
    (KeyCustody SignatureSoundness PhysicalStoreRefinement
      NetworkAuthenticated : Prop) : Prop where
  keyCustody : KeyCustody
  signatureSoundness : SignatureSoundness
  physicalStoreRefinement : PhysicalStoreRefinement
  networkAuthenticated : NetworkAuthenticated

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.CredentialTokenLocalEndpoint.first_use_semantic_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms first_use_semantic_join
/-- info: 'Minidregg.Assurance.CredentialTokenLocalEndpoint.authority_widening_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authority_widening_rejected
/-- info: 'Minidregg.Assurance.CredentialTokenLocalEndpoint.LocalStore.restarted_exact_retry_is_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms LocalStore.restarted_exact_retry_is_idempotent

end

end Minidregg.Assurance.CredentialTokenLocalEndpoint
