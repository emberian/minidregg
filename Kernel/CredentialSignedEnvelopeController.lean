/-
# Kernel.CredentialSignedEnvelopeController -- committed credential signatures

This is the first byte-level controller for the signature carrier of
`CredentialAuthorityFamily`.  Lean owns every framing and selection decision:

* a signed header names its codec version, authority root, exact committed key
  registry, key id/epoch/algorithm, domain, message bytes, and nullifier;
* the key registry is a versioned projection committed by the controller state;
* only the uniquely selected current, live, non-revoked key reaches native
  verification; and
* success consumes the signed nullifier in the next persistent state.

Native code receives only public-key, canonical-frame, and signature bytes and
returns `Except Error Bool`.  The relation between `true` and cryptographic
authenticity, and the relation between authenticity and custody/EUF-CMA, remain
explicit premises below.  The executable digest used to pin the registry is a
representation function only; no collision-resistance theorem is claimed.
-/
import Compiler.Tower256ConcreteBackend
import Kernel.CanonicalPolicyRegistry
import Theory.CredentialAuthorityFamily

namespace Minidregg.Kernel.CredentialSignedEnvelopeController

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def stateCodecVersion : Nat := 1
def registryCodecVersion : Nat := 1
def envelopeCodecVersion : Nat := 1

/-! ## Versioned committed key projection -/

/-- One current key projection.  `activeFrom` and `activeUntil` are registry
epochs, not wall-clock timestamps.  Rotation changes `keyEpoch` and the
registry commitment; revocation changes `revoked` and the commitment. -/
structure KeyRecord where
  keyId : Nat
  keyEpoch : Nat
  algorithm : Nat
  subject : Nat
  publicKey : List UInt8
  activeFrom : Nat
  activeUntil : Nat
  revoked : Bool
  deriving DecidableEq, Repr

abbrev KeyRecordTuple :=
  Nat × Nat × Nat × Nat × List UInt8 × Nat × Nat × Bool

def keyRecordTupleStream : StreamCodec KeyRecordTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product bytesStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat StreamCodec.bool))))))

def KeyRecord.toTuple (key : KeyRecord) : KeyRecordTuple :=
  (key.keyId, key.keyEpoch, key.algorithm, key.subject, key.publicKey,
    key.activeFrom, key.activeUntil, key.revoked)

def KeyRecord.ofTuple : KeyRecordTuple -> KeyRecord
  | (keyId, keyEpoch, algorithm, subject, publicKey, activeFrom,
      activeUntil, revoked) =>
    { keyId, keyEpoch, algorithm, subject, publicKey, activeFrom,
      activeUntil, revoked }

@[simp] theorem KeyRecord.ofTuple_toTuple (key : KeyRecord) :
    KeyRecord.ofTuple key.toTuple = key := by
  cases key
  rfl

def keyRecordStream : StreamCodec KeyRecord :=
  StreamCodec.xmap keyRecordTupleStream KeyRecord.toTuple KeyRecord.ofTuple
    KeyRecord.ofTuple_toTuple

/-- This is a projection of key-custody metadata committed beneath one exact
canonical authority root.  It is not an independently authoritative host map. -/
structure KeyRegistryProjection where
  codecVersion : Nat
  authorityRoot : Digest
  registryEpoch : Nat
  keys : List KeyRecord
  deriving DecidableEq, Repr

abbrev RegistryTuple := Nat × Digest × Nat × List KeyRecord

def registryTupleStream : StreamCodec RegistryTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.list keyRecordStream)))

def KeyRegistryProjection.toTuple
    (registry : KeyRegistryProjection) : RegistryTuple :=
  (registry.codecVersion, registry.authorityRoot, registry.registryEpoch,
    registry.keys)

def KeyRegistryProjection.ofTuple : RegistryTuple -> KeyRegistryProjection
  | (version, root, epoch, keys) =>
    { codecVersion := version, authorityRoot := root,
      registryEpoch := epoch, keys := keys }

@[simp] theorem KeyRegistryProjection.ofTuple_toTuple
    (registry : KeyRegistryProjection) :
    KeyRegistryProjection.ofTuple registry.toTuple = registry := by
  cases registry
  rfl

def registryStream : StreamCodec KeyRegistryProjection :=
  StreamCodec.xmap registryTupleStream KeyRegistryProjection.toTuple
    KeyRegistryProjection.ofTuple KeyRegistryProjection.ofTuple_toTuple

def registryCodec : LawfulCodec KeyRegistryProjection :=
  registryStream.toLawful

/-- Deterministic content addressing for the projection.  This supplies exact
byte binding, not collision resistance. -/
def registryDigest (bytes : List UInt8) : Digest :=
  ⟨bytes.foldl (fun accumulator byte =>
      accumulator * 257 + byte.toNat + 1) 17⟩

/-! ## Exact signed frame -/

structure SignedHeader where
  codecVersion : Nat
  authorityRoot : Digest
  registryCommitment : Digest
  keyId : Nat
  keyEpoch : Nat
  algorithm : Nat
  domain : List UInt8
  message : List UInt8
  nullifier : Nat
  deriving DecidableEq, Repr

abbrev HeaderTuple :=
  Nat × Digest × Digest × Nat × Nat × Nat × List UInt8 × List UInt8 × Nat

def headerTupleStream : StreamCodec HeaderTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product bytesStream
                (StreamCodec.product bytesStream StreamCodec.nat)))))))

def SignedHeader.toTuple (header : SignedHeader) : HeaderTuple :=
  (header.codecVersion, header.authorityRoot, header.registryCommitment,
    header.keyId, header.keyEpoch, header.algorithm, header.domain,
    header.message, header.nullifier)

def SignedHeader.ofTuple : HeaderTuple -> SignedHeader
  | (version, root, commitment, keyId, keyEpoch, algorithm, domain,
      message, nullifier) =>
    { codecVersion := version, authorityRoot := root,
      registryCommitment := commitment, keyId := keyId, keyEpoch := keyEpoch,
      algorithm := algorithm, domain := domain, message := message,
      nullifier := nullifier }

@[simp] theorem SignedHeader.ofTuple_toTuple (header : SignedHeader) :
    SignedHeader.ofTuple header.toTuple = header := by
  cases header
  rfl

def headerStream : StreamCodec SignedHeader :=
  StreamCodec.xmap headerTupleStream SignedHeader.toTuple SignedHeader.ofTuple
    SignedHeader.ofTuple_toTuple

def headerCodec : LawfulCodec SignedHeader := headerStream.toLawful

structure SignedEnvelope where
  header : SignedHeader
  signature : List UInt8
  deriving DecidableEq, Repr

def envelopeStream : StreamCodec SignedEnvelope :=
  StreamCodec.xmap (StreamCodec.product headerStream bytesStream)
    (fun envelope => (envelope.header, envelope.signature))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro envelope; cases envelope; rfl)

def envelopeCodec : LawfulCodec SignedEnvelope := envelopeStream.toLawful

/-- The native verifier receives precisely these bytes.  In particular, it
does not receive a `Request`, `Authorized`, registry, or controller state. -/
def SignedEnvelope.frame (envelope : SignedEnvelope) : List UInt8 :=
  headerCodec.encode envelope.header

/-! ## Persistent replay state and Lean-owned planning -/

structure ControllerState where
  codecVersion : Nat
  authorityRoot : Digest
  registryCommitment : Digest
  registryEpoch : Nat
  consumedNullifiers : List Nat
  deriving DecidableEq, Repr

abbrev StateTuple := Nat × Digest × Digest × Nat × List Nat

def stateTupleStream : StreamCodec StateTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.list StreamCodec.nat))))

def ControllerState.toTuple (state : ControllerState) : StateTuple :=
  (state.codecVersion, state.authorityRoot, state.registryCommitment,
    state.registryEpoch, state.consumedNullifiers)

def ControllerState.ofTuple : StateTuple -> ControllerState
  | (version, root, commitment, epoch, nullifiers) =>
    { codecVersion := version, authorityRoot := root,
      registryCommitment := commitment, registryEpoch := epoch,
      consumedNullifiers := nullifiers }

@[simp] theorem ControllerState.ofTuple_toTuple (state : ControllerState) :
    ControllerState.ofTuple state.toTuple = state := by
  cases state
  rfl

def stateStream : StreamCodec ControllerState :=
  StreamCodec.xmap stateTupleStream ControllerState.toTuple
    ControllerState.ofTuple ControllerState.ofTuple_toTuple

def stateCodec : LawfulCodec ControllerState := stateStream.toLawful

inductive Failure (NativeError : Type) where
  | malformedState
  | malformedRegistry
  | malformedEnvelope
  | wrongStateVersion
  | wrongRegistryVersion
  | wrongEnvelopeVersion
  | staleAuthority
  | uncommittedRegistry
  | staleRegistry
  | wrongRegistryCommitment
  | wrongDomain
  | wrongMessage
  | replayedNullifier
  | unknownKey
  | wrongSubject
  | wrongKeyEpoch
  | wrongAlgorithm
  | revokedKey
  | staleKey
  | invalidSignature
  | nativeVerify (error : NativeError)
  deriving DecidableEq, Repr

/-- A successful preparation retains every selected value.  `frame` is not
supplied by native code: it is recomputed from the decoded envelope. -/
structure Prepared where
  state : ControllerState
  registry : KeyRegistryProjection
  envelope : SignedEnvelope
  key : KeyRecord
  frame : List UInt8
  frameExact : frame = envelope.frame

def KeyRegistryProjection.findKey
    (registry : KeyRegistryProjection) (keyId : Nat) : Option KeyRecord :=
  registry.keys.find? (fun key => key.keyId == keyId)

/-- Decode and check all semantic data before native verification.  The order
is intentional: malformed or stale control data never reaches crypto. -/
def prepare {NativeError : Type}
    (expectedSubject : Nat) (expectedDomain expectedMessage : List UInt8)
    (stateBytes registryBytes envelopeBytes : List UInt8) :
    Except (Failure NativeError) Prepared :=
  match stateCodec.decode stateBytes with
  | none => .error .malformedState
  | some state =>
      match registryCodec.decode registryBytes with
      | none => .error .malformedRegistry
      | some registry =>
          match envelopeCodec.decode envelopeBytes with
          | none => .error .malformedEnvelope
          | some envelope =>
              if state.codecVersion != stateCodecVersion then
                .error .wrongStateVersion
              else if registry.codecVersion != registryCodecVersion then
                .error .wrongRegistryVersion
              else if envelope.header.codecVersion != envelopeCodecVersion then
                .error .wrongEnvelopeVersion
              else if registry.authorityRoot != state.authorityRoot then
                .error .staleAuthority
              else if envelope.header.authorityRoot != state.authorityRoot then
                .error .staleAuthority
              else if registryDigest registryBytes != state.registryCommitment then
                .error .uncommittedRegistry
              else if registry.registryEpoch != state.registryEpoch then
                .error .staleRegistry
              else if envelope.header.registryCommitment !=
                  state.registryCommitment then
                .error .wrongRegistryCommitment
              else if envelope.header.domain != expectedDomain then
                .error .wrongDomain
              else if envelope.header.message != expectedMessage then
                .error .wrongMessage
              else if state.consumedNullifiers.contains
                  envelope.header.nullifier then
                .error .replayedNullifier
              else
                match registry.findKey envelope.header.keyId with
                | none => .error .unknownKey
                | some key =>
                    if key.subject != expectedSubject then .error .wrongSubject
                    else if key.keyEpoch != envelope.header.keyEpoch then
                      .error .wrongKeyEpoch
                    else if key.algorithm != envelope.header.algorithm then
                      .error .wrongAlgorithm
                    else if key.revoked then .error .revokedKey
                    else if registry.registryEpoch < key.activeFrom ||
                        key.activeUntil < registry.registryEpoch then
                      .error .staleKey
                    else
                      .ok
                        { state, registry, envelope, key
                          frame := envelope.frame
                          frameExact := rfl }

structure Admission where
  keyId : Nat
  keyEpoch : Nat
  algorithm : Nat
  message : List UInt8
  nullifier : Nat
  nextStateBytes : List UInt8
  deriving DecidableEq, Repr

def Prepared.nextState (prepared : Prepared) : ControllerState :=
  { prepared.state with
    consumedNullifiers :=
      prepared.envelope.header.nullifier ::
        prepared.state.consumedNullifiers }

def finish {NativeError : Type} (prepared : Prepared)
    (nativeResult : Except NativeError Bool) :
    Except (Failure NativeError) Admission :=
  match nativeResult with
  | .error error => .error (.nativeVerify error)
  | .ok false => .error .invalidSignature
  | .ok true =>
      .ok
        { keyId := prepared.key.keyId
          keyEpoch := prepared.key.keyEpoch
          algorithm := prepared.key.algorithm
          message := prepared.envelope.header.message
          nullifier := prepared.envelope.header.nullifier
          nextStateBytes := stateCodec.encode prepared.nextState }

abbrev OpaqueVerifier (Error : Type) :=
  List UInt8 -> List UInt8 -> List UInt8 -> Except Error Bool

/-- The only native call.  The exact selected public key and Lean-generated
frame are passed opaquely; a native error is never reinterpreted as rejection
or success. -/
def runNative {Error : Type} (verify : OpaqueVerifier Error)
    (expectedSubject : Nat) (expectedDomain expectedMessage : List UInt8)
    (stateBytes registryBytes envelopeBytes : List UInt8) :
    Except (Failure Error) Admission :=
  match prepare (NativeError := Error) expectedSubject expectedDomain
      expectedMessage stateBytes registryBytes envelopeBytes with
  | .error reason => .error reason
  | .ok prepared =>
      finish prepared
        (verify prepared.key.publicKey prepared.frame
          prepared.envelope.signature)

/-! ## Explicit cryptographic and custody ceilings -/

/-- This is the missing implementation-refinement theorem for an opaque native
verifier.  No instance is supplied by the controller. -/
structure NativeVerifierRefinement {Error : Type}
    (verify : OpaqueVerifier Error)
    (Authenticates : List UInt8 -> List UInt8 -> List UInt8 -> Prop) : Prop where
  sound : forall publicKey frame signature,
    verify publicKey frame signature = .ok true ->
      Authenticates publicKey frame signature

/-- This is the EUF-CMA/key-custody portal: an authentic signature under a
registered public key must have been issued by the corresponding protected
signer.  It too is deliberately uninhabited here. -/
structure EufCmaKeyCustody
    (Authenticates : List UInt8 -> List UInt8 -> List UInt8 -> Prop)
    (SignerIssued : Nat -> Nat -> List UInt8 -> List UInt8 -> Prop) : Prop where
  authentic_implies_issued : forall (key : KeyRecord) frame signature,
    Authenticates key.publicKey frame signature ->
      SignerIssued key.keyId key.keyEpoch frame signature

structure SignatureCompletion {Error : Type}
    (verify : OpaqueVerifier Error)
    (Authenticates : List UInt8 -> List UInt8 -> List UInt8 -> Prop)
    (SignerIssued : Nat -> Nat -> List UInt8 -> List UInt8 -> Prop) : Prop where
  native : NativeVerifierRefinement verify Authenticates
  custody : EufCmaKeyCustody Authenticates SignerIssued

theorem SignatureCompletion.issued_of_verified {Error : Type}
    {verify : OpaqueVerifier Error}
    {Authenticates : List UInt8 -> List UInt8 -> List UInt8 -> Prop}
    {SignerIssued : Nat -> Nat -> List UInt8 -> List UInt8 -> Prop}
    (completion : SignatureCompletion verify Authenticates SignerIssued)
    (prepared : Prepared)
    (verified : verify prepared.key.publicKey prepared.frame
        prepared.envelope.signature = .ok true) :
    SignerIssued prepared.key.keyId prepared.key.keyEpoch prepared.frame
      prepared.envelope.signature :=
  completion.custody.authentic_implies_issued prepared.key prepared.frame
    prepared.envelope.signature
      (completion.native.sound _ _ _ verified)

end Minidregg.Kernel.CredentialSignedEnvelopeController
