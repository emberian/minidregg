/-
# Kernel.CredentialSignedEnvelopeController -- committed credential signatures

This is the first byte-level controller for the signature carrier of
`CredentialAuthorityFamily`.  Lean owns every framing and selection decision:

* a signed header names its codec version, the plan's authority footprint (the
  exact authority values it read, `Theory.PlanBinding`), the height it is valid
  until, key id/epoch/algorithm, domain, message bytes, and nullifier.  It names
  no authority root: a signature over the root was invalidated by every
  admission anywhere in the authority cell;
* the key registry is a versioned projection committed by the controller state;
* only the uniquely selected current key within its activation window reaches
  native verification (revocation is not a record field: the key version's
  standing is read from the authority cell's presence planes by
  `CredentialSignatureAdmission.select` before this controller runs); and
* success consumes the signed nullifier in the next persistent state.

Native code receives only public-key, canonical-frame, and signature bytes and
returns `Except Error Bool`.  The relation between `true` and cryptographic
authenticity, and the relation between authenticity and custody/EUF-CMA, remain
explicit premises below.  The executable digest used to pin the registry is a
representation function only; no collision-resistance theorem is claimed.
-/
module

public import Compiler.Tower256ConcreteBackend
public import Compiler.CredentialSigningKeyCodec
public import Kernel.CanonicalPolicyRegistry
public import Theory.CredentialAuthorityFamily
public import Theory.AxiomPin

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.CredentialSignedEnvelopeController

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def stateCodecVersion : Nat := 2
def registryCodecVersion : Nat := 1
/-- Version 2: the header binds the authority footprint and `validUntil` in
place of the authority root and registry commitment.  Version-1 envelopes
refuse (`wrongEnvelopeVersion`, and their tuple no longer decodes). -/
def envelopeCodecVersion : Nat := 2

/-! ## Versioned committed key projection -/

/-- The same record and codec installed in canonical authority pages. This
compatibility name does not define a second key schema or key directory. -/
abbrev KeyRecord := Minidregg.Theory.CredentialSigningKey.KeyRecord

abbrev keyRecordStream := Minidregg.Compiler.CredentialSigningKeyCodec.keyRecordStream

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

/-- One step of `registryDigest`'s fold. -/
def registryStep (accumulator : Nat) (byte : UInt8) : Nat :=
  accumulator * 257 + byte.toNat + 1

theorem registryStep_foldl (start : Nat) (bytes : List UInt8) :
    bytes.foldl registryStep start = start * 257 ^ bytes.length + bytes.foldl registryStep 0 := by
  induction bytes generalizing start with
  | nil => simp
  | cons byte rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, ih (registryStep 0 byte)]
      simp only [registryStep, Nat.pow_succ]
      grind

/-- 257 ^ 7, below 2 ^ 63: a seven-byte chunk's fold is a scalar. -/
def registryChunkScale : Nat := 257 ^ 7

/-- `registryDigest`'s fold seven bytes at a time: one multiplication of the growing value per
chunk instead of one per byte (the value is a base-257 numeral as long as the registry). -/
def registryFoldFast (start : Nat) : List UInt8 → Nat
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest =>
      registryFoldFast (start * registryChunkScale + [b0, b1, b2, b3, b4, b5, b6].foldl registryStep 0) rest
  | rest => rest.foldl registryStep start

theorem registryFoldFast_eq (start : Nat) (bytes : List UInt8) :
    registryFoldFast start bytes = bytes.foldl registryStep start := by
  fun_induction registryFoldFast start bytes with
  | case1 start b0 b1 b2 b3 b4 b5 b6 rest ih =>
      rw [ih, registryChunkScale]
      have chunk := registryStep_foldl start [b0, b1, b2, b3, b4, b5, b6]
      simp only [List.length_cons, List.length_nil] at chunk
      simp only [List.foldl_cons, List.foldl_nil] at chunk ⊢
      rw [chunk]
  | case2 start rest _ => rfl

def registryDigestFast (bytes : List UInt8) : Digest :=
  ⟨registryFoldFast 17 bytes⟩

@[csimp] theorem registryDigest_eq_fast : @registryDigest = @registryDigestFast := by
  funext bytes
  simp only [registryDigest, registryDigestFast, registryFoldFast_eq]
  rfl

/-! ## Exact signed frame -/

structure SignedHeader where
  codecVersion : Nat
  /-- Canonical bytes of the plan's authority reads: (address, value) pairs. -/
  footprint : List UInt8
  /-- The last admission height at which this plan may be admitted. -/
  validUntil : Nat
  keyId : Nat
  keyEpoch : Nat
  algorithm : Nat
  domain : List UInt8
  message : List UInt8
  nullifier : Nat
  deriving DecidableEq, Repr

abbrev HeaderTuple :=
  Nat × List UInt8 × Nat × Nat × Nat × Nat × List UInt8 × List UInt8 × Nat

def headerTupleStream : StreamCodec HeaderTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product bytesStream
                (StreamCodec.product bytesStream StreamCodec.nat)))))))

def SignedHeader.toTuple (header : SignedHeader) : HeaderTuple :=
  (header.codecVersion, header.footprint, header.validUntil,
    header.keyId, header.keyEpoch, header.algorithm, header.domain,
    header.message, header.nullifier)

def SignedHeader.ofTuple : HeaderTuple -> SignedHeader
  | (version, footprint, validUntil, keyId, keyEpoch, algorithm, domain,
      message, nullifier) =>
    { codecVersion := version, footprint := footprint,
      validUntil := validUntil, keyId := keyId, keyEpoch := keyEpoch,
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

/-- The controller's view of the current authority state.  `footprint` is the
canonical encoding of the current values at the addresses the signed footprint
names, and `height` is the admission height; both are derived at admission,
never supplied by the signer. -/
structure ControllerState where
  codecVersion : Nat
  authorityRoot : Digest
  registryCommitment : Digest
  registryEpoch : Nat
  footprint : List UInt8
  height : Nat
  consumedNullifiers : List Nat
  deriving DecidableEq, Repr

abbrev StateTuple := Nat × Digest × Digest × Nat × List UInt8 × Nat × List Nat

def stateTupleStream : StreamCodec StateTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product bytesStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.list StreamCodec.nat))))))

def ControllerState.toTuple (state : ControllerState) : StateTuple :=
  (state.codecVersion, state.authorityRoot, state.registryCommitment,
    state.registryEpoch, state.footprint, state.height, state.consumedNullifiers)

def ControllerState.ofTuple : StateTuple -> ControllerState
  | (version, root, commitment, epoch, footprint, height, nullifiers) =>
    { codecVersion := version, authorityRoot := root,
      registryCommitment := commitment, registryEpoch := epoch,
      footprint := footprint, height := height,
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
  /-- A value the plan read in the authority cell has changed since it was
  signed.  The only authority-state staleness a signature can carry. -/
  | footprintStale
  /-- The admission height is past the plan's signed `validUntil`. -/
  | expired
  | wrongDomain
  | wrongMessage
  | replayedNullifier
  | unknownKey
  | wrongSubject
  | wrongKeyEpoch
  | wrongAlgorithm
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
              if ¬(registry.keys.map (fun key => key.keyId)).Nodup then
                .error .malformedRegistry
              else if state.codecVersion != stateCodecVersion then
                .error .wrongStateVersion
              else if registry.codecVersion != registryCodecVersion then
                .error .wrongRegistryVersion
              else if envelope.header.codecVersion != envelopeCodecVersion then
                .error .wrongEnvelopeVersion
              else if registry.authorityRoot != state.authorityRoot then
                .error .staleAuthority
              else if registryDigest registryBytes != state.registryCommitment then
                .error .uncommittedRegistry
              else if registry.registryEpoch != state.registryEpoch then
                .error .staleRegistry
              else if envelope.header.footprint != state.footprint then
                .error .footprintStale
              else if envelope.header.validUntil < state.height then
                .error .expired
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
                    else if registry.registryEpoch < key.activeFrom ||
                        key.activeUntil < registry.registryEpoch then
                      .error .staleKey
                    else
                      .ok
                        { state, registry, envelope, key
                          frame := envelope.frame
                          frameExact := rfl }

/-- What `prepare` decides once its three decodes succeed (`prepare_decoded`): a caller that
holds the state, the registry and the envelope as values asks this, not an encode and a decode
of each. `registryBytes` is the registry's encoding, the bytes its commitment is over. -/
def prepareDecoded {NativeError : Type}
    (expectedSubject : Nat) (expectedDomain expectedMessage : List UInt8)
    (state : ControllerState) (registry : KeyRegistryProjection) (registryBytes : List UInt8)
    (envelope : SignedEnvelope) :
    Except (Failure NativeError) Prepared :=
  if ¬(registry.keys.map (fun key => key.keyId)).Nodup then
    .error .malformedRegistry
  else if state.codecVersion != stateCodecVersion then
    .error .wrongStateVersion
  else if registry.codecVersion != registryCodecVersion then
    .error .wrongRegistryVersion
  else if envelope.header.codecVersion != envelopeCodecVersion then
    .error .wrongEnvelopeVersion
  else if registry.authorityRoot != state.authorityRoot then
    .error .staleAuthority
  else if registryDigest registryBytes != state.registryCommitment then
    .error .uncommittedRegistry
  else if registry.registryEpoch != state.registryEpoch then
    .error .staleRegistry
  else if envelope.header.footprint != state.footprint then
    .error .footprintStale
  else if envelope.header.validUntil < state.height then
    .error .expired
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
        else if registry.registryEpoch < key.activeFrom ||
            key.activeUntil < registry.registryEpoch then
          .error .staleKey
        else
          .ok
            { state, registry, envelope, key
              frame := envelope.frame
              frameExact := rfl }

/-- **`prepare` is its decodes, then `prepareDecoded`.** -/
theorem prepare_decoded {NativeError : Type}
    (expectedSubject : Nat) (expectedDomain expectedMessage : List UInt8)
    (stateBytes registryBytes envelopeBytes : List UInt8) :
    prepare (NativeError := NativeError) expectedSubject expectedDomain expectedMessage
        stateBytes registryBytes envelopeBytes =
      match stateCodec.decode stateBytes with
      | none => .error .malformedState
      | some state =>
          match registryCodec.decode registryBytes with
          | none => .error .malformedRegistry
          | some registry =>
              match envelopeCodec.decode envelopeBytes with
              | none => .error .malformedEnvelope
              | some envelope => prepareDecoded expectedSubject expectedDomain expectedMessage
                  state registry registryBytes envelope := by
  rfl

/-- `prepare` over a state and a registry it is handed as their encodings. -/
theorem prepare_encoded {NativeError : Type}
    (expectedSubject : Nat) (expectedDomain expectedMessage : List UInt8)
    (state : ControllerState) (registry : KeyRegistryProjection) (envelopeBytes : List UInt8) :
    prepare (NativeError := NativeError) expectedSubject expectedDomain expectedMessage
        (stateCodec.encode state) (registryCodec.encode registry) envelopeBytes =
      match envelopeCodec.decode envelopeBytes with
      | none => .error .malformedEnvelope
      | some envelope => prepareDecoded expectedSubject expectedDomain expectedMessage
          state registry (registryCodec.encode registry) envelope := by
  rw [prepare_decoded, stateCodec.decode_encode, registryCodec.decode_encode]

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

/-! ## Poles of `SignatureCompletion`

A verifier that never accepts completes against any custody; one that accepts
everything is refused when nothing authenticates. -/

theorem signatureCompletion_rejectAll :
    SignatureCompletion (Error := Unit) (fun _ _ _ => .ok false) (fun _ _ _ => False)
      (fun _ _ _ _ => False) :=
  ⟨⟨fun _ _ _ h => nomatch h⟩, ⟨fun _ _ _ h => h.elim⟩⟩

theorem signatureCompletion_acceptAll_refused :
    ¬ SignatureCompletion (Error := Unit) (fun _ _ _ => .ok true) (fun _ _ _ => False)
      (fun _ _ _ _ => True) :=
  fun c => c.native.sound [] [] [] rfl

#assert_axioms signatureCompletion_rejectAll signatureCompletion_acceptAll_refused

end Minidregg.Kernel.CredentialSignedEnvelopeController
