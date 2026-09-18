/-
# Compiler.CredentialSignatureAdmission — native signatures from one authority snapshot

The complete authority snapshot selects the current committed key. Lean
derives the singleton key projection, authority root, catalogue revision,
canonical sixteen-field request and shared operation nullifier. The existing
SignedEnvelope controller checks canonical framing, key identity/epoch,
revocation, activation and replay before the native verifier sees bytes.

`CheckedSignature` has a private constructor and no wire decoder. Its only
producer calls the configured Ed25519 verifier and the existing controller's
finish step. Pure policy/capability admission can compare this receipt to the
exact request; a caller cannot submit an arbitrary positive verification bit.

Verification does not persist the controller's standalone nextStateBytes.
The enclosing source-owned authority effect consumes the expected nullifier
ONCE with the whole hyperedge, under the same old authority snapshot guards.
All its incidences may bind that one marker. Native implementation/transport
and cryptographic custody assumptions remain explicit; the receipt is not a
Lean proof of Ed25519 or physical commit.
-/
import Compiler.CredentialSignatureIO
import Compiler.CredentialAuthorityDomain
import Compiler.DeclaredHyperedgeArtifact
import Compiler.ResourceBirthCodec

namespace Minidregg.Compiler.CredentialSignatureAdmission

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.CredentialAuthorityDomain

open Minidregg.Kernel

set_option autoImplicit false

/-- Source-pinned algorithm code for this receiving adapter. -/
def ed25519Algorithm : Nat := 1

def signatureDomain : List UInt8 := "DREGG/AUTH/SIGNED-REQUEST".toUTF8.toList ++ [1]
def requestFrame : List UInt8 := "DREGG/AUTH/REQUEST".toUTF8.toList ++ [1]

/-- Canonical ingress uses the existing signed-envelope parser and encoding.
The legacy stream remains useful inside a source-owned ordered bundle, whose
whole-message decoder must likewise enforce exact re-encoding. Parsing a
canonical envelope alone does not authenticate it or mint a receipt. -/
def canonicalEnvelopeCodec : LawfulCodec CredentialSignedEnvelopeController.SignedEnvelope :=
  ResourceBirthCodec.strictCodec CredentialSignedEnvelopeController.envelopeCodec

theorem canonicalEnvelopeCodec_accepted_bytes
    {bytes : List UInt8} {envelope : CredentialSignedEnvelopeController.SignedEnvelope}
    (accepted : canonicalEnvelopeCodec.decode bytes = some envelope) :
    canonicalEnvelopeCodec.encode envelope = bytes :=
  ResourceBirthCodec.strictCodec_canonical CredentialSignedEnvelopeController.envelopeCodec accepted

/-- Reuses the existing complete dependent request projection and field order.
No caller supplies a second target, effect digest, epoch or cost to sign. -/
def requestBytes (request : SomeRequest) : List UInt8 :=
  requestFrame ++ (StreamCodec.list StreamCodec.nat).encode
    (DeclaredHyperedgeArtifact.requestWords (encodeRequest request))

theorem requestWords_injective : Function.Injective DeclaredHyperedgeArtifact.requestWords := by
  intro left right equal
  cases left
  cases right
  simpa [DeclaredHyperedgeArtifact.requestWords] using equal

theorem requestBytes_injective : Function.Injective requestBytes := by
  intro left right equal
  unfold requestBytes at equal
  have words : DeclaredHyperedgeArtifact.requestWords (encodeRequest left) =
      DeclaredHyperedgeArtifact.requestWords (encodeRequest right) := by
    let codec := (StreamCodec.list StreamCodec.nat).toLawful
    have payload : codec.encode (DeclaredHyperedgeArtifact.requestWords (encodeRequest left)) =
        codec.encode (DeclaredHyperedgeArtifact.requestWords (encodeRequest right)) :=
      List.append_cancel_left equal
    have decoded := congrArg codec.decode payload
    rw [codec.decode_encode, codec.decode_encode] at decoded
    exact Option.some.inj decoded
  have decoded := congrArg decodeRequest (requestWords_injective words)
  rw [decodeRequest_encodeRequest, decodeRequest_encodeRequest] at decoded
  exact Option.some.inj decoded

inductive Reject where
  | wrongDomain
  | missingCurrentKey
  | subjectKeyEpoch
  | unsupportedAlgorithm
  | publicKeyLength
  | envelope (reason : CredentialSignedEnvelopeController.Failure CredentialSignatureIO.Error)
  | sourceBinding
  deriving DecidableEq, Repr

/-- Selection is a read of the canonical authority schema, never a host key
map. Missing epoch or record refuses, including an absent "epoch zero". -/
structure Selected (snapshot : Snapshot) (request : SomeRequest) where
  key : KeyRecord
  selected : CredentialAuthorityState.currentSigningKey snapshot.logical
    request.2.subject = some key
  epochCurrent : request.2.subjectKeyEpoch = snapshot.authState.subjectKeyEpoch request.2.subject
  epochExact : key.keyEpoch = request.2.subjectKeyEpoch
  domainExact : request.2.domain = snapshot.domain
  algorithmExact : key.algorithm = ed25519Algorithm
  keyLength : key.publicKey.length = 32

def select (snapshot : Snapshot) (request : SomeRequest) : Except Reject (Selected snapshot request) :=
  if domainExact : request.2.domain = snapshot.domain then
    match selected : CredentialAuthorityState.currentSigningKey snapshot.logical request.2.subject with
    | none => .error .missingCurrentKey
    | some key =>
        if epochCurrent : request.2.subjectKeyEpoch =
            snapshot.authState.subjectKeyEpoch request.2.subject then
          if epochExact : key.keyEpoch = request.2.subjectKeyEpoch then
            if algorithmExact : key.algorithm = ed25519Algorithm then
              if keyLength : key.publicKey.length = 32 then
                .ok ⟨key, selected, epochCurrent, epochExact, domainExact, algorithmExact, keyLength⟩
              else .error .publicKeyLength
            else .error .unsupportedAlgorithm
          else .error .subjectKeyEpoch
        else .error .subjectKeyEpoch
  else .error .wrongDomain

/-- The activation epoch is the complete authority catalogue revision. Every
lowered authority update can advance it; it is not height or subject epoch. -/
def keyRegistry (snapshot : Snapshot) (key : KeyRecord) : CredentialSignedEnvelopeController.KeyRegistryProjection where
  codecVersion := CredentialSignedEnvelopeController.registryCodecVersion
  authorityRoot := snapshot.cell.root
  registryEpoch := snapshot.catalogue.revision
  keys := [key]

def controllerState (snapshot : Snapshot) (key : KeyRecord) (nullifier : Nat) :
    CredentialSignedEnvelopeController.ControllerState where
  codecVersion := CredentialSignedEnvelopeController.stateCodecVersion
  authorityRoot := snapshot.cell.root
  registryCommitment := CredentialSignedEnvelopeController.registryDigest
    (CredentialSignedEnvelopeController.registryCodec.encode (keyRegistry snapshot key))
  registryEpoch := snapshot.catalogue.revision
  consumedNullifiers :=
    if (show Option Bool from snapshot.logical.fields (.nullifier nullifier)).getD false then
      [nullifier]
    else []

def header (snapshot : Snapshot) (key : KeyRecord) (nullifier : Nat)
    (request : SomeRequest) : CredentialSignedEnvelopeController.SignedHeader where
  codecVersion := CredentialSignedEnvelopeController.envelopeCodecVersion
  authorityRoot := snapshot.cell.root
  registryCommitment := (controllerState snapshot key nullifier).registryCommitment
  keyId := key.keyId
  keyEpoch := key.keyEpoch
  algorithm := ed25519Algorithm
  domain := signatureDomain
  message := requestBytes request
  nullifier := nullifier

/-- Client preparation exposes only the exact source-derived bytes to sign;
it does not construct a checked signature or choose an independent key. -/
def signingHeader (snapshot : Snapshot) (nullifier : Nat) (request : SomeRequest) :
    Except Reject CredentialSignedEnvelopeController.SignedHeader := do
  let selected ← select snapshot request
  .ok (header snapshot selected.key nullifier request)

structure Prepared (snapshot : Snapshot) (nullifier : Nat) (request : SomeRequest) where
  source : Selected snapshot request
  controller : CredentialSignedEnvelopeController.Prepared
  keyExact : controller.key = source.key
  headerExact : controller.envelope.header = header snapshot source.key nullifier request

/-- The parser and all envelope admission decisions remain in the existing
controller. The additional equality pins its result to this source snapshot
and the enclosing operation's exact shared nullifier. -/
def prepare (snapshot : Snapshot) (nullifier : Nat) (request : SomeRequest)
    (envelopeBytes : List UInt8) : Except Reject (Prepared snapshot nullifier request) := do
  let source ← select snapshot request
  match CredentialSignedEnvelopeController.prepare (NativeError := CredentialSignatureIO.Error) request.2.subject.value
      signatureDomain (requestBytes request)
      (CredentialSignedEnvelopeController.stateCodec.encode (controllerState snapshot source.key nullifier))
      (CredentialSignedEnvelopeController.registryCodec.encode (keyRegistry snapshot source.key)) envelopeBytes with
  | .error reason => .error (.envelope reason)
  | .ok controller =>
      if keyExact : controller.key = source.key then
        if headerExact : controller.envelope.header = header snapshot source.key nullifier request then
          .ok ⟨source, controller, keyExact, headerExact⟩
        else .error .sourceBinding
      else .error .sourceBinding

/-- The constructor is module-private. There is no positive-result decoder,
test receipt constructor, arbitrary verifier callback or pure mint function. -/
structure CheckedSignature (snapshot : Snapshot) where
  private mk ::
  verifier : CredentialSignatureIO.NativeConfig
  request : SomeRequest
  nullifier : Nat
  envelopeBytes : List UInt8
  prepared : Prepared snapshot nullifier request
  preparedFrom : prepare snapshot nullifier request envelopeBytes = .ok prepared
  admission : CredentialSignedEnvelopeController.Admission
  admitted : CredentialSignedEnvelopeController.finish prepared.controller (Except.ok true : Except CredentialSignatureIO.Error Bool) =
    .ok admission

def verifyNative (config : CredentialSignatureIO.NativeConfig) (snapshot : Snapshot) (nullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (envelopeBytes : List UInt8) :
    IO (Except Reject (CheckedSignature snapshot)) := do
  match preparation : prepare snapshot nullifier ⟨kind, request⟩ envelopeBytes with
  | .error reason => return .error reason
  | .ok prepared =>
      match ← CredentialSignatureIO.verify config prepared.controller.key.publicKey prepared.controller.frame
          prepared.controller.envelope.signature with
      | .error error => return .error (.envelope (.nativeVerify error))
      | .ok false => return .error (.envelope .invalidSignature)
      | .ok true =>
          match admitted : CredentialSignedEnvelopeController.finish prepared.controller
              (Except.ok true : Except CredentialSignatureIO.Error Bool) with
          | .error reason => return .error (.envelope reason)
          | .ok admission =>
              return .ok ⟨config, ⟨kind, request⟩, nullifier, envelopeBytes,
                prepared, preparation, admission, admitted⟩

/-- The pure portal can use a native receipt only for its exact complete
request and the same operation marker. Snapshot selection is a type index. -/
def verifySignature (snapshot : Snapshot) (expectedNullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (receipt : CheckedSignature snapshot) : Bool :=
  decide (encodeRequest receipt.request = encodeRequest ⟨kind, request⟩ ∧
    receipt.nullifier = expectedNullifier)

theorem verified_request_exact (snapshot : Snapshot) (expectedNullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (receipt : CheckedSignature snapshot)
    (verified : verifySignature snapshot expectedNullifier request receipt = true) :
    receipt.request = ⟨kind, request⟩ ∧ receipt.nullifier = expectedNullifier := by
  have binding : encodeRequest receipt.request = encodeRequest ⟨kind, request⟩ ∧
      receipt.nullifier = expectedNullifier := of_decide_eq_true verified
  constructor
  · have decoded := congrArg decodeRequest binding.1
    rw [decodeRequest_encodeRequest, decodeRequest_encodeRequest] at decoded
    exact Option.some.inj decoded
  · exact binding.2

theorem checked_key_from_same_snapshot (snapshot : Snapshot) (receipt : CheckedSignature snapshot) :
    CredentialAuthorityState.currentSigningKey snapshot.logical receipt.request.2.subject =
      some receipt.prepared.controller.key := by
  rw [receipt.prepared.keyExact]
  exact receipt.prepared.source.selected

theorem checked_frame_exact (snapshot : Snapshot) (receipt : CheckedSignature snapshot) :
    receipt.prepared.controller.frame = CredentialSignedEnvelopeController.headerCodec.encode
      (header snapshot receipt.prepared.source.key receipt.nullifier receipt.request) := by
  rw [receipt.prepared.controller.frameExact]
  change CredentialSignedEnvelopeController.headerCodec.encode receipt.prepared.controller.envelope.header = _
  rw [receipt.prepared.headerExact]

/-- Explicit IO-to-verifier refinement obligation for ACTUAL execution,
including the pinned executable and exact process/filesystem byte transport.
`Returned` denotes that physical execution relation; a structurally available
receipt alone is not its proof. No relation or instance is asserted here.
The existing controller separately requires cryptographic refinement and
EUF-CMA/key-custody assumptions. -/
structure NativeIORefinement
    (config : CredentialSignatureIO.NativeConfig)
    (Returned : CredentialSignatureIO.NativeConfig → List UInt8 → List UInt8 → List UInt8 →
      Except CredentialSignatureIO.Error Bool → Prop)
    (verify : CredentialSignedEnvelopeController.OpaqueVerifier CredentialSignatureIO.Error) : Prop where
  exactResult : ∀ publicKey frame signature result,
    Returned config publicKey frame signature result → verify publicKey frame signature = result

theorem issued_of_checked
    {config : CredentialSignatureIO.NativeConfig}
    {Returned : CredentialSignatureIO.NativeConfig → List UInt8 → List UInt8 → List UInt8 →
      Except CredentialSignatureIO.Error Bool → Prop}
    {verify : CredentialSignedEnvelopeController.OpaqueVerifier CredentialSignatureIO.Error}
    {Authenticates : List UInt8 → List UInt8 → List UInt8 → Prop}
    {SignerIssued : Nat → Nat → List UInt8 → List UInt8 → Prop}
    (ioRefinement : NativeIORefinement config Returned verify)
    (completion : CredentialSignedEnvelopeController.SignatureCompletion
      verify Authenticates SignerIssued)
    (snapshot : Snapshot) (receipt : CheckedSignature snapshot)
    (observed : Returned config receipt.prepared.controller.key.publicKey
      receipt.prepared.controller.frame receipt.prepared.controller.envelope.signature (.ok true)) :
    SignerIssued receipt.prepared.controller.key.keyId receipt.prepared.controller.key.keyEpoch
      receipt.prepared.controller.frame receipt.prepared.controller.envelope.signature :=
  completion.issued_of_verified receipt.prepared.controller
    (ioRefinement.exactResult _ _ _ _ observed)

end Minidregg.Compiler.CredentialSignatureAdmission
