import Compiler.CredentialSignatureAdmission
import Compiler.CredentialAuthorityDomainReceiver

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.CredentialSignatureAdmission
open Minidregg.Kernel

namespace CredentialSignatureProbe

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL credential signature: {label}")

def requireSome {α : Type} (label : String) : Option α → IO α
  | some value => pure value
  | none => throw (IO.userError s!"FAIL credential signature: {label}")

def requireOk {α : Type} (label : String) : Except CredentialSignatureAdmission.Reject α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"FAIL credential signature: {label}: {repr reason}")

def rejectAs {α : Type} (label : String) (expected : CredentialSignatureAdmission.Reject)
    (result : Except CredentialSignatureAdmission.Reject α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"FAIL credential signature: {label} accepted")
  | .error actual => require s!"{label}: {repr actual}" (decide (actual = expected))

/-- This signer uses a public deterministic test seed. Production verifier
has no signing operation; only its separate example executable signs here. -/
def sign (signer : System.FilePath) (seed : Nat) (frame : List UInt8) :
    IO (List UInt8 × List UInt8) :=
  IO.FS.withTempDir fun directory => do
    let framePath := directory / "frame.bin"
    let keyPath := directory / "key.bin"
    let signaturePath := directory / "signature.bin"
    IO.FS.writeBinFile framePath frame.toByteArray
    let result ← IO.Process.output
      { cmd := signer.toString
        args := #[toString seed, framePath.toString, keyPath.toString, signaturePath.toString] }
    require "real public test signer succeeds"
      (result.exitCode == 0 && result.stdout == "" &&
        result.stderr == s!"PUBLIC TEST KEY: seed = [{seed}; 32]; anyone can reproduce this signing key.\n")
    pure ((← IO.FS.readBinFile keyPath).toList, (← IO.FS.readBinFile signaturePath).toList)

def deployment : CanonicalCellRegistry.Deployment := ⟨⟨6300⟩, 10, 11, 12⟩
def operationNullifier : Nat := 991

def key (publicKey : List UInt8) : KeyRecord where
  keyId := 7001
  keyEpoch := 2
  algorithm := CredentialSignatureAdmission.ed25519Algorithm
  subject := 7
  publicKey := publicKey
  activeFrom := 4
  activeUntil := 8
  revoked := false

def pagesFor (entries : List Entry) : IO (List Page) :=
  requireSome "source-derived routed authority pages"
    (runEdits deployment.domain [] (entries.map fun entry => ⟨none, entry⟩))

def catalogueFor (revision : Nat) (pages : List Page) : Catalogue :=
  let old : Catalogue := ⟨deployment.domain, revision, []⟩
  { CredentialAuthorityDomainReceiver.placedCatalogue old
      (CredentialAuthorityDomainReceiver.placePages old pages 2000) with revision := revision }

def source (record : KeyRecord) (revision : Nat := 5) (consumed : Bool := false) :
    IO Snapshot := do
  let pages ← pagesFor [.subjectKey record, .nullifier operationNullifier consumed]
  requireSome "complete authority assembly" (assemble (catalogueFor revision pages) pages)

/-- Load the positive authority from actual persisted lifecycle bytes. The
key is not supplied separately to the signature admission function. -/
def physicalSource (nativeStore : System.FilePath) (record : KeyRecord) : IO Snapshot :=
  IO.FS.withTempDir fun directory => do
    let pages ← pagesFor [.subjectKey record, .nullifier operationNullifier false]
    let catalogue := catalogueFor 5 pages
    let seed : DurableReceiver.Seed :=
      { absentBytes := []
        cells := (deployment.authorityAnchor.catalogueCellId,
            CredentialAuthorityDomainReceiver.catalogueBytes catalogue) ::
          (catalogue.pages.zip pages).map fun (reference, page) =>
            (reference.cellId, CredentialAuthorityDomainReceiver.shardBytes page)
        available := fun _ => 100 }
    let transport := (DurableReceiverIO.NativeConfig.mk nativeStore (directory / "store")).transport
    match ← DurableReceiverIO.bootstrap transport ResourceBirthCodec.rootBytes seed with
    | .error reason => throw (IO.userError s!"FAIL signature physical bootstrap: {reason}")
    | .ok () => pure ()
    let durable ← match ← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes with
      | .error reason => throw (IO.userError s!"FAIL signature physical reopen: {reason}")
      | .ok value => pure value
    let loaded ← requireSome "actual full authority loader"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot)
    require "committed key survives native reopen"
      (decide (loaded.snapshot.currentSigningKey ⟨record.subject⟩ = some record))
    pure loaded.snapshot

def request (snapshot : Snapshot) : Request .object where
  domain := snapshot.domain
  semantics := ⟨6400⟩
  federation := ⟨6401⟩
  subject := ⟨7⟩
  subjectKeyEpoch := 2
  target := ⟨6402⟩
  verb := .mutateObject
  argsDigest := ⟨6403⟩
  effectsDigest := ⟨6404⟩
  nonce := 123
  height := 5000
  preStateRoot := ⟨6405⟩
  policyId := ⟨6406⟩
  policyEpoch := 3
  policyRevision := 19
  cost := 27

def envelope (signer : System.FilePath) (snapshot : Snapshot) (wanted : Request .object)
    (seed : Nat := 7) : IO CredentialSignedEnvelopeController.SignedEnvelope := do
  let header ← requireOk "source-derived signing header"
    (signingHeader snapshot operationNullifier ⟨.object, wanted⟩)
  let (_, signature) ← sign signer seed (CredentialSignedEnvelopeController.headerCodec.encode header)
  pure ⟨header, signature⟩

def bytes (envelope : CredentialSignedEnvelopeController.SignedEnvelope) : List UInt8 :=
  CredentialSignedEnvelopeController.envelopeCodec.encode envelope

def run (nativeVerifier signer nativeStore : System.FilePath) : IO Unit := do
  let config : CredentialSignatureIO.NativeConfig := ⟨nativeVerifier⟩
  let (publicKey, _) ← sign signer 7 []
  let record := key publicKey
  let snapshot ← physicalSource nativeStore record
  let wanted := request snapshot
  let signed ← envelope signer snapshot wanted
  let receipt ← requireOk "real valid signature reaches existing receiving controller"
    (← verifyNative config snapshot operationNullifier wanted (bytes signed))
  require "exact native receipt request check succeeds"
    (verifySignature snapshot operationNullifier wanted receipt)
  require "receipt cannot change shared replay marker"
    (!verifySignature snapshot (operationNullifier + 1) wanted receipt)
  let changed := { wanted with effectsDigest := ⟨6407⟩ }
  require "private receipt cannot authorize a different effect"
    (!verifySignature snapshot operationNullifier changed receipt)
  rejectAs "modified expected request" (.envelope .wrongMessage)
    (← verifyNative config snapshot operationNullifier changed (bytes signed))
  let changedHeader := { signed.header with message := requestBytes ⟨.object, changed⟩ }
  rejectAs "modified canonical frame invalidates actual Ed25519 signature" (.envelope .invalidSignature)
    (← verifyNative config snapshot operationNullifier changed (bytes ⟨changedHeader, signed.signature⟩))
  let changedRevision := { wanted with policyRevision := wanted.policyRevision + 1 }
  require "native receipt binds source revision independently of grant generation"
    (!verifySignature snapshot operationNullifier changedRevision receipt)
  rejectAs "changed source revision cannot reuse an old signature" (.envelope .wrongMessage)
    (← verifyNative config snapshot operationNullifier changedRevision (bytes signed))
  let changedRevisionHeader :=
    { signed.header with message := requestBytes ⟨.object, changedRevision⟩ }
  rejectAs "reframing revision without signing fails real Ed25519" (.envelope .invalidSignature)
    (← verifyNative config snapshot operationNullifier changedRevision
      (bytes ⟨changedRevisionHeader, signed.signature⟩))
  -- Old framing is deliberately a negative fixture, never a live decoder path.
  let oldRequestFrame := "DREGG/AUTH/REQUEST".toUTF8.toList ++ [1]
  let words := TypedAuthorizationRequestCodec.requestWords (encodeRequest ⟨.object, wanted⟩)
  let oldWords := words.take 15 ++ words.drop 16
  require "old sixteen-field request has no canonical decode or revision fallback"
    ((TypedAuthorizationRequestCodec.someRequestCodec.decode
      ((StreamCodec.list StreamCodec.nat).encode oldWords)).isNone)
  let oldHeader := { signed.header with message := oldRequestFrame ++
    (StreamCodec.list StreamCodec.nat).encode oldWords }
  let (_, oldSignature) ← sign signer 7
    (CredentialSignedEnvelopeController.headerCodec.encode oldHeader)
  rejectAs "actually signed legacy request frame refuses" (.envelope .wrongMessage)
    (← verifyNative config snapshot operationNullifier wanted
      (bytes ⟨oldHeader, oldSignature⟩))
  let oldDomainHeader := { signed.header with domain :=
    "DREGG/AUTH/SIGNED-REQUEST".toUTF8.toList ++ [1] }
  let (_, oldDomainSignature) ← sign signer 7
    (CredentialSignedEnvelopeController.headerCodec.encode oldDomainHeader)
  rejectAs "actually signed legacy signature domain refuses" (.envelope .wrongDomain)
    (← verifyNative config snapshot operationNullifier wanted
      (bytes ⟨oldDomainHeader, oldDomainSignature⟩))
  let wrongSigner ← envelope signer snapshot wanted 8
  rejectAs "wrong private key" (.envelope .invalidSignature)
    (← verifyNative config snapshot operationNullifier wanted (bytes wrongSigner))
  let wrongKey := { signed with header := { signed.header with keyId := record.keyId + 1 } }
  rejectAs "wrong selected key id" (.envelope .unknownKey)
    (← verifyNative config snapshot operationNullifier wanted (bytes wrongKey))
  let wrongEpoch := { signed with header := { signed.header with keyEpoch := 3 } }
  rejectAs "wrong signed key epoch" (.envelope .wrongKeyEpoch)
    (← verifyNative config snapshot operationNullifier wanted (bytes wrongEpoch))
  rejectAs "stale request key epoch" .subjectKeyEpoch
    (← verifyNative config snapshot operationNullifier { wanted with subjectKeyEpoch := 1 } (bytes signed))
  rejectAs "request cannot cross authority domains" .wrongDomain
    (← verifyNative config snapshot operationNullifier { wanted with domain := ⟨6301⟩ } (bytes signed))
  let changedAuthority ← source { record with activeUntil := 9 }
  rejectAs "same signing key cannot substitute another complete authority snapshot" (.envelope .staleAuthority)
    (← verifyNative config changedAuthority operationNullifier (request changedAuthority) (bytes signed))
  let wrongMarker := { signed with header := { signed.header with nullifier := operationNullifier + 1 } }
  rejectAs "wire caller cannot select another replay marker" .sourceBinding
    (← verifyNative config snapshot operationNullifier wanted (bytes wrongMarker))
  let noncanonicalBytes := [1, 0, 255] ++ (bytes signed).drop 2
  require "noncanonical envelope alias reaches primitive decoder"
    ((CredentialSignedEnvelopeController.envelopeCodec.decode noncanonicalBytes).isSome)
  require "strict ingress parsing refuses the alias before replay lookup"
    ((canonicalEnvelopeCodec.decode noncanonicalBytes).isNone)
  rejectAs "noncanonical envelope refuses existing controller" (.envelope .malformedEnvelope)
    (← verifyNative config snapshot operationNullifier wanted noncanonicalBytes)
  rejectAs "trailing envelope bytes" (.envelope .malformedEnvelope)
    (← verifyNative config snapshot operationNullifier wanted ((bytes signed) ++ [0]))
  let revoked ← source { record with revoked := true }
  let revokedEnvelope ← envelope signer revoked (request revoked)
  rejectAs "committed revoked key" (.envelope .revokedKey)
    (← verifyNative config revoked operationNullifier (request revoked) (bytes revokedEnvelope))
  let rotated ← source { record with keyEpoch := 3 }
  rejectAs "old subject epoch after committed rotation" .subjectKeyEpoch
    (← verifyNative config rotated operationNullifier wanted (bytes signed))
  let replayed ← source record 5 true
  let replayEnvelope ← envelope signer replayed (request replayed)
  rejectAs "same authority nullifier already consumed" (.envelope .replayedNullifier)
    (← verifyNative config replayed operationNullifier (request replayed) (bytes replayEnvelope))
  let revisionNine ← source record 9
  let expiredEnvelope ← envelope signer revisionNine (request revisionNine)
  rejectAs "activation ends by complete catalogue revision" (.envelope .staleKey)
    (← verifyNative config revisionNine operationNullifier (request revisionNine) (bytes expiredEnvelope))
  let revisionThree ← source record 3
  let earlyEnvelope ← envelope signer revisionThree (request revisionThree)
  rejectAs "activation begins by complete catalogue revision" (.envelope .staleKey)
    (← verifyNative config revisionThree operationNullifier (request revisionThree) (bytes earlyEnvelope))
  let keylessPages ← pagesFor [.subjectKeyEpoch ⟨7⟩ 2]
  let keyless ← requireSome "keyless old authority remains representable"
    (assemble (catalogueFor 5 keylessPages) keylessPages)
  rejectAs "epoch without committed key is never signature authority" .missingCurrentKey
    (← verifyNative config keyless operationNullifier (request keyless) (bytes signed))
  let shortKey ← source { record with publicKey := publicKey.drop 1 }
  rejectAs "committed public key must be exactly32 bytes" .publicKeyLength
    (← verifyNative config shortKey operationNullifier (request shortKey) (bytes signed))
  let otherAlgorithm ← source { record with algorithm := 99 }
  rejectAs "unknown committed algorithm cannot reach Ed25519" .unsupportedAlgorithm
    (← verifyNative config otherAlgorithm operationNullifier (request otherAlgorithm) (bytes signed))
  let empty ← requireSome "empty catalogue is representable"
    (assemble (catalogueFor 5 []) [])
  rejectAs "absent epoch0 is not signing authority" .missingCurrentKey
    (← verifyNative config empty operationNullifier
      { request empty with subjectKeyEpoch := 0 } (bytes signed))
  IO.println "PASS credential signature: real Ed25519 through existing Lean controller; committed key from native SQLite/full authority reopen; exact seventeen-field request including independently signed source revision, legacy-frame refusal, key/epoch, canonical frame, revocation, shared nullifier and catalogue-revision activation; no standalone signature-state commit"

end CredentialSignatureProbe

def main (arguments : List String) : IO Unit :=
  match arguments with
  | [verifier, signer, store] => CredentialSignatureProbe.run verifier signer store
  | _ => throw (IO.userError "usage: lean --run scripts/probe-credential-signature.lean VERIFIER TEST-SIGNER SQLITE-STORE")
