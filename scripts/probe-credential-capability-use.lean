/-
Actual native capability use through the existing policy-install receiver.
The initial authority fixture is persisted and reopened through the full
catalogue/shard loader. Test seeds are public; no private checked receipt is
fabricated. Success is an AcceptedCellEffect, not a claim of durable commit.
-/
import Kernel.PolicyInstallController
import Compiler.CredentialAuthorityDomainReceiver

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Kernel

namespace CredentialCapabilityUseProbe

abbrev Snapshot := CredentialAuthorityDomain.Snapshot

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL capability use: {label}")

def requireSome {α : Type} (label : String) : Option α → IO α
  | some value => pure value
  | none => throw (IO.userError s!"FAIL capability use: {label}")

def requireOk {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"FAIL capability use: {label}: {repr reason}")

def refused {α : Type} (label : String) (reason : PolicyInstallController.Reject)
    (result : Except PolicyInstallController.Reject α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"FAIL capability use: {label} accepted")
  | .error actual => require s!"{label}: {repr actual}" (decide (actual = reason))

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
    require "actual public-test-key signer"
      (result.exitCode == 0 && result.stdout == "" &&
        result.stderr == s!"PUBLIC TEST KEY: seed = [{seed}; 32]; anyone can reproduce this signing key.\n")
    pure ((← IO.FS.readBinFile keyPath).toList, (← IO.FS.readBinFile signaturePath).toList)

instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- The actual projected headers and address bytes must embed distinctly.
The tiny ZMod13 compiler model cannot represent this receiving fixture. -/
def profile : CanonicalRuntimeProfile.Profile (ZMod 65537) :=
  .source ⟨⟨5⟩, 100000, 10000⟩ ⟨65537⟩ 65537 inferInstance 15
    (PredOrder.noWrap_zmod (by decide))

def deployment : CanonicalCellRegistry.Deployment := ⟨⟨7300⟩, 10, 11, 12⟩
def policyId : PolicyId := ⟨600⟩
def codeId : CapabilityId := ⟨42⟩
def controlId : CapabilityId := ⟨43⟩

def key (publicKey : List UInt8) : KeyRecord where
  keyId := 7001
  keyEpoch := 2
  algorithm := CredentialSignatureAdmission.ed25519Algorithm
  subject := 7
  publicKey := publicKey
  activeFrom := 0
  activeUntil := 100
  revoked := false

def oldPolicy : PolicyRecord where
  policyId := policyId
  version := 1
  domain := deployment.domain
  semantics := profile.semantics
  previous := none
  predicate := .eq "policy/version" 2

def newPolicy : PolicyRecord where
  policyId := policyId
  version := 2
  domain := deployment.domain
  semantics := profile.semantics
  previous := some (policyRecordDigest oldPolicy)
  predicate := .eq "policy/version" 3

def store : CanonicalPolicyRegistry.PayloadStore where
  fetch := fun address =>
    if address = policyRecordDigest oldPolicy then some (policyRecordCodec.encode oldPolicy)
    else none

def capability (kind : ResourceKind) (verb : Verb kind) (identifier : CapabilityId) :
    Capability kind where
  id := identifier
  root := identifier
  parent := none
  issuer := ⟨5⟩
  holder := .subject ⟨7⟩
  scope := ⟨{⟨policyId.value⟩}, {verb}, 100000⟩
  notBefore := 0
  notAfter := 10000
  issuerEpoch := 2
  policyId := policyId
  policyEpoch := 1
  ancestors := ∅
  channels := ∅

def codeCapability : Capability .program := capability .program .installProgram codeId
def controlCapability : Capability .program := capability .program .installPolicy controlId
def rootStored (cap : Capability .program) : StoredCapability .program := ⟨cap, []⟩

def entries (record : KeyRecord) (control : StoredCapability .program)
    (issuerEpoch : Nat := 2) (revoked : Bool := false) : List Entry :=
  [.subjectKey record, .issuerEpoch ⟨5⟩ issuerEpoch,
   .policy policyId 1 1 (policyRecordDigest oldPolicy),
   .capability .program (rootStored codeCapability), .capability .program control,
   .revocation (.capability controlId) revoked]

def pagesFor (entries : List Entry) : IO (List Page) :=
  requireSome "canonical routed pages"
    (runEdits deployment.domain [] (entries.map fun entry => ⟨none, entry⟩))

def catalogueFor (pages : List Page) : Catalogue :=
  let empty : Catalogue := ⟨deployment.domain, 5, []⟩
  CredentialAuthorityDomainReceiver.placedCatalogue empty
    (CredentialAuthorityDomainReceiver.placePages empty pages 2000)

def source (entries : List Entry) : IO Snapshot := do
  let pages ← pagesFor entries
  requireSome "complete source assembly" (assemble (catalogueFor pages) pages)

def physicalSource (nativeStore : System.FilePath) (entries : List Entry) : IO Snapshot :=
  IO.FS.withTempDir fun directory => do
    let pages ← pagesFor entries
    let catalogue := catalogueFor pages
    let seed : DurableReceiver.Seed :=
      { absentBytes := []
        cells := (deployment.authorityAnchor.catalogueCellId,
            CredentialAuthorityDomainReceiver.catalogueBytes catalogue) ::
          (catalogue.pages.zip pages).map fun (reference, page) =>
            (reference.cellId, CredentialAuthorityDomainReceiver.shardBytes page)
        available := fun _ => 100 }
    let transport := (DurableReceiverIO.NativeConfig.mk nativeStore (directory / "store")).transport
    match ← DurableReceiverIO.bootstrap transport ResourceBirthCodec.rootBytes seed with
    | .error reason => throw (IO.userError s!"FAIL capability bootstrap: {reason}")
    | .ok () => pure ()
    let durable ← match ← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes with
      | .error reason => throw (IO.userError s!"FAIL capability reopen: {reason}")
      | .ok value => pure value
    let loaded ← requireSome "full canonical authority loader"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot)
    pure loaded.snapshot

def context (snapshot : Snapshot) : PolicyInstallController.RequestContext :=
  ⟨⟨9⟩, ⟨7⟩, snapshot.authState.subjectKeyEpoch ⟨7⟩, 10,
    snapshot.authState.policyEpoch policyId, snapshot.authState.policyRevision policyId⟩

def declaration (snapshot : Snapshot) : PolicyInstallController.Declaration :=
  ⟨snapshot.cell.root, some ⟨1, policyRecordDigest oldPolicy⟩, 991, newPolicy⟩

def prepare (snapshot : Snapshot) : IO (PolicyInstallController.Prepared profile snapshot (context snapshot)) :=
  requireOk "source-derived policy replacement candidate"
    (PolicyInstallController.prepare profile snapshot (context snapshot)
      (PolicyInstallController.encodeDeclaration (declaration snapshot)))

def envelope (signer : System.FilePath) {snapshot : Snapshot}
    (prepared : PolicyInstallController.Prepared profile snapshot (context snapshot)) (seed : Nat := 7) :
    IO (List UInt8) := do
  let wanted := PolicyInstallController.request profile snapshot (context snapshot) prepared.declaration
  let nullifier := (PolicyInstallController.requestDigest profile snapshot (context snapshot) prepared.declaration).value
  let header ← requireOk "exact request signing header"
    (CredentialSignatureAdmission.signingHeader snapshot nullifier ⟨.program, wanted⟩)
  let (_, signature) ← sign signer seed (CredentialSignedEnvelopeController.headerCodec.encode header)
  pure (CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩)

def run (nativeVerifier signer nativeStore : System.FilePath) : IO Unit := do
  let native : CredentialSignatureIO.NativeConfig := ⟨nativeVerifier⟩
  let (publicKey, _) ← sign signer 7 []
  let record := key publicKey
  let snapshot ← physicalSource nativeStore (entries record (rootStored controlCapability))
  let prepared ← prepare snapshot
  let signed ← envelope signer prepared
  let accepted ← requireOk "actual policy-control capability accepted"
    (← prepared.admitNative store native controlId signed)
  require "accepted evidence retains actual capability mode"
    (decide (accepted.authorization.evidence.capabilityValue =
      some (controlCapability, storedCapabilityDigest snapshot (rootStored controlCapability))))
  let postGeneration : Option Nat := accepted.prepared.post.logical.fields (.policyEpoch policyId)
  require "source replacement preserves the exact grant generation" (postGeneration == some 1)
  require "accepted source patch installs the requested policy head"
    (decide (CredentialAuthorityDomain.headAt accepted.prepared.post.logical policyId =
      some ⟨2, policyRecordDigest newPolicy⟩))
  refused "ordinary program-code edit cannot replace policy" .capability
    (← prepared.admitNative store native codeId signed)
  let changedNonce ← requireOk "independently prepared changed nonce"
    (PolicyInstallController.prepare profile snapshot (context snapshot)
      (PolicyInstallController.encodeDeclaration
        { declaration snapshot with nonce := (declaration snapshot).nonce + 1 }))
  refused "a checked source request cannot be relabeled with another nonce"
    (.nativeSignature (.envelope .wrongMessage))
    (← changedNonce.admitNative store native controlId signed)
  let copied ← envelope signer prepared 8
  refused "copying public capability and signing with another key"
    (.nativeSignature (.envelope .invalidSignature))
    (← prepared.admitNative store native controlId copied)
  let digest := storedCapabilityDigest snapshot (rootStored controlCapability)
  require "altered capability head refuses even with correct stored digest"
    (!capabilityCheck snapshot { controlCapability with notAfter := 10001 } digest)
  require "typed object role cannot stand in for program control"
    (!capabilityCheck snapshot (capability .object .mutateObject controlId) digest)
  require "membership at another authority root refuses"
    (!(sourcePortal snapshot 0).verifyMembership ⟨snapshot.cell.root.value + 1⟩ digest
      (.capability .program controlId))
  require "policy-role opening cannot substitute for this capability opening"
    (!(sourcePortal snapshot 0).verifyMembership snapshot.cell.root digest (.policy policyId 1))
  require "capability-role opening cannot substitute for this policy opening"
    (!(sourcePortal snapshot 0).verifyMembership snapshot.cell.root (policyRecordDigest oldPolicy)
      (.capability .program controlId))
  let revoked ← source (entries record (rootStored controlCapability) 2 true)
  let revokedPrepared ← prepare revoked
  refused "actual stored capability revocation" .capability
    (← revokedPrepared.admitNative store native controlId (← envelope signer revokedPrepared))
  let staleIssuer ← source (entries record (rootStored controlCapability) 3)
  let stalePrepared ← prepare staleIssuer
  refused "actual current issuer epoch supersedes stored grant" .capability
    (← stalePrepared.admitNative store native controlId (← envelope signer stalePrepared))
  let stalePolicy ← source (entries record (rootStored { controlCapability with policyEpoch := 0 }))
  let policyPrepared ← prepare stalePolicy
  refused "stored capability policy epoch is current" .capability
    (← policyPrepared.admitNative store native controlId (← envelope signer policyPrepared))
  let malformed ← source (entries record ⟨controlCapability, [⟨codeCapability, .strict⟩]⟩)
  let malformedPrepared ← prepare malformed
  refused "a stored ancestry hash is insufficient without valid lineage" .capability
    (← malformedPrepared.admitNative store native controlId (← envelope signer malformedPrepared))
  IO.println "PASS capability use: canonical persisted authority + native Ed25519 + exact source policy-install AcceptedCellEffect; explicit policy control succeeds, code-only/altered/wrong-kind/copied/revoked/stale/invalid-lineage authority refuses; no durable commit claimed"

end CredentialCapabilityUseProbe

def main (arguments : List String) : IO Unit :=
  match arguments with
  | [verifier, signer, store] => CredentialCapabilityUseProbe.run verifier signer store
  | _ => throw (IO.userError "usage: lean --run scripts/probe-credential-capability-use.lean VERIFIER TEST-SIGNER SQLITE-STORE")
