/-
Actual policy-source replacement through native signatures, the capability-only
installer, deterministic physical lowering and the SQLite receiving loop.
Fixtures use public test keys. No accepted token, signature verdict, source map
or authority snapshot is fabricated at the admission boundary.

The same stored ordinary owner and policy-control grants survive successive
source revisions. Later use is checked against the newly installed law; grants
and signatures are never reissued or silently refreshed.
-/
import Kernel.PolicyInstallReceiver
import Kernel.DeclaredResourceController

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Kernel

namespace PolicyInstallReceiverProbe

def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL policy install receiver: {label}")
  IO.println s!"PASS policy install receiver: {label}"

def requireSome {α : Type} (label : String) : Option α → IO α
  | some value => pure value
  | none => throw (IO.userError s!"FAIL policy install receiver: {label}")

def requireOk {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"FAIL policy install receiver: {label}: {repr reason}")

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
    require "public-test-key signer executed"
      (result.exitCode == 0 && result.stdout == "" &&
        result.stderr == s!"PUBLIC TEST KEY: seed = [{seed}; 32]; anyone can reproduce this signing key.\n")
    pure ((← IO.FS.readBinFile keyPath).toList, (← IO.FS.readBinFile signaturePath).toList)

instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- These are executable probe parameters, not a production field selection. -/
def profile : CanonicalRuntimeProfile.Profile (ZMod 65537) :=
  .source ⟨⟨5⟩, 100000, 10000⟩ ⟨65537⟩ 65537 inferInstance 15
    (PredOrder.noWrap_zmod (by decide))

def deployment : CanonicalCellRegistry.Deployment := ⟨⟨7301⟩, 10, 11, 12⟩
def policyId : PolicyId := ⟨600⟩
def controlId : CapabilityId := ⟨43⟩
def codeId : CapabilityId := ⟨42⟩
def ownerId : CapabilityId := ⟨44⟩
def federation : FederationId := ⟨9⟩
def height : Height := 10

def key (publicKey : List UInt8) : KeyRecord where
  keyId := 7001
  keyEpoch := 2
  algorithm := CredentialSignatureAdmission.ed25519Algorithm
  subject := 7
  publicKey := publicKey
  activeFrom := 0
  activeUntil := 100
  revoked := false

def oldPolicy (denies : Bool := false) : PolicyRecord where
  policyId := policyId
  version := 1
  domain := deployment.domain
  semantics := profile.semantics
  previous := none
  predicate := .all [.eq "policy/version" (if denies then 99 else 2),
    .eq "request/subject" 7, .monotone "policy/version"]

def newPolicy (denies : Bool := false) : PolicyRecord where
  policyId := policyId
  version := 2
  domain := deployment.domain
  semantics := profile.semantics
  previous := some (PolicyRecordCodec.digest (oldPolicy denies))
  predicate := .any
    [.all [.eq "request/verb" (Int.ofNat (CredentialAuthorityEntryCodec.verbTag Verb.installPolicy)), .eq "policy/version" 3],
     .all [.eq "request/verb" (Int.ofNat (CredentialAuthorityEntryCodec.verbTag Verb.mutateObject)), .eq "request/nonce" 1001]]

def thirdPolicy : PolicyRecord where
  policyId := policyId
  version := 3
  domain := deployment.domain
  semantics := profile.semantics
  previous := some (PolicyRecordCodec.digest newPolicy)
  predicate := .all [.eq "request/subject" 7, .eq "request/verb" (Int.ofNat (CredentialAuthorityEntryCodec.verbTag Verb.mutateObject))]

def capability (identifier : CapabilityId) (verb : Verb .program) : Capability .program where
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

def ownerCapability : Capability .object where
  id := ownerId
  root := ownerId
  parent := none
  issuer := ⟨5⟩
  holder := .subject ⟨7⟩
  scope := ⟨{⟨policyId.value⟩}, {.mutateObject}, 100000⟩
  notBefore := 0
  notAfter := 10000
  issuerEpoch := 2
  policyId := policyId
  policyEpoch := 1
  ancestors := ∅
  channels := ∅

def objectCell : CellRegistry.PackedCell CanonicalCellRegistry.registry :=
  ⟨.declaredObject, CellState.materialize DeclaredEffectPageMaterializer.materializer
    (DeclaredEffectPageMaterializer.stateOfOption (some
      ⟨deployment.domain, policyId.value % DeclaredEffectPageMaterializer.shardCount,
        some ⟨.objectField ⟨policyId.value⟩ ⟨1⟩, 0⟩, none, none, none⟩))⟩

def entries (publicKey : List UInt8) (denies : Bool) : List Entry :=
  [.subjectKey (key publicKey), .issuerEpoch ⟨5⟩ 2,
    .policy policyId 1 1 (PolicyRecordCodec.digest (oldPolicy denies)),
    .capability .program ⟨capability codeId .installProgram, []⟩,
    .capability .program ⟨capability controlId .installPolicy, []⟩,
    .capability .object ⟨ownerCapability, []⟩,
    .revocation (.capability controlId) false]

inductive SourceFixture where
  | fresh | occupiedSuccessor | retiredSuccessor | missingOld

def seed (publicKey : List UInt8) (fixture : SourceFixture := .fresh) (denies : Bool := false) :
    IO DurableReceiver.Seed := do
  let pages ← requireSome "routed authority pages"
    (runEdits deployment.domain [] ((entries publicKey denies).map fun entry => ⟨none, entry⟩))
  let empty : Catalogue := ⟨deployment.domain, 5, []⟩
  let catalogue := CredentialAuthorityDomainReceiver.placedCatalogue empty
    (CredentialAuthorityDomainReceiver.placePages empty pages 2000)
  let oldSource := CanonicalCellRegistry.policySourceCreate deployment.domain (oldPolicy denies)
  let successor := CanonicalCellRegistry.policySourceCreate deployment.domain (newPolicy denies)
  let sourceRows := match fixture with
    | .missingOld => []
    | _ => [(⟨oldSource.cellId⟩,
        ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry (.live oldSource.cell))]
  let extraRows := match fixture with
    | .occupiedSuccessor => [(⟨successor.cellId⟩,
        ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry (.live successor.cell))]
    | .retiredSuccessor => [(⟨successor.cellId⟩,
        ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry .retired)]
    | _ => []
  pure
    { absentBytes := []
      cells := (deployment.authorityAnchor.catalogueCellId,
          CredentialAuthorityDomainReceiver.catalogueBytes catalogue) ::
        ((catalogue.pages.zip pages).map fun (reference, page) =>
          (reference.cellId, CredentialAuthorityDomainReceiver.shardBytes page)) ++ sourceRows ++ extraRows ++
          [(⟨policyId.value⟩, ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry (.live objectCell))]
      available := fun _ => 10000000 }

def bootstrap (nativeStore directory : System.FilePath) (publicKey : List UInt8)
    (fixture : SourceFixture := .fresh) (denies : Bool := false) : IO DurableReceiverIO.NativeConfig := do
  let config : DurableReceiverIO.NativeConfig := ⟨nativeStore, directory / "store"⟩
  requireOk "actual SQLite bootstrap"
    (← DurableReceiverIO.bootstrap config.transport ResourceBirthCodec.rootBytes (← seed publicKey fixture denies))
  pure config

def load (config : DurableReceiverIO.NativeConfig) : IO PolicyInstallReceiver.Durable := do
  requireOk "actual SQLite reopen" (← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes)

def declaration (snapshot : CredentialAuthorityDomain.Snapshot) (denies : Bool := false) :
    PolicyInstallController.Declaration :=
  ⟨snapshot.cell.root, snapshot.currentHead policyId, 991, newPolicy denies⟩

def signedIngress (signer : System.FilePath) (durable : PolicyInstallReceiver.Durable)
    (capabilityId : CapabilityId := controlId) (testSeed : Nat := 7) (denies : Bool := false)
    (successor : Option PolicyRecord := none) (nonce : Nat := 991) :
    IO (List UInt8) := do
  let authority ← requireSome "complete same-snapshot authority"
    (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot)
  let snapshot := authority.snapshot
  let command := { declaration snapshot denies with source := successor.getD (newPolicy denies), nonce := nonce }
  let context : PolicyInstallController.RequestContext :=
    ⟨federation, ⟨7⟩, 2, height, snapshot.authState.policyEpoch policyId, snapshot.authState.policyRevision policyId⟩
  let wanted := PolicyInstallController.request profile snapshot context command
  let marker := (PolicyInstallController.requestDigest profile snapshot context command).value
  let header ← requireOk "source-bound native signing header"
    (CredentialSignatureAdmission.signingHeader snapshot marker ⟨.program, wanted⟩)
  let (_, signature) ← sign signer testSeed (CredentialSignedEnvelopeController.headerCodec.encode header)
  pure (PolicyInstallReceiver.ingressCodec.encode
    { subject := ⟨7⟩
      controlCapability := capabilityId
      declarationBytes := PolicyInstallController.encodeDeclaration command
      envelopeBytes := CredentialSignatureAdmission.canonicalEnvelopeCodec.encode ⟨header, signature⟩ })

def expectRejected (label : String) (reason : PolicyInstallReceiver.Reject)
    (result : PolicyInstallReceiver.Result) : IO Unit :=
  match result with
  | .rejected actual => require s!"{label}: {repr actual}" (decide (actual = reason))
  | .confirmed _ _ => throw (IO.userError s!"FAIL {label}: accepted")
  | .durableRejected actual => throw (IO.userError s!"FAIL {label}: wrong durable rejection {repr actual}")
  | .contention => throw (IO.userError s!"FAIL {label}: contention")
  | .unavailable detail | .uncertain detail => throw (IO.userError s!"FAIL {label}: {detail}")

def expectConfirmed (label : String) (kind : DurableReceiverIO.Confirmation)
    (result : PolicyInstallReceiver.Result) : IO PolicyInstallReceiver.Receipt :=
  match result with
  | .confirmed actual receipt => do
      require label (decide (actual = kind))
      pure receipt
  | .rejected reason => throw (IO.userError s!"FAIL {label}: {repr reason}")
  | .durableRejected reason => throw (IO.userError s!"FAIL {label}: durable {repr reason}")
  | .contention => throw (IO.userError s!"FAIL {label}: contention")
  | .unavailable detail | .uncertain detail => throw (IO.userError s!"FAIL {label}: {detail}")

def refusedWithoutMutation (native : CredentialSignatureIO.NativeConfig) (signer nativeStore : System.FilePath)
    (publicKey : List UInt8) (label : String) (reason : PolicyInstallReceiver.Reject)
    (fixture : SourceFixture := .fresh) (capabilityId : CapabilityId := controlId)
    (testSeed : Nat := 7) (denies : Bool := false) : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let config ← bootstrap nativeStore directory publicKey fixture denies
    let before ← load config
    let original ← signedIngress signer before capabilityId testSeed denies
    expectRejected label reason
      (← PolicyInstallReceiver.receive profile deployment native config.transport federation height original)
    let after ← load config
    require s!"{label}: exact SQLite bytes unchanged" (after.bytes == before.bytes)

def signedOwnerInvocation (signer : System.FilePath) (durable : PolicyInstallReceiver.Durable)
    (nonce : Nat) (oldValue newValue : Int) : IO DeclaredResourceController.SignedCommand := do
  let authority ← requireSome "same loaded invocation authority"
    (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot)
  let directory ← requireSome "same loaded invocation directory"
    (CredentialAuthorityDomainReceiver.loadDirectory durable)
  let object ← requireSome "actual persisted object"
    (ResourceBirthController.Concrete.observeCell deployment directory.directory policyId.value .declaredObject)
  let command : DeclaredResourceController.Command :=
    { kind := .object
      target := policyId.value
      subject := ⟨7⟩
      capability := ownerId
      expectedAuthorityRoot := authority.snapshot.cell.root
      schemaVersion := 1
      expectedTargetRoot := object.payload.root
      nonce := nonce
      actions := [.write (.objectField ⟨policyId.value⟩ ⟨1⟩) (some oldValue) newValue] }
  let marker := DeclaredResourceController.operationMarker deployment.domain profile.semantics command
  let signed : Digest → IO (List UInt8) := fun root => do
    let wanted := DeclaredResourceController.request authority.snapshot profile.semantics
      ⟨federation, height⟩ command root
    let header ← requireOk "new-revision complete owner request"
      (CredentialSignatureAdmission.signingHeader authority.snapshot marker ⟨.object, wanted⟩)
    let (_, signature) ← sign signer 7 (CredentialSignedEnvelopeController.headerCodec.encode header)
    pure (CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩)
  pure
    { commandBytes := DeclaredResourceController.commandCodec.encode command
      targetEnvelope := ← signed object.payload.root
      authorityEnvelope := ← signed authority.snapshot.cell.root }

def confirmOwnerInvocation (label : String) (native : CredentialSignatureIO.NativeConfig)
    (config : DurableReceiverIO.NativeConfig) (signed : DeclaredResourceController.SignedCommand) : IO Unit := do
  match ← DeclaredResourceController.receive deployment profile ⟨federation, height⟩ native config.transport signed with
  | .settlement (.confirmed .installed _) => require label true
  | .rejected reason => throw (IO.userError s!"FAIL {label}: {repr reason}")
  | _ => throw (IO.userError s!"FAIL {label}: owner operation did not install")

def assertPreservedGrants (durable : PolicyInstallReceiver.Durable) (revision : Nat) : IO Unit := do
  let authority ← requireSome "same reopened grant snapshot"
    (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot)
  require "source revision advances independently of grant generation"
    (authority.snapshot.authState.policyEpoch policyId == 1 &&
      authority.snapshot.authState.policyRevision policyId == revision)
  require "original ordinary owner grant retained exactly, not reissued"
    (decide (readCapability authority.snapshot.cell .object ownerId = some ⟨ownerCapability, []⟩))
  require "original policy-control grant retained exactly, not reissued"
    (decide (readCapability authority.snapshot.cell .program controlId =
      some ⟨capability controlId .installPolicy, []⟩))

def acceptedAndReplayed (native : CredentialSignatureIO.NativeConfig) (signer nativeStore : System.FilePath)
    (publicKey : List UInt8) : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let config ← bootstrap nativeStore directory publicKey
    let before ← load config
    let original ← signedIngress signer before
    let decoded ← requireSome "strict signed ingress" (PolicyInstallReceiver.decodeIngress original)
    require "trailing ingress byte refuses" ((PolicyInstallReceiver.decodeIngress (original ++ [0])).isNone)
    let prepared ← requireOk "actual deterministic representation preparation"
      (PolicyInstallReceiver.prepare profile deployment before federation height decoded)
    let accepted ← requireOk "actual native capability-only accepted installation"
      (← PolicyInstallReceiver.admitDecodedNative profile deployment native before federation height decoded)
    let wanted := PolicyInstallReceiver.intent accepted
    require "new source identity participates in actual allocation"
      ((prepared.creates.map (·.cellId)).contains
        (CanonicalCellRegistry.policySourceCreate deployment.domain newPolicy).cellId)
    let lostReply : DurableReceiverIO.Transport :=
      { read := config.read
        cas := fun expected proposed => do
          match ← config.cas expected proposed with
          | .installed | .alreadyPresent => return .uncertain "probe discards only the native success response"
          | other => return other }
    let first ← expectConfirmed "lost native reply recovered by exact readback" .recoveredAfterUncertainResponse
      (← PolicyInstallReceiver.receive profile deployment native lostReply federation height original)
    let after ← load config
    let authority ← requireSome "complete committed authority"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment after.snapshot)
    require "actual committed new head selects exact source content"
      (decide (authority.snapshot.currentHead policyId = some ⟨2, PolicyRecordCodec.digest (newPolicy)⟩))
    require "actual committed semantic marker consumed"
      (CredentialAuthorityState.isNullified authority.snapshot.cell decoded.marker)
    require "retired source address is absent from authority selection"
      ((authority.snapshot.logical.fields (.policyAddress policyId 1)).isNone)
    let actualDirectory ← requireSome "complete committed lifecycle directory"
      (CredentialAuthorityDomainReceiver.loadDirectory after)
    let source ← requireSome "new head resolves actual immutable source from same reopened snapshot"
      (CanonicalCellRegistry.loadPolicySource deployment.domain actualDirectory.directory
        (PolicyRecordCodec.digest (newPolicy)))
    require "resolved exact successor bytes and record"
      (decide (source.record = newPolicy) && source.canonicalBytes == PolicyRecordCodec.encode (newPolicy))
    require "old immutable source remains available for provenance"
      ((CanonicalCellRegistry.loadPolicySource deployment.domain actualDirectory.directory
        (PolicyRecordCodec.digest (oldPolicy))).isSome)
    require "one recorded transaction and one event"
      (after.snapshot.model.journal.length == 1 && after.snapshot.model.history.length == 1)
    require "actual exact vector charged once"
      (ResourceCost.Lane.allCheck fun lane =>
        decide (after.snapshot.model.available lane + wanted.exactCharge lane =
          before.snapshot.model.available lane))
    let unavailableNative : CredentialSignatureIO.NativeConfig := ⟨directory / "missing-verifier"⟩
    let replayed ← expectConfirmed "original expired-key and expired-grant request replayed before fresh native admission" .replayed
      (← PolicyInstallReceiver.receive profile deployment unavailableNative config.transport federation 20000 original)
    require "historical replay returns only same receipt IDs" (decide (replayed = first))
    let reopened ← load config
    require "restart replay neither rewrites storage nor charges again" (reopened.bytes == after.bytes)
    let changed := { decoded.declaration with source := { decoded.declaration.source with predicate := .all [] } }
    let substituted := PolicyInstallReceiver.ingressCodec.encode
      { decoded.ingress with declarationBytes := PolicyInstallController.encodeDeclaration changed }
    expectRejected "changed payload at same source-derived transaction identity conflicts" .transactionConflict
      (← PolicyInstallReceiver.receive profile deployment unavailableNative config.transport federation 20000 substituted)
    let final ← load config
    require "payload conflict leaves exact physical bytes unchanged" (final.bytes == after.bytes)
    assertPreservedGrants final 2
    let refusedOwner ← signedOwnerInvocation signer final 1002 0 1
    match ← DeclaredResourceController.receive deployment profile ⟨federation, height⟩ native config.transport refusedOwner with
    | .rejected .policyRejected => require "retained owner grant still checks revision-two rules" true
    | _ => throw (IO.userError "FAIL new source must reject wrong-nonce owner mutation")
    require "new-law refusal preserves exact physical image" ((← load config).bytes == final.bytes)
    let firstOwner ← signedOwnerInvocation signer final 1001 0 1
    confirmOwnerInvocation "same original owner grant mutates under revision two" native config firstOwner
    let invoked ← load config
    assertPreservedGrants invoked 2
    let second ← signedIngress signer invoked controlId 7 false (some thirdPolicy) 992
    let secondReceipt ← expectConfirmed "same original control grant installs revision three" .installed
      (← PolicyInstallReceiver.receive profile deployment native config.transport federation height second)
    let twice ← load config
    assertPreservedGrants twice 3
    let secondOwner ← signedOwnerInvocation signer twice 1002 1 2
    confirmOwnerInvocation "same owner grant now satisfies the changed revision-three rule" native config secondOwner
    let complete ← load config
    assertPreservedGrants complete 3
    let completeDirectory ← requireSome "complete final object directory"
      (CredentialAuthorityDomainReceiver.loadDirectory complete)
    let finalObject ← requireSome "actual final persisted object"
      (ResourceBirthController.Concrete.observeCell deployment completeDirectory.directory policyId.value .declaredObject)
    let finalPage ← requireSome "actual final object page"
      (DeclaredEffectPageMaterializer.pageAt finalObject.payload.logical)
    require "both owner mutations survive actual SQLite reopen"
      (decide (finalPage.lookup (.objectField ⟨policyId.value⟩ ⟨1⟩) = some 2))
    require "two installs plus two accepted owner mutations are the whole journal"
      (complete.snapshot.model.journal.length == 4)
    let fourth : PolicyRecord :=
      { thirdPolicy with version := 4, previous := some (PolicyRecordCodec.digest thirdPolicy), predicate := .all [] }
    let lockout ← signedIngress signer complete controlId 7 false (some fourth) 993
    expectRejected "self-governing rule lockout is policy refusal, not a revoked control grant"
      (.semantic .policyRejected)
      (← PolicyInstallReceiver.receive profile deployment native config.transport federation height lockout)
    let historicalFirst ← expectConfirmed "first install replay survives subsequent source and object changes" .replayed
      (← PolicyInstallReceiver.receive profile deployment unavailableNative config.transport federation 20000 original)
    let historicalSecond ← expectConfirmed "second install replay survives subsequent object changes" .replayed
      (← PolicyInstallReceiver.receive profile deployment unavailableNative config.transport federation 20000 second)
    require "both historical receipts are the original receipts"
      (decide (historicalFirst = first) && decide (historicalSecond = secondReceipt))
    require "lockout and expired historical replay preserve all physical bytes and charges"
      ((← load config).bytes == complete.bytes)
    IO.println s!"committed source bytes={source.canonicalBytes.length}, first writes={prepared.writes.length}, first guards={prepared.readGuards.length}, final journal={complete.snapshot.model.journal.length}"


def run (verifier signer nativeStore : System.FilePath) : IO Unit := do
  let native : CredentialSignatureIO.NativeConfig := ⟨verifier⟩
  let (publicKey, _) ← sign signer 7 []
  refusedWithoutMutation native signer nativeStore publicKey "preexisting exact successor source refuses"
    (.allocation .duplicateCreate) .occupiedSuccessor
  refusedWithoutMutation native signer nativeStore publicKey "retired successor identity cannot resurrect"
    (.allocation .retiredIdentifier) .retiredSuccessor
  refusedWithoutMutation native signer nativeStore publicKey "unavailable old canonical source refuses"
    .oldSourceUnavailable .missingOld
  refusedWithoutMutation native signer nativeStore publicKey "ordinary code-edit cap cannot replace law"
    (.semantic .capability) .fresh codeId
  refusedWithoutMutation native signer nativeStore publicKey "copied public cap without holder key refuses"
    (.nativeSignature (.envelope .invalidSignature)) .fresh controlId 8
  refusedWithoutMutation native signer nativeStore publicKey "actual old policy controls replacement"
    (.semantic .policyRejected) .fresh controlId 7 true
  acceptedAndReplayed native signer nativeStore publicKey
  IO.println "PASS policy installation: real native holder signature and control capability, same-snapshot old source, atomic durable new source+head+marker, occupied/retired/old-law/cap/key refusals, lost-reply recovery and unchanged-ingress restart replay. Successive source revisions preserve the exact original owner/control grants, newly selected rules govern actual object mutations, and deliberate self-governing install lockout remains distinct from epoch revocation."

end PolicyInstallReceiverProbe

def main (arguments : List String) : IO Unit :=
  match arguments with
  | [verifier, signer, store] => PolicyInstallReceiverProbe.run verifier signer store
  | _ => throw (IO.userError
      "usage: lean --run scripts/probe-policy-install-receiver.lean VERIFIER PUBLIC-TEST-SIGNER SQLITE-STORE")
