/-
One native user action chain: create an owned object through the actual birth
receiver, reopen the published image, then invoke its actually issued owner
capability. Bootstrap contains only the deployment, Alice's existing fee
account, its spending capability, and their existing policies. The newborn,
both owner roles and its initial policy must all come from accepted birth.
-/
import Kernel.ResourceBirthReceiver
import Kernel.DeclaredResourceController
import Kernel.PolicyInstallReceiver
import Kernel.CapabilityDelegationReceiver

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel

namespace BornResourceInvocationProbe

def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL born resource: {label}")
  IO.println s!"PASS born resource: {label}"

def requireSome {α : Type} (label : String) : Option α → IO α
  | some value => pure value
  | none => throw (IO.userError s!"FAIL born resource: {label}")

def requireOk {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"FAIL born resource: {label}: {repr reason}")

def sign (signer : System.FilePath) (seed : Nat) (frame : List UInt8) :
    IO (List UInt8 × List UInt8) :=
  IO.FS.withTempDir fun directory => do
    let framePath := directory / "frame.bin"
    let keyPath := directory / "key.bin"
    let signaturePath := directory / "signature.bin"
    IO.FS.writeBinFile framePath frame.toByteArray
    let output ← IO.Process.output
      { cmd := signer.toString
        args := #[toString seed, framePath.toString, keyPath.toString, signaturePath.toString] }
    require "actual public-test-key signer"
      (output.exitCode == 0 && output.stdout == "" &&
        output.stderr == s!"PUBLIC TEST KEY: seed = [{seed}; 32]; anyone can reproduce this signing key.\n")
    pure ((← IO.FS.readBinFile keyPath).toList, (← IO.FS.readBinFile signaturePath).toList)

instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- Probe parameters, not a production field selection. -/
def profile : CanonicalRuntimeProfile.Profile (ZMod 65537) :=
  .source ⟨⟨5⟩, 100000, 10000⟩ ⟨65537⟩ 65537 inferInstance 15
    (PredOrder.noWrap_zmod (by decide))

def deployment : CanonicalCellRegistry.Deployment := ⟨⟨8500⟩, 10, 11, 12⟩
def height : Height := 10
def targetId : Nat := 600
def payerId : Nat := 7
def collectorId : Nat := 99
def payerCapId : CapabilityId := ⟨41⟩
def ownerCapId : CapabilityId := ⟨42⟩
def controlCapId : CapabilityId := ⟨43⟩

def key (subject : Nat) (publicKey : List UInt8) : KeyRecord where
  keyId := 7000 + subject
  keyEpoch := 2
  algorithm := CredentialSignatureAdmission.ed25519Algorithm
  subject := subject
  publicKey := publicKey
  activeFrom := 0
  activeUntil := 100
  revoked := false

def policy (identifier : Nat) (predicate : Minidregg.Pred.Pred) : PolicyRecord where
  policyId := ⟨identifier⟩
  version := 0
  domain := deployment.domain
  semantics := profile.semantics
  previous := none
  predicate := predicate

def factoryPolicy : PolicyRecord := policy deployment.factoryId (.eq "request/creator" 7)
def payerPolicy : PolicyRecord := policy payerId (.eq "request/subject" 7)
def bornPolicy : PolicyRecord := policy targetId (.memberOf "request/verb" [2, 3, 4])

def pins : FactoryPins where
  factory := ⟨deployment.factoryId⟩
  domain := deployment.domain
  semantics := profile.semantics
  federation := ⟨9⟩
  policyId := factoryPolicy.policyId
  policyAddress := PolicyRecordCodec.digest factoryPolicy
  tariff := ⟨3, 2, 1, 0, collectorId, 0⟩

def rootCapability (kind : ResourceKind) (identifier : CapabilityId)
    (target : Nat) (verbs : Finset (Verb kind)) (starts : Height) : Capability kind where
  id := identifier
  root := identifier
  parent := none
  issuer := profile.template.issuer
  holder := .subject ⟨7⟩
  scope := ⟨{⟨target⟩}, verbs, profile.template.ownerBudget⟩
  notBefore := starts
  notAfter := starts + profile.template.lifetime
  issuerEpoch := 2
  policyId := ⟨target⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def payerCapability : Capability .account :=
  rootCapability .account payerCapId payerId {.transfer} 0

def ownerCapability : Capability .object :=
  rootCapability .object ownerCapId targetId
    (ResourceBirthPolicyController.Concrete.ownerVerbs .object) height

def controlCapability : Capability .program :=
  rootCapability .program controlCapId targetId {.installPolicy} height

def objectCell (identifier : Nat) (value : Int) : PackedCell CanonicalCellRegistry.registry :=
  ⟨.declaredObject, materialize DeclaredEffectPageMaterializer.materializer
    (DeclaredEffectPageMaterializer.stateOfOption (some
      ⟨deployment.domain, identifier % DeclaredEffectPageMaterializer.shardCount,
        some ⟨.objectField ⟨identifier⟩ ⟨1⟩, value⟩, none, none, none⟩))⟩

def initialBook : CanonicalResourceKernel.Book where
  accounts := {0, payerId, collectorId}
  balances := DFinsupp.single (0, 0) (-100) + DFinsupp.single (payerId, 0) 100
  leaseRecords := 0

def bookCell : PackedCell CanonicalCellRegistry.registry :=
  ⟨.resourceBook, materialize CanonicalResourcePageMaterializer.materializer
    (CanonicalResourcePageMaterializer.stateOfOption (some initialBook))⟩

def physicalCell (identifier : Nat) (cell : PackedCell CanonicalCellRegistry.registry) :
    Digest × List UInt8 :=
  (⟨identifier⟩, ResourceBirthCodec.LifecycleImage.bytes _ (.live cell))

def sourceCell (record : PolicyRecord) : Digest × List UInt8 :=
  physicalCell (PolicySourceCell.physicalId deployment.domain (PolicyRecordCodec.digest record))
    (CanonicalCellRegistry.policySourceCell record)

def seed (alice bob : KeyRecord) : IO DurableReceiver.Seed := do
  let entries : List CredentialAuthorityPageMaterializer.Entry :=
    [.subjectKey alice, .subjectKey bob, .issuerEpoch profile.template.issuer 2,
      .policy factoryPolicy.policyId 0 0 (PolicyRecordCodec.digest factoryPolicy),
      .policy payerPolicy.policyId 0 0 (PolicyRecordCodec.digest payerPolicy),
      .capability .account ⟨payerCapability, []⟩]
  let pages ← requireSome "source-routed deployment authority"
    (CredentialAuthorityDomain.runEdits deployment.domain []
      (entries.map fun entry => ⟨none, entry⟩))
  let empty : CredentialAuthorityDomain.Catalogue := ⟨deployment.domain, 0, []⟩
  let catalogue := CredentialAuthorityDomainReceiver.placedCatalogue empty
    (CredentialAuthorityDomainReceiver.placePages empty pages 2000)
  pure
    { absentBytes := []
      cells :=
        [(deployment.authorityAnchor.catalogueCellId, CredentialAuthorityDomainReceiver.catalogueBytes catalogue),
         physicalCell deployment.factoryId (objectCell deployment.factoryId 0),
         physicalCell deployment.resourceBookId bookCell,
         sourceCell factoryPolicy, sourceCell payerPolicy] ++
          (catalogue.pages.zip pages).map fun (reference, page) =>
            (reference.cellId, CredentialAuthorityDomainReceiver.shardBytes page)
      available := fun _ => 10000000 }

def birthIdentity : Digest :=
  ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile deployment ⟨7⟩ 9411

def draft : Descriptor CanonicalCellRegistry.registry where
  factory := pins.factory
  creator := ⟨7⟩
  transactionId := birthIdentity
  nonce := 9411
  births :=
    [⟨⟨targetId, CellSlot.root CanonicalCellRegistry.registry .absent, objectCell targetId 0⟩,
      .object, ⟨7⟩⟩]
  auxiliaryCreates := []
  grants := [⟨.object, ⟨ownerCapability, []⟩⟩, ⟨.program, ⟨controlCapability, []⟩⟩]
  initialPolicies :=
    [⟨bornPolicy.policyId, PolicyRecordCodec.digest bornPolicy, PolicyRecordCodec.encode bornPolicy⟩]
  authorityNullifier := birthIdentity.value
  funding := []
  fee := ⟨payerId, collectorId, 0, 7⟩

def envelope (signer : System.FilePath) (snapshot : CredentialAuthorityDomain.Snapshot)
    (marker : Nat) (wanted : PackedEffectRequest) (seed : Nat := 7) : IO (List UInt8) := do
  let header ← requireOk "exact source signing header"
    (CredentialSignatureAdmission.signingHeader snapshot marker wanted)
  let (_, signature) ← sign signer seed (CredentialSignedEnvelopeController.headerCodec.encode header)
  pure (CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩)

def birthIngress (signer : System.FilePath)
    {durable : ResourceBirthController.Concrete.Durable}
    (prepared : ResourceBirthController.Concrete.PreparedDraft profile.compilerProfile
      deployment pins durable draft) : IO (List UInt8) := do
  let credential : ResourceBirthPolicyController.Concrete.Branch prepared.descriptor →
      IO ResourceBirthPolicyController.Concrete.BranchCredential := fun branch => do
    let wanted := ResourceBirthPolicyController.Concrete.branchRequest
      (profile := profile) prepared.prepared height branch
    let wire ← envelope signer prepared.prepared.authority.snapshot
      prepared.descriptor.authorityNullifier wanted
    let capability := match branch with
      | .source _ => some payerCapId
      | _ => none
    pure ({ capability := capability, envelope := wire } : ResourceBirthPolicyController.Concrete.BranchCredential)
  let factory ← credential .factory
  let authority ← credential .authority
  let allocations ← (List.finRange prepared.descriptor.createRequests.length).mapM
    (fun index => credential (.allocation index))
  let sources ← (List.finRange prepared.descriptor.resourceBatch.operations.length).mapM
    (fun index => credential (.source index))
  pure (ResourceBirthPolicyController.Concrete.ingressCodec.encode
    ⟨CanonicalCellRegistry.sourceEncoding.codec.encode prepared.descriptor,
      ⟨factory, authority, allocations, sources⟩⟩)

def actualBook (durable : ResourceBirthController.Concrete.Durable) : IO CanonicalResourceKernel.Book := do
  let directory ← requireSome "complete reopened directory"
    (CredentialAuthorityDomainReceiver.loadDirectory durable)
  let book ← requireSome "pinned actual Book"
    (ResourceBirthController.Concrete.observeCell deployment directory.directory
      deployment.resourceBookId .resourceBook)
  pure (CanonicalResourceKernel.logicalBook book.payload.logical)

def invocation (durable : ResourceBirthController.Concrete.Durable)
    (snapshot : CredentialAuthorityDomain.Snapshot) : IO DeclaredResourceController.Command := do
  let directory ← requireSome "born resource directory"
    (CredentialAuthorityDomainReceiver.loadDirectory durable)
  let object ← requireSome "actual born declared object"
    (ResourceBirthController.Concrete.observeCell deployment directory.directory targetId .declaredObject)
  pure
    { kind := .object
      target := targetId
      subject := ⟨7⟩
      capability := ownerCapId
      expectedAuthorityRoot := snapshot.cell.root
      schemaVersion := 1
      expectedTargetRoot := object.payload.root
      nonce := 991
      actions := [.write (.objectField ⟨targetId⟩ ⟨1⟩) (some 0) 1] }

def invocationAmbient : DeclaredResourceController.Ambient := ⟨pins.federation, height + 1⟩

def signedInvocationAt (ambient : DeclaredResourceController.Ambient) (signer : System.FilePath) (snapshot : CredentialAuthorityDomain.Snapshot)
    (command : DeclaredResourceController.Command) (seed : Nat := 7) : IO DeclaredResourceController.SignedCommand := do
  let marker := DeclaredResourceController.operationMarker snapshot.domain profile.semantics command
  let wanted := fun root =>
    DeclaredResourceController.request snapshot profile.semantics ambient command root
  pure
    { commandBytes := DeclaredResourceController.commandCodec.encode command
      targetEnvelope := ← envelope signer snapshot marker ⟨command.kind, wanted command.expectedTargetRoot⟩ seed
      authorityEnvelope := ← envelope signer snapshot marker ⟨command.kind, wanted snapshot.cell.root⟩ seed }

def signedInvocation (signer : System.FilePath) (snapshot : CredentialAuthorityDomain.Snapshot)
    (command : DeclaredResourceController.Command) (seed : Nat := 7) : IO DeclaredResourceController.SignedCommand :=
  signedInvocationAt invocationAmbient signer snapshot command seed

def ownerRule (revision : Nat) (previous : Digest) (recipientMayMutate : Bool) : PolicyRecord where
  policyId := ⟨targetId⟩
  version := revision
  domain := deployment.domain
  semantics := profile.semantics
  previous := some previous
  predicate := .any
    [.all [.memberOf "request/verb" [3, 4], .eq "request/subject" 7],
      .all [.eq "request/verb" 2, .eq "request/subject" (if recipientMayMutate then 8 else 99)]]

def installRules (native : CredentialSignatureIO.NativeConfig) (signer : System.FilePath)
    (transport : DurableReceiverIO.Transport) (atHeight : Height) (nonce : Nat)
    (source : PolicyRecord) : IO (List UInt8 × PolicyInstallReceiver.Receipt) := do
  let loaded ← requireOk "load rule replacement" (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
  let authority ← requireSome "rule replacement complete authority"
    (CredentialAuthorityDomainReceiver.loadDeployment deployment loaded.snapshot)
  let snapshot := authority.snapshot
  let context : PolicyInstallController.RequestContext :=
    { federation := pins.federation, subject := ⟨7⟩, subjectKeyEpoch := snapshot.authState.subjectKeyEpoch ⟨7⟩,
      height := atHeight, policyEpoch := snapshot.authState.policyEpoch source.policyId,
      policyRevision := snapshot.authState.policyRevision source.policyId }
  let declaration : PolicyInstallController.Declaration :=
    ⟨snapshot.cell.root, snapshot.currentHead source.policyId, nonce, source⟩
  let wanted := PolicyInstallController.request profile snapshot context declaration
  let marker := (PolicyInstallController.requestDigest profile snapshot context declaration).value
  let wire := PolicyInstallReceiver.ingressCodec.encode
    { subject := ⟨7⟩, controlCapability := controlCapId,
      declarationBytes := PolicyInstallController.declarationCodec.encode declaration,
      envelopeBytes := ← envelope signer snapshot marker ⟨.program, wanted⟩ }
  match ← PolicyInstallReceiver.receiveLoaded profile deployment native transport loaded pins.federation atHeight wire with
  | .confirmed .installed receipt => pure (wire, receipt)
  | .rejected reason => throw (IO.userError s!"FAIL born resource: rule replacement rejected: {repr reason}")
  | _ => throw (IO.userError "FAIL born resource: rule replacement not durably installed")

def bobCapability : Capability .object where
  id := ⟨44⟩
  root := ownerCapId
  parent := some ownerCapId
  issuer := ownerCapability.issuer
  holder := .subject ⟨8⟩
  scope := ⟨{⟨targetId⟩}, {.mutateObject}, 50000⟩
  notBefore := height + 3
  notAfter := 50
  issuerEpoch := ownerCapability.issuerEpoch
  policyId := ⟨targetId⟩
  policyEpoch := 0
  ancestors := {ownerCapId}
  channels := ∅

def birthSummary : ResourceBirthReceiver.Result → String
  | .confirmed kind _ => s!"confirmed {repr kind}"
  | .rejected .malformedIngress => "malformed ingress"
  | .rejected .transactionConflict => "transaction conflict"
  | .rejected (.admission reason) => s!"admission: {repr reason}"
  | .rejected (.durable reason) => s!"durable: {repr reason}"
  | .contention => "contention"
  | .unavailable detail => s!"unavailable: {detail}"
  | .uncertain detail => s!"uncertain: {detail}"

def invocationSummary : DeclaredResourceController.ReceiveResult → String
  | .replayed _ => "replayed"
  | .rejected reason => s!"admission: {repr reason}"
  | .transactionConflict => "transaction conflict"
  | .unavailable detail => s!"unavailable: {detail}"
  | .settlement (.confirmed kind _) => s!"confirmed {repr kind}"
  | .settlement (.rejected reason) => s!"durable: {repr reason}"
  | .settlement .contention => "contention"
  | .settlement (.unavailable detail) => s!"unavailable: {detail}"
  | .settlement (.uncertain detail) => s!"uncertain: {detail}"

set_option maxRecDepth 4096 in
def run (verifier signer nativeStore : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let native : CredentialSignatureIO.NativeConfig := ⟨verifier⟩
    let transport := (DurableReceiverIO.NativeConfig.mk nativeStore (directory / "store")).transport
    let (aliceKey, _) ← sign signer 7 []
    let (bobKey, _) ← sign signer 8 []
    let initial ← seed (key 7 aliceKey) (key 8 bobKey)
    requireOk "bootstrap deployment and existing fee account"
      (← DurableReceiverIO.bootstrap transport ResourceBirthCodec.rootBytes initial)
    let before ← requireOk "initial physical reopen"
      (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
    let initialDirectory ← requireSome "initial complete directory"
      (CredentialAuthorityDomainReceiver.loadDirectory before)
    let initialAuthority ← requireSome "initial complete authority"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment before.snapshot)
    require "newborn absent before actual birth"
      (match initialDirectory.directory.slots targetId with | .absent => true | _ => false)
    require "no initial owner or policy-control grant"
      ((readCapability initialAuthority.snapshot.cell .object ownerCapId).isNone &&
        (readCapability initialAuthority.snapshot.cell .program controlCapId).isNone)
    require "newborn policy source absent before actual birth"
      ((CanonicalCellRegistry.fetchPolicySource deployment.domain initialDirectory.directory
        (PolicyRecordCodec.digest bornPolicy)).isNone)
    let prepared ← requireOk "source preparation of the complete user birth"
      (ResourceBirthController.Concrete.prepareDraft profile.compilerProfile deployment pins before draft)
    let input ← birthIngress signer prepared
    let parsed ← requireSome "strict source signed ingress roundtrip"
      (ResourceBirthPolicyController.Concrete.ingressCodec.decode input)
    let birth := ResourceBirthReceiver.receive profile deployment pins native transport height
    let originalBytes ← requireOk "original storage bytes" (← transport.read)
    let copiedIdentity := { prepared.descriptor with creator := ⟨8⟩ }
    let foreignRequest := factoryRequest pins CanonicalCellRegistry.sourceEncoding
      prepared.prepared.oldAuthority prepared.prepared.factory.payload.root height copiedIdentity
    let foreignEnvelope ← envelope signer prepared.prepared.authority.snapshot
      copiedIdentity.authorityNullifier ⟨.object, foreignRequest⟩ 8
    let _ ← requireOk "Bob has a real valid enrolled signature for his exact copied-coordinate factory request"
      (← CredentialSignatureAdmission.verifyNative native prepared.prepared.authority.snapshot
        copiedIdentity.authorityNullifier foreignRequest foreignEnvelope)
    let foreignInput := ResourceBirthPolicyController.Concrete.ingressCodec.encode
      { parsed with
        descriptorBytes := CanonicalCellRegistry.sourceEncoding.codec.encode copiedIdentity
        credentials := { parsed.credentials with factory := ⟨none, foreignEnvelope⟩ } }
    match ← birth foreignInput with
    | .rejected (.admission (.preparation .identity)) => pure ()
    | _ => throw (IO.userError "FAIL born resource: a foreign creator copied Alice's source identity")
    match ← birth (input ++ [0]) with
    | .rejected _ => pure ()
    | _ => throw (IO.userError "FAIL born resource: noncanonical signed birth did not refuse")
    require "rejected birth leaves exact storage image unchanged"
      (decide ((← requireOk "storage after refusal" (← transport.read)) = originalBytes))
    let birthReceipt ← match ← birth input with
      | .confirmed .installed receipt => pure receipt
      | outcome => throw (IO.userError s!"FAIL born resource: actual signed birth: {birthSummary outcome}")
    let born ← requireOk "reopen actual accepted birth"
      (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
    let bornAuthority ← requireSome "complete born authority"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment born.snapshot)
    require "actual birth issued the exact ordinary and policy-control roles"
      (decide (readCapability bornAuthority.snapshot.cell .object ownerCapId = some ⟨ownerCapability, []⟩) &&
        decide (readCapability bornAuthority.snapshot.cell .program controlCapId = some ⟨controlCapability, []⟩))
    let bornDirectory ← requireSome "born complete directory"
      (CredentialAuthorityDomainReceiver.loadDirectory born)
    require "actual birth persisted the exact initial policy source"
      (decide (CanonicalCellRegistry.fetchPolicySource deployment.domain bornDirectory.directory
        (PolicyRecordCodec.digest bornPolicy) = some (PolicyRecordCodec.encode bornPolicy)))
    require "actual birth consumed its shared authority marker"
      (isNullified bornAuthority.snapshot.cell draft.authorityNullifier)
    let paidBook ← actualBook born
    require "creation fee is an actual conserved Book debit and credit"
      (paidBook.balance payerId 0 == 93 && paidBook.balance collectorId 0 == 7 &&
        paidBook.totalAsset 0 == initialBook.totalAsset 0)
    require "fee admission lane charged the same amount"
      (before.snapshot.model.available .feeDebit - born.snapshot.model.available .feeDebit == 7)
    let bornBytes ← requireOk "committed birth bytes" (← transport.read)
    match ← birth input with
    | .confirmed .replayed receipt => require "exact birth retry returns original receipt" (receipt == birthReceipt)
    | _ => throw (IO.userError "FAIL born resource: exact birth retry did not replay")
    require "birth retry performs no write, fee or admission charge"
      (decide ((← requireOk "read birth retry" (← transport.read)) = bornBytes))
    let changedPayload := { prepared.descriptor with
      births := prepared.descriptor.births.map fun item =>
        { item with create := { item.create with cell := objectCell targetId 9 } } }
    require "changed payload retains the source creator/nonce identity"
      (changedPayload.transactionId == ResourceBirthController.Concrete.sourceIdentity
        profile.compilerProfile deployment changedPayload.creator changedPayload.nonce)
    let changedInput := ResourceBirthPolicyController.Concrete.ingressCodec.encode
      { parsed with descriptorBytes := CanonicalCellRegistry.sourceEncoding.codec.encode changedPayload }
    match ← birth changedInput with
    | .rejected .transactionConflict => pure ()
    | _ => throw (IO.userError "FAIL born resource: changed payload reused a successful birth identity")
    require "changed-payload replay conflict preserves the exact born image"
      (decide ((← requireOk "read birth replay conflict" (← transport.read)) = bornBytes))
    let command ← invocation born bornAuthority.snapshot
    let invoke := DeclaredResourceController.receive deployment profile invocationAmbient native transport
    let bob := { command with subject := ⟨8⟩ }
    match ← invoke (← signedInvocation signer bornAuthority.snapshot bob 8) with
    | .rejected _ => pure ()
    | _ => throw (IO.userError "FAIL born resource: Bob used Alice's newly issued capability")
    require "unrelated signer refusal preserves the actual born image"
      (decide ((← requireOk "read denied born invocation" (← transport.read)) = bornBytes))
    let invokeInput ← signedInvocation signer bornAuthority.snapshot command
    match ← invoke invokeInput with
    | .settlement (.confirmed .installed _) => pure ()
    | outcome => throw (IO.userError s!"FAIL born resource: actual issued owner invocation: {invocationSummary outcome}")
    let invoked ← requireOk "reopen born owner invocation"
      (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
    let finalDirectory ← requireSome "invoked directory"
      (CredentialAuthorityDomainReceiver.loadDirectory invoked)
    let target ← requireSome "persisted born object"
      (DeclaredResourceController.observeTarget deployment finalDirectory.directory command)
    let page ← requireSome "persisted born object page"
      (DeclaredEffectPageMaterializer.pageAt target.pre.logical)
    require "actual born owner changed the actual object"
      (decide (page.lookup (.objectField ⟨targetId⟩ ⟨1⟩) = some 1))
    let finalBook ← actualBook invoked
    require "ordinary object invocation does not manufacture or repeat a Book fee"
      (finalBook.balance payerId 0 == 93 && finalBook.balance collectorId 0 == 7 &&
        finalBook.totalAsset 0 == initialBook.totalAsset 0)
    let finalBytes ← requireOk "final physical image" (← transport.read)
    match ← invoke invokeInput with
    | .replayed _ => pure ()
    | _ => throw (IO.userError "FAIL born resource: exact owner invocation retry did not replay")
    match ← birth input with
    | .confirmed .replayed receipt => require "birth receipt survives later invocation" (receipt == birthReceipt)
    | _ => throw (IO.userError "FAIL born resource: historical birth retry failed after owner invocation")
    match ← ResourceBirthReceiver.receive profile deployment pins native transport 20000 input with
    | .confirmed .replayed receipt =>
      require "expired-key and expired-owner replay returns original birth receipt" (receipt == birthReceipt)
    | _ => throw (IO.userError "FAIL born resource: original birth replay was treated as fresh after credential expiry")
    require "historical and expired-credential retries preserve all storage, fees and admission lanes"
      (decide ((← requireOk "read both historical retries" (← transport.read)) = finalBytes))
    let firstRule := ownerRule 1 (PolicyRecordCodec.digest bornPolicy) false
    let (firstInstall, firstReceipt) ← installRules native signer transport (height + 2) 1201 firstRule
    let once ← requireOk "reopen first rule update" (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
    let onceAuthority ← requireSome "first rule authority"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment once.snapshot)
    require "rule update changes revision while preserving exact owner/control grants and generation"
      (onceAuthority.snapshot.authState.policyEpoch ⟨targetId⟩ == 0 &&
        onceAuthority.snapshot.authState.policyRevision ⟨targetId⟩ == 1 &&
        decide (readCapability onceAuthority.snapshot.cell .object ownerCapId = some ⟨ownerCapability, []⟩) &&
        decide (readCapability onceAuthority.snapshot.cell .program controlCapId = some ⟨controlCapability, []⟩))
    let onceDirectory ← requireSome "first rule object directory" (CredentialAuthorityDomainReceiver.loadDirectory once)
    let onceObject ← requireSome "first rule object"
      (ResourceBirthController.Concrete.observeCell deployment onceDirectory.directory targetId .declaredObject)
    let denied : DeclaredResourceController.Command :=
      { command with
        expectedAuthorityRoot := onceAuthority.snapshot.cell.root
        expectedTargetRoot := onceObject.payload.root
        nonce := 1202
        actions := [.write (.objectField ⟨targetId⟩ ⟨1⟩) (some 1) 2] }
    let deniedAmbient : DeclaredResourceController.Ambient := ⟨pins.federation, height + 2⟩
    let onceBytes ← requireOk "first rule bytes" (← transport.read)
    match ← DeclaredResourceController.receiveLoaded deployment profile deniedAmbient native transport once
        (← signedInvocationAt deniedAmbient signer onceAuthority.snapshot denied) with
    | .rejected .policyRejected => pure ()
    | outcome => throw (IO.userError s!"FAIL born resource: retained owner ignored new rule: {invocationSummary outcome}")
    require "new-rule refusal preserves exact durable image"
      (decide ((← requireOk "read new-rule refusal" (← transport.read)) = onceBytes))
    let secondRule := ownerRule 2 (PolicyRecordCodec.digest firstRule) true
    let (secondInstall, secondReceipt) ← installRules native signer transport (height + 3) 1203 secondRule
    let twice ← requireOk "reopen second rule update" (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
    let twiceAuthority ← requireSome "second rule authority"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment twice.snapshot)
    require "same original control grant performs second rule replacement"
      (twiceAuthority.snapshot.authState.policyEpoch ⟨targetId⟩ == 0 &&
        twiceAuthority.snapshot.authState.policyRevision ⟨targetId⟩ == 2 &&
        decide (readCapability twiceAuthority.snapshot.cell .program controlCapId = some ⟨controlCapability, []⟩))
    let twiceDirectory ← requireSome "delegation resource directory" (CredentialAuthorityDomainReceiver.loadDirectory twice)
    let twiceObject ← requireSome "delegation observed actual born resource"
      (ResourceBirthController.Concrete.observeCell deployment twiceDirectory.directory targetId .declaredObject)
    let delegationAmbient : CapabilityDelegationController.Ambient := ⟨pins.federation, height + 4⟩
    let delegationDraft : CapabilityDelegationController.Command .object :=
      { subject := ⟨7⟩, nonce := 1301, expectedTargetRoot := twiceObject.payload.root,
        declaration := ⟨bobCapability, ownerCapId, ⟨targetId⟩, twiceAuthority.snapshot.cell.root, 0⟩ }
    let marker := CapabilityDelegationController.operationMarker deployment.domain profile.semantics delegationDraft
    let delegation := { delegationDraft with
      declaration := { delegationDraft.declaration with operationNullifier := marker } }
    let wanted := CapabilityDelegationController.request twiceAuthority.snapshot profile.semantics delegationAmbient delegation
    let delegationEnvelope ← envelope signer twiceAuthority.snapshot marker ⟨.object, wanted⟩
    let delegationWire := CapabilityDelegationReceiver.ingressCodec.encode
      ⟨CapabilityDelegationController.commandCodec.encode ⟨.object, delegation⟩, delegationEnvelope⟩
    let beforeDelegationBytes ← requireOk "before delegation bytes" (← transport.read)
    match ← CapabilityDelegationReceiver.receive deployment profile delegationAmbient native transport (delegationWire ++ [0]) with
    | .rejected .malformedCommand => pure ()
    | _ => throw (IO.userError "FAIL born resource: noncanonical delegation ingress accepted")
    let editedChild := { delegation with declaration := { delegation.declaration with child :=
      { bobCapability with scope := { bobCapability.scope with maxCost := 100001 } } } }
    let editedWire := CapabilityDelegationReceiver.ingressCodec.encode
      ⟨CapabilityDelegationController.commandCodec.encode ⟨.object, editedChild⟩, delegationEnvelope⟩
    match ← CapabilityDelegationReceiver.receive deployment profile delegationAmbient native transport editedWire with
    | .rejected _ => pure ()
    | _ => throw (IO.userError "FAIL born resource: amplified/edited child accepted")
    let changedRecipient := { delegation with declaration := { delegation.declaration with child :=
      { bobCapability with holder := .subject ⟨7⟩ } } }
    let changedRecipientWire := CapabilityDelegationReceiver.ingressCodec.encode
      ⟨CapabilityDelegationController.commandCodec.encode ⟨.object, changedRecipient⟩, delegationEnvelope⟩
    match ← CapabilityDelegationReceiver.receive deployment profile delegationAmbient native transport changedRecipientWire with
    | .rejected (.signature _) => pure ()
    | _ => throw (IO.userError "FAIL born resource: signature permitted child recipient substitution")
    let duplicateKind := { delegation with declaration := { delegation.declaration with child :=
      { bobCapability with id := controlCapId } } }
    let duplicateKindWire := CapabilityDelegationReceiver.ingressCodec.encode
      ⟨CapabilityDelegationController.commandCodec.encode ⟨.object, duplicateKind⟩, delegationEnvelope⟩
    match ← CapabilityDelegationReceiver.receive deployment profile delegationAmbient native transport duplicateKindWire with
    | .rejected .descent => pure ()
    | _ => throw (IO.userError "FAIL born resource: child identity already used by another storage kind")
    require "delegation refusals never create child or consume marker"
      (decide ((← requireOk "read denied delegation" (← transport.read)) = beforeDelegationBytes))
    let delegationReceipt ← match ← CapabilityDelegationReceiver.receiveLoaded deployment profile delegationAmbient native transport twice delegationWire with
      | .confirmed .installed receipt => pure receipt
      | .rejected reason => throw (IO.userError s!"FAIL born resource: actual Alice delegation rejected: {repr reason}")
      | _ => throw (IO.userError "FAIL born resource: actual Alice delegation did not commit")
    let delegated ← requireOk "reopen delegated grant" (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
    let delegatedAuthority ← requireSome "delegated complete authority"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment delegated.snapshot)
    let storedBob ← requireSome "source-created Bob child"
      (readCapability delegatedAuthority.snapshot.cell .object bobCapability.id)
    require "exact delegated child retains full source-derived origin and canonical parent"
      (decide (storedBob.head = bobCapability) &&
        decide (storedBob.ancestry = [⟨ownerCapability, .delegated wanted⟩]) &&
        CredentialLineageAdmission.storedLineageCheck delegatedAuthority.snapshot.cell storedBob)
    let recipientAmbient : DeclaredResourceController.Ambient := ⟨pins.federation, height + 5⟩
    let recipient : DeclaredResourceController.Command :=
      { denied with
        subject := ⟨8⟩
        capability := bobCapability.id
        nonce := 1302
        expectedAuthorityRoot := delegatedAuthority.snapshot.cell.root }
    let delegatedBytes ← requireOk "delegated bytes" (← transport.read)
    match ← DeclaredResourceController.receiveLoaded deployment profile recipientAmbient native transport delegated
        (← signedInvocationAt recipientAmbient signer delegatedAuthority.snapshot recipient 7) with
    | .rejected _ => pure ()
    | _ => throw (IO.userError "FAIL born resource: Alice's signature invoked Bob's child")
    require "wrong recipient signature preserves storage"
      (decide ((← requireOk "read wrong recipient signature" (← transport.read)) = delegatedBytes))
    let recipientWire ← signedInvocationAt recipientAmbient signer delegatedAuthority.snapshot recipient 8
    match ← DeclaredResourceController.receiveLoaded deployment profile recipientAmbient native transport delegated recipientWire with
    | .settlement (.confirmed .installed _) => pure ()
    | outcome => throw (IO.userError s!"FAIL born resource: actual Bob invocation: {invocationSummary outcome}")
    let finished ← requireOk "reopen recipient invocation" (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
    let finishedDirectory ← requireSome "recipient final directory" (CredentialAuthorityDomainReceiver.loadDirectory finished)
    let finishedObject ← requireSome "recipient final object"
      (ResourceBirthController.Concrete.observeCell deployment finishedDirectory.directory targetId .declaredObject)
    let finishedPage ← requireSome "recipient final page" (DeclaredEffectPageMaterializer.pageAt finishedObject.payload.logical)
    require "Bob's native invocation changed actual born object under revision2"
      (decide (finishedPage.lookup (.objectField ⟨targetId⟩ ⟨1⟩) = some 2))
    let finishedBytes ← requireOk "recipient final bytes" (← transport.read)
    let finishedAuthority ← requireSome "final authority for forbidden redelegation"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment finished.snapshot)
    let grandchild : Capability .object :=
      { bobCapability with
        id := ⟨45⟩
        parent := some bobCapability.id
        holder := .subject ⟨7⟩
        scope := { bobCapability.scope with maxCost := 40000 }
        notBefore := height + 5
        notAfter := 40
        ancestors := {ownerCapId, bobCapability.id} }
    let forbiddenDraft : CapabilityDelegationController.Command .object :=
      { subject := ⟨8⟩, nonce := 1303, expectedTargetRoot := finishedObject.payload.root,
        declaration := ⟨grandchild, bobCapability.id, ⟨targetId⟩, finishedAuthority.snapshot.cell.root, 0⟩ }
    let forbiddenMarker := CapabilityDelegationController.operationMarker deployment.domain profile.semantics forbiddenDraft
    let forbidden := { forbiddenDraft with declaration :=
      { forbiddenDraft.declaration with operationNullifier := forbiddenMarker } }
    let forbiddenAmbient : CapabilityDelegationController.Ambient := ⟨pins.federation, height + 5⟩
    let forbiddenRequest := CapabilityDelegationController.request finishedAuthority.snapshot profile.semantics forbiddenAmbient forbidden
    let forbiddenWire := CapabilityDelegationReceiver.ingressCodec.encode
      ⟨CapabilityDelegationController.commandCodec.encode ⟨.object, forbidden⟩,
        ← envelope signer finishedAuthority.snapshot forbiddenMarker ⟨.object, forbiddenRequest⟩ 8⟩
    match ← CapabilityDelegationReceiver.receiveLoaded deployment profile forbiddenAmbient native transport finished forbiddenWire with
    | .rejected .shape => pure ()
    | _ => throw (IO.userError "FAIL born resource: Bob redelegated without a delegate verb in his narrowed grant")
    match ← CapabilityDelegationReceiver.receive deployment profile ⟨pins.federation, 20000⟩ native transport delegationWire with
    | .confirmed .replayed receipt => require "delegation original receipt after expiry" (receipt == delegationReceipt)
    | _ => throw (IO.userError "FAIL born resource: original delegation replay after expiry")
    match ← DeclaredResourceController.receive deployment profile ⟨pins.federation, 20000⟩ native transport recipientWire with
    | .replayed _ => pure ()
    | _ => throw (IO.userError "FAIL born resource: original recipient replay after expiry")
    for (wire, expected) in [(firstInstall, firstReceipt), (secondInstall, secondReceipt)] do
      match ← PolicyInstallReceiver.receive profile deployment native transport pins.federation 20000 wire with
      | .confirmed .replayed receipt => require "original rule-update receipt after later updates and expiry" (receipt == expected)
      | _ => throw (IO.userError "FAIL born resource: historical installer replay after expiry")
    match ← CapabilityDelegationReceiver.receive deployment profile delegationAmbient native transport editedWire with
    | .transactionConflict => pure ()
    | _ => throw (IO.userError "FAIL born resource: changed delegation payload at same identity was not a conflict")
    require "all historical receipts and payload-conflict refusals preserve final exact image"
      (decide ((← requireOk "read final historical retries" (← transport.read)) = finishedBytes))
    IO.println "PASS born resource: native paid birth -> original owner invocation -> two rule replacements preserve owner/control grants and generation -> new law refuses old owner operation -> actual parent-authorized narrower Alice-to-Bob delegation -> Bob fresh signature/current revision invocation -> reopen; refused inputs and exact historical retries after expiry preserve durable image. Test keys and ZMod65537/scalar15 are fixture parameters."

end BornResourceInvocationProbe

def main (arguments : List String) : IO Unit :=
  match arguments with
  | [verifier, signer, store] => BornResourceInvocationProbe.run verifier signer store
  | _ => throw (IO.userError "usage: lean --run scripts/probe-born-resource-invocation.lean VERIFIER TEST-SIGNER SQLITE-STORE")
