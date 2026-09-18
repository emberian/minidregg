/-
Compiled-host acceptance through actual process commands. Fresh OpenSSL
Ed25519 custody stays in this temporary client fixture; the host receives only
public enrollment records and detached signatures. Every mutation goes through
the compiled CLI. Local administrator readback asserts the actual durable
state; it is not an unauthenticated resource-query API offered by the host.
-/
import Kernel.NativeHost
import Kernel.NativeHostGenesis
import Compiler.NativeObservationCodec
import Kernel.NativeObservationController
import Lean.Data.Json

open Lean
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel

namespace NativeHostCliProbe

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL native host CLI: {label}")

def need {α : Type} (label : String) : Option α → IO α
  | none => throw (IO.userError s!"FAIL native host CLI: {label}")
  | some value => pure value

def runProcess (binary : System.FilePath) (arguments : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := binary.toString, args := arguments }

def processOk (binary : System.FilePath) (arguments : Array String) : IO Unit := do
  let output ← runProcess binary arguments
  unless output.exitCode == 0 do
    throw (IO.userError s!"FAIL process {binary}: exit {output.exitCode}: {output.stderr}")

structure Custody where
  privateKey : System.FilePath
  publicKey : List UInt8
  subject : SubjectId

def freshCustody (openssl directory : System.FilePath) (label : String) (subject : Nat) : IO Custody := do
  let privateKey := directory / s!"{label}.pem"
  let publicKey := directory / s!"{label}.der"
  processOk openssl #["genpkey", "-algorithm", "ED25519", "-out", privateKey.toString]
  processOk openssl #["pkey", "-in", privateKey.toString, "-pubout", "-outform", "DER", "-out", publicKey.toString]
  let bytes := (← IO.FS.readBinFile publicKey).toList
  require "actual Ed25519 SPKI public key" (bytes.length == 44 &&
    bytes.take 12 == [48, 42, 48, 5, 6, 3, 43, 101, 112, 3, 33, 0])
  pure ⟨privateKey, bytes.drop 12, ⟨subject⟩⟩

def sign (openssl directory : System.FilePath) (custody : Custody)
    (header : List UInt8) (index : Nat) : IO (List UInt8) := do
  let input := directory / s!"header-{index}.bin"
  let output := directory / s!"signature-{index}.bin"
  IO.FS.writeBinFile input header.toByteArray
  processOk openssl #["pkeyutl", "-sign", "-rawin", "-inkey", custody.privateKey.toString,
    "-in", input.toString, "-out", output.toString]
  let signature := (← IO.FS.readBinFile output).toList
  require "actual detached Ed25519 signature" (signature.length == 64)
  pure signature

def key (subject : Nat) (custody : Custody) : KeyRecord :=
  ⟨7000 + subject, 2, CredentialSignatureAdmission.ed25519Algorithm,
    subject, custody.publicKey, 0, 1000000, false⟩

def hostConfig (store verifier directory : System.FilePath) : NativeHost.Config where
  deployment := ⟨⟨8501⟩, 10, 11, 12⟩
  federation := ⟨9⟩
  template := ⟨⟨5⟩, 100000, 10000⟩
  tariff := ⟨3, 2, 1, 0, 99, 0⟩
  genesisHeight := 10
  expectedSeed := ⟨0⟩
  storage := ⟨store, directory / "store"⟩
  signature := ⟨verifier⟩

/-- Exercise the actual public JSON boundary; no private key occurs here. -/
def settingsJson (config : NativeHost.Config) : Json := Json.mkObj
  [("domain", toJson config.deployment.domain.value),
   ("federation", toJson config.federation.value),
   ("factoryId", toJson config.deployment.factoryId),
   ("resourceBookId", toJson config.deployment.resourceBookId),
   ("authorityCatalogueId", toJson config.deployment.authorityCatalogueId),
   ("issuer", toJson config.template.issuer.value), ("ownerBudget", toJson config.template.ownerBudget),
   ("lifetime", toJson config.template.lifetime), ("tariffBase", toJson config.tariff.base),
   ("tariffPerBirth", toJson config.tariff.perBirth), ("tariffPerGrant", toJson config.tariff.perGrant),
   ("tariffPerInitialPayloadByte", toJson config.tariff.perInitialPayloadByte),
   ("collector", toJson config.tariff.collector), ("asset", toJson config.tariff.asset),
   ("genesisHeight", toJson config.genesisHeight), ("expectedSeed", toJson config.expectedSeed.value),
   ("storageBinary", toJson config.storage.binary.toString),
   ("storageRoot", toJson config.storage.root.toString),
   ("signatureBinary", toJson config.signature.binary.toString)]

def genesisConfig (config : NativeHost.Config) (alice bob : Custody) : NativeHostGenesis.Config where
  deployment := config.deployment
  federation := config.federation
  tariff := config.tariff
  expectedSemantics := config.profile.semantics
  issuerEpoch := 2
  genesisHeight := config.genesisHeight
  factoryPredicate := .any
    [.eq "request/creator" 7,
     .all [.eq "request/verb" (Int.ofNat (CredentialAuthorityEntryCodec.verbTag (.observeObject))),
       .memberOf "request/subject" [7, 8]],
     .eq "request/subject" 7]
  enrollments :=
    [⟨key 7 alice, 7, ⟨41⟩, ⟨51⟩, ⟨54⟩, 100, .all []⟩,
     ⟨key 8 bob, 8, ⟨42⟩, ⟨52⟩, ⟨55⟩, 200, .all []⟩]
  factoryController := ⟨⟨7⟩, ⟨53⟩⟩
  meterAllowance := fun _ => 10000000

def targetId : Nat := 600
def ownerId : CapabilityId := ⟨61⟩
def controlId : CapabilityId := ⟨62⟩
def childId : CapabilityId := ⟨63⟩

def owner (config : NativeHost.Config) (genesis : NativeHostGenesis.Config) : Capability .object :=
  NativeHostGenesis.rootCapability config.profile genesis .object ownerId ⟨7⟩ targetId
    (ResourceBirthPolicyController.Concrete.ownerVerbs .object)

def control (config : NativeHost.Config) (genesis : NativeHostGenesis.Config) : Capability .program :=
  NativeHostGenesis.rootCapability config.profile genesis .program controlId ⟨7⟩ targetId {.installPolicy}

def initialRule (config : NativeHost.Config) (genesis : NativeHostGenesis.Config) : PolicyRecord :=
  NativeHostGenesis.policy config.profile genesis targetId (.memberOf "request/verb"
    [Int.ofNat (CredentialAuthorityEntryCodec.verbTag (.observeObject)),
     Int.ofNat (CredentialAuthorityEntryCodec.verbTag (.mutateObject)),
     Int.ofNat (CredentialAuthorityEntryCodec.verbTag (.delegateObject)),
     Int.ofNat (CredentialAuthorityEntryCodec.verbTag (.installPolicy))])

def birthDraft (config : NativeHost.Config) (genesis : NativeHostGenesis.Config) : Draft :=
  let identity := ResourceBirthController.Concrete.sourceIdentity config.profile.compilerProfile
    config.deployment ⟨7⟩ 14001
  let rule := initialRule config genesis
  let descriptor : Descriptor CanonicalCellRegistry.registry :=
    { factory := ⟨config.deployment.factoryId⟩, creator := ⟨7⟩,
      transactionId := identity, nonce := 14001,
      births := [⟨⟨targetId, CellSlot.root CanonicalCellRegistry.registry .absent,
        NativeHostGenesis.declaredCell genesis targetId false⟩, .object, ⟨7⟩⟩],
      auxiliaryCreates := [],
      grants := [⟨.object, ⟨owner config genesis, []⟩⟩, ⟨.program, ⟨control config genesis, []⟩⟩],
      initialPolicies := [⟨rule.policyId, PolicyRecordCodec.digest rule, PolicyRecordCodec.encode rule⟩],
      authorityNullifier := identity.value, funding := [],
      fee := ⟨7, config.tariff.collector, config.tariff.asset, 0⟩ }
  let priced := { descriptor with fee := { descriptor.fee with amount := descriptor.quotedFee config.tariff } }
  .birth (CanonicalCellRegistry.sourceEncoding.codec.encode priced) [⟨41⟩]

structure Client where
  host : System.FilePath
  openssl : System.FilePath
  directory : System.FilePath
  settings : System.FilePath
  config : NativeHost.Config

def Client.command (client : Client) (arguments : Array String) : IO Unit :=
  processOk client.host (#[client.settings.toString] ++ arguments)

def Client.open (client : Client) : IO (NativeHost.Opened client.config) :=
  return ← IO.ofExcept (← NativeHost.openExisting client.config)

def Client.physicalBytes (client : Client) : IO (List UInt8) := do
  let some bytes ← IO.ofExcept (← client.config.storage.read)
    | throw (IO.userError "FAIL CLI: expected initialized store")
  pure bytes

def Client.assemble (client : Client) (label : String) (plan : SigningPlan) (custody : Custody) :
    IO System.FilePath := do
  let planPath := client.directory / s!"{label}-plan.bin"
  let signaturesPath := client.directory / s!"{label}-signatures.bin"
  let callPath := client.directory / s!"{label}-call.bin"
  IO.FS.writeBinFile planPath (signingPlanCodec.encode plan).toByteArray
  let signatures ← (plan.slots.zipIdx).mapM fun (slot, index) =>
    sign client.openssl client.directory custody slot.header index
  let codec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
  IO.FS.writeBinFile signaturesPath (codec.encode signatures).toByteArray
  client.command #["assemble", planPath.toString, signaturesPath.toString, callPath.toString]
  pure callPath

def Client.observeSigned (client : Client) (label : String)
    (purpose : NativeObservationCodec.Purpose) (grants : List NativeObservationCodec.GrantRef)
    (custody : Custody) : IO System.FilePath := do
  let input := client.directory / s!"{label}-observe-intent.bin"
  let challengePath := client.directory / s!"{label}-observe-challenge.bin"
  let signaturePath := client.directory / s!"{label}-observe-signatures.bin"
  let signedPath := client.directory / s!"{label}-observe-signed.bin"
  let intent : NativeObservationCodec.Intent :=
    ⟨custody.subject, 20000 + label.length, purpose, grants⟩
  IO.FS.writeBinFile input (NativeObservationCodec.intentCodec.encode intent).toByteArray
  client.command #["challenge", input.toString, challengePath.toString]
  let challenge ← need "canonical public observation challenge"
    (NativeObservationCodec.challengeCodec.decode (← IO.FS.readBinFile challengePath).toList)
  require "challenge binds exact client intent/profile/domain"
    (decide (challenge.intent = intent) && challenge.domain == client.config.deployment.domain &&
      challenge.semantics == client.config.profile.semantics && challenge.federation == client.config.federation)
  let signatures ← (challenge.headers.zipIdx).mapM fun (header, index) =>
    sign client.openssl client.directory custody header index
  let signaturesCodec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
  IO.FS.writeBinFile signaturePath (signaturesCodec.encode signatures).toByteArray
  client.command #["observe-assemble", challengePath.toString, signaturePath.toString, signedPath.toString]
  pure signedPath

def Client.signed (client : Client) (label : String) (draft : Draft) (custody : Custody) :
    IO (System.FilePath × SigningPlan) := do
  let planPath := client.directory / s!"{label}-plan.bin"
  let grants : List NativeObservationCodec.GrantRef := match draft with
    | .birth _ _ =>
        [⟨.object, client.config.deployment.factoryId,
          if custody.subject.value = 7 then ⟨54⟩ else ⟨55⟩⟩,
         ⟨.account, 7, ⟨41⟩⟩]
    | _ => [⟨.object, targetId, if custody.subject.value = 7 then ownerId else childId⟩]
  let signedPath ← client.observeSigned label (.prepare draft) grants custody
  client.command #["prepare", signedPath.toString, planPath.toString]
  let plan ← need "canonical CLI signing plan"
    (signingPlanCodec.decode (← IO.FS.readBinFile planPath).toList)
  require "host selects actual profile and deployment"
    (plan.domain == client.config.deployment.domain && plan.semantics == client.config.profile.semantics)
  pure (← client.assemble label plan custody, plan)

def Client.outcome (client : Client) (command : String) (call : System.FilePath) : IO Outcome := do
  let path := client.directory / "outcome.bin"
  client.command #[command, call.toString, path.toString]
  need "canonical CLI outcome" (outcomeCodec.decode (← IO.FS.readBinFile path).toList)

/-- The attacker controls only a scratch image. The live fixture store is
never temporarily disarmed, rewritten, or restored after a red proof. -/
def forgedHistoryRefused (client : Client) (image : DurableReceiver.Image)
    (label : String) (edit : DurableReceiver.IntentRecord → DurableReceiver.IntentRecord) : IO Unit := do
  let first :: rest := image.accepted
    | throw (IO.userError "FAIL replay tooth: expected actual accepted history")
  let forged : DurableReceiver.Image := { image with accepted := edit first :: rest }
  require s!"{label}: forged history remains physically replayable"
    (forged.restore ResourceBirthCodec.rootBytes).isSome
  let bytes := DurableReceiverCodec.encode forged
  let scratchConfig := { client.config with
    storage := { client.config.storage with root := client.directory / s!"scratch-{label}" } }
  let observation ← scratchConfig.storage.cas none bytes
  match observation with
  | .installed => pure ()
  | _ => throw (IO.userError s!"FAIL {label}: scratch image was not installed")
  let settings := client.directory / s!"scratch-{label}.json"
  IO.FS.writeFile settings (settingsJson scratchConfig).pretty
  let output ← runProcess client.host #[settings.toString, "describe"]
  require s!"{label}: real public open refuses forged semantic history"
    (output.exitCode != 0 && output.stdout == "")
  let actual ← IO.ofExcept (← scratchConfig.storage.read)
  require s!"{label}: refused open never mutates scratch image" (decide (actual = some bytes))

def installed (label : String) : Outcome → IO Receipt
  | .confirmed .installed receipt => pure receipt
  | .refused phase detail => throw (IO.userError s!"FAIL {label}: {phase} {detail}")
  | _ => throw (IO.userError s!"FAIL {label}: not installed")

def replayed (label : String) (original : Receipt) : Outcome → IO Unit
  | .confirmed .replayed receipt => require label (receipt == original)
  | _ => throw (IO.userError s!"FAIL {label}: did not return original replay receipt")

def rejected (label : String) : Outcome → IO Unit
  | .refused _ _ => pure ()
  | _ => throw (IO.userError s!"FAIL {label}: did not refuse")

def invocation (client : Client) (subject : SubjectId) (capability : CapabilityId)
    (nonce : Nat) (before after : Int) : IO Draft := do
  let opened ← client.open
  let target ← need "actual invocation target"
    (ResourceBirthController.Concrete.observeCell client.config.deployment opened.directory.directory targetId .declaredObject)
  let command : DeclaredResourceController.Command :=
    { kind := .object, target := targetId, subject := subject, capability := capability,
      expectedAuthorityRoot := opened.authority.snapshot.cell.root, schemaVersion := 1,
      expectedTargetRoot := target.payload.root, nonce := nonce,
      actions := [.write (.objectField ⟨targetId⟩ ⟨1⟩) (some before) after] }
  pure (.invoke (DeclaredResourceController.commandCodec.encode command))

def nextRule (client : Client) (revision : Nat) (previous : Digest) (bobMayMutate : Bool) : PolicyRecord :=
  { policyId := ⟨targetId⟩, version := revision, domain := client.config.deployment.domain,
    semantics := client.config.profile.semantics, previous := some previous,
    predicate := .any
      [.all [.memberOf "request/verb"
          [Int.ofNat (CredentialAuthorityEntryCodec.verbTag (.observeObject))],
        .memberOf "request/subject" [7, 8]],
       .all [.memberOf "request/verb"
          [Int.ofNat (CredentialAuthorityEntryCodec.verbTag (.delegateObject)),
           Int.ofNat (CredentialAuthorityEntryCodec.verbTag (.installPolicy))],
        .eq "request/subject" 7],
       .all [.eq "request/verb" (Int.ofNat (CredentialAuthorityEntryCodec.verbTag (.mutateObject))),
         .eq "request/subject" (if bobMayMutate then 8 else 99)]] }

def installDraft (client : Client) (nonce : Nat) (rule : PolicyRecord) : IO Draft := do
  let opened ← client.open
  let declaration : PolicyInstallController.Declaration :=
    ⟨opened.authority.snapshot.cell.root, opened.authority.snapshot.currentHead rule.policyId, nonce, rule⟩
  pure (.install ⟨7⟩ controlId (PolicyInstallController.declarationCodec.encode declaration))

def delegationDraft (client : Client) (genesis : NativeHostGenesis.Config) :
    IO (Draft × Capability .object) := do
  let opened ← client.open
  let target ← need "actual delegation target"
    (ResourceBirthController.Concrete.observeCell client.config.deployment opened.directory.directory targetId .declaredObject)
  let parent := owner client.config genesis
  let child : Capability .object :=
    { parent with id := childId, parent := some ownerId, holder := .subject ⟨8⟩,
      scope := ⟨{⟨targetId⟩}, {.observeObject, .mutateObject}, 50000⟩,
      notBefore := NativeHost.logicalHeight client.config opened.durable,
      notAfter := 50, ancestors := {ownerId} }
  let draft : CapabilityDelegationController.Command .object :=
    { subject := ⟨7⟩, nonce := 15001, expectedTargetRoot := target.payload.root,
      declaration := ⟨child, ownerId, ⟨targetId⟩, opened.authority.snapshot.cell.root, 0⟩ }
  let marker := CapabilityDelegationController.operationMarker client.config.deployment.domain
    client.config.profile.semantics draft
  let command := { draft with declaration := { draft.declaration with operationNullifier := marker } }
  pure (.delegate (CapabilityDelegationController.commandCodec.encode ⟨.object, command⟩), child)

def run (host verifier store openssl : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let alice ← freshCustody openssl directory "alice" 7
    let bob ← freshCustody openssl directory "bob" 8
    let initial := hostConfig store verifier directory
    let source := genesisConfig initial alice bob
    let initialSettings := directory / "initial.json"
    let pinnedSettings := directory / "pinned.json"
    let sourcePath := directory / "source.bin"
    let genesisPath := directory / "genesis.bin"
    IO.FS.writeFile initialSettings (settingsJson initial).pretty
    IO.FS.writeBinFile sourcePath (NativeHostGenesis.configCodec.encode source).toByteArray
    let absent ← runProcess host #[initialSettings.toString, "describe"]
    require "ordinary open refuses absent genesis" (absent.exitCode != 0)
    processOk host #[initialSettings.toString, "genesis", sourcePath.toString,
      genesisPath.toString, pinnedSettings.toString]
    let pinned ← IO.ofExcept (Json.parse (← IO.FS.readFile pinnedSettings))
    let expected : Nat ← IO.ofExcept (pinned.getObjValAs? Nat "expectedSeed")
    let cfg := { initial with expectedSeed := ⟨expected⟩ }
    let client : Client := ⟨host, openssl, directory, pinnedSettings, cfg⟩
    client.command #["bootstrap", genesisPath.toString]
    let bootstrapBytes ← client.physicalBytes
    client.command #["bootstrap", genesisPath.toString]
    require "exact genesis initialization is idempotent" ((← client.physicalBytes) == bootstrapBytes)
    let ownQuery ← client.observeSigned "own-account"
      (.query ⟨.account, 7, .resource⟩) [⟨.account, 7, ⟨41⟩⟩] alice
    let ownViewPath := directory / "own-account-view.bin"
    client.command #["query", ownQuery.toString, ownViewPath.toString]
    let (ownPacked, ownBalances) ← need "source-owned protected resource view codec"
      (NativeObservationController.resourceViewCodec.decode (← IO.FS.readBinFile ownViewPath).toList)
    let ownCell ← need "own account view contains canonical selected cell"
      (CanonicalCellRegistry.cellCodec.decode ownPacked)
    require "authorized account view contains only Alice's exact asset cut"
      (ownCell.kind == .accountMetadata && decide (ownBalances = [(0, 100)]))
    let foreignQuery ← client.observeSigned "foreign-account"
      (.query ⟨.account, 8, .resource⟩) [⟨.account, 8, ⟨41⟩⟩] alice
    let foreignViewPath := directory / "foreign-account-view.bin"
    let foreignRefusal ← runProcess host
      #[pinnedSettings.toString, "query", foreignQuery.toString, foreignViewPath.toString]
    require "own account capability does not reveal Bob's account"
      (foreignRefusal.exitCode != 0 && foreignRefusal.stdout == "" && !(← foreignViewPath.pathExists))
    require "authorized/refused reads add no journal entry" ((← client.physicalBytes) == bootstrapBytes)
    let (birth, birthPlan) ← client.signed "birth" (birthDraft cfg source) alice
    require "genesis logical clock" (birthPlan.height == cfg.genesisHeight)
    let birthReceipt ← installed "compiled birth" (← client.outcome "submit" birth)
    let staleViewPath := directory / "stale-account-view.bin"
    let staleRefusal ← runProcess host
      #[pinnedSettings.toString, "query", ownQuery.toString, staleViewPath.toString]
    require "stale signed challenge refuses without a payload"
      (staleRefusal.exitCode != 0 && staleRefusal.stdout == "" && !(← staleViewPath.pathExists))
    require "unauthorized and stale observation refusals have one external diagnostic"
      (foreignRefusal.stderr == staleRefusal.stderr)
    let born ← client.open
    require "owner/control grants created by actual birth"
      (decide (readCapability born.authority.snapshot.cell .object ownerId = some ⟨owner cfg source, []⟩) &&
       decide (readCapability born.authority.snapshot.cell .program controlId = some ⟨control cfg source, []⟩))
    let (ownerCall, _) ← client.signed "owner" (← invocation client ⟨7⟩ ownerId 14002 0 1) alice
    let ownerReceipt ← installed "compiled owner invocation" (← client.outcome "submit" ownerCall)
    let rule1 := nextRule client 1 (PolicyRecordCodec.digest (initialRule cfg source)) false
    let (install1, _) ← client.signed "rule-1" (← installDraft client 14003 rule1) alice
    let receipt1 ← installed "first compiled rule update" (← client.outcome "submit" install1)
    let once ← client.open
    require "rule replacement preserves grants and increments only revision"
      (once.authority.snapshot.authState.policyEpoch ⟨targetId⟩ == 0 &&
       once.authority.snapshot.authState.policyRevision ⟨targetId⟩ == 1 &&
       decide (readCapability once.authority.snapshot.cell .object ownerId = some ⟨owner cfg source, []⟩) &&
       decide (readCapability once.authority.snapshot.cell .program controlId = some ⟨control cfg source, []⟩))
    let beforeRefusal ← client.physicalBytes
    let (denied, _) ← client.signed "new-law-denies-owner"
      (← invocation client ⟨7⟩ ownerId 14004 1 2) alice
    rejected "new law applies to retained owner grant" (← client.outcome "submit" denied)
    require "policy refusal leaves physical bytes unchanged" ((← client.physicalBytes) == beforeRefusal)
    let rule2 := nextRule client 2 (PolicyRecordCodec.digest rule1) true
    let (install2, _) ← client.signed "rule-2" (← installDraft client 14005 rule2) alice
    let receipt2 ← installed "same original controller changes rules again" (← client.outcome "submit" install2)
    let (delegation, child) ← delegationDraft client source
    let (delegate, _) ← client.signed "delegate" delegation alice
    let delegationReceipt ← installed "actual Alice to Bob delegation" (← client.outcome "submit" delegate)
    let delegated ← client.open
    let stored ← need "actual received child" (readCapability delegated.authority.snapshot.cell .object childId)
    require "canonical current lineage and exact narrow child"
      (decide (stored.head = child) && CredentialLineageAdmission.storedLineageCheck delegated.authority.snapshot.cell stored)
    let recipientDraft ← invocation client ⟨8⟩ childId 15002 1 2
    let beforeWrongSigner ← client.physicalBytes
    let (recipient, recipientPlan) ← client.signed "recipient" recipientDraft bob
    let wrongSigner ← client.assemble "wrong-recipient-signature" recipientPlan alice
    rejected "Alice cannot sign Bob's received grant" (← client.outcome "submit" wrongSigner)
    require "signature refusal leaves physical bytes unchanged" ((← client.physicalBytes) == beforeWrongSigner)
    require "clock derives from accepted history only" (recipientPlan.height == cfg.genesisHeight + 5)
    let recipientReceipt ← installed "compiled Bob invocation" (← client.outcome "submit" recipient)
    let finished ← client.open
    let object ← need "actual final object"
      (ResourceBirthController.Concrete.observeCell cfg.deployment finished.directory.directory targetId .declaredObject)
    let page ← need "actual final page" (DeclaredEffectPageMaterializer.pageAt object.payload.logical)
    require "actual object contains Bob's write"
      (decide (page.lookup (.objectField ⟨targetId⟩ ⟨1⟩) = some 2))
    let book ← need "actual final conserved Book"
      (ResourceBirthController.Concrete.observeCell cfg.deployment finished.directory.directory cfg.deployment.resourceBookId .resourceBook)
    let finalBook := CanonicalResourceKernel.logicalBook book.payload.logical
    require "single birth fee and exact conserved genesis supply"
      (finalBook.balance 7 0 == 93 && finalBook.balance 8 0 == 200 &&
       finalBook.balance 99 0 == 7 && finalBook.balance 0 0 == -300 && finalBook.totalAsset 0 == 0)
    require "six accepted mutations; refusals add no history" (finished.durable.image.accepted.length == 6)
    let finalBytes ← client.physicalBytes
    forgedHistoryRefused client finished.durable.image "unknown-ingress"
      (fun record => { record with event := { record.event with canonicalBytes := [255] } })
    forgedHistoryRefused client finished.durable.image "changed-event"
      (fun record => { record with event := { record.event with eventId := ⟨record.event.eventId.value + 1⟩ } })
    forgedHistoryRefused client finished.durable.image "changed-charge"
      (fun record => { record with exactCharge := fun lane =>
        record.exactCharge lane + if lane = .proofWork then 1 else 0 })
    for (call, original) in [(birth, birthReceipt), (ownerCall, ownerReceipt), (install1, receipt1),
        (install2, receipt2), (delegate, delegationReceipt), (recipient, recipientReceipt)] do
      replayed "fresh-process historical lookup" original (← client.outcome "lookup" call)
      replayed "fresh-process exact retry" original (← client.outcome "submit" call)
    let malformed := directory / "malformed.bin"
    IO.FS.writeBinFile malformed ((← IO.FS.readBinFile recipient) ++ [0].toByteArray)
    rejected "noncanonical outer frame" (← client.outcome "submit" malformed)
    require "all restarted receipt lookups/retries/refusals preserve exact final bytes"
      ((← client.physicalBytes) == finalBytes)
    IO.println "PASS compiled native CLI: fresh external Ed25519 custody; source genesis/bootstrap; prepare/sign/assemble/submit birth; original owner invocation; two rule changes retain grants; narrowed Bob delegation and current-rule invocation; process restart lookup/exact retry; policy/signature/encoding refusals; exact conserved Book and unchanged replay image. BabyBear/scalar29 native execution, no succinct-proof or chain-funds claim."

end NativeHostCliProbe

def main (args : List String) : IO Unit := do
  match args with
  | [host, verifier, store, openssl] => NativeHostCliProbe.run host verifier store openssl
  | _ => throw (IO.userError "usage: lean --run scripts/probe-native-host-cli.lean HOST VERIFIER SQLITE-STORE OPENSSL")
