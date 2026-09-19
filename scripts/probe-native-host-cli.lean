/-
Public-host acceptance through actual process commands. The runner records whether
the host process is a linked executable or an interpreted current-source entry. Fresh OpenSSL
Ed25519 custody stays in this temporary client fixture; the host receives only
public enrollment records and detached signatures. Every mutation goes through
the public CLI. Local administrator readback asserts the actual durable
state; it is not an unauthenticated resource-query API offered by the host.
-/
import Kernel.NativeHost
import Kernel.NativeHostGenesis
import Kernel.AgentGrain
import Kernel.ContentResource
import Kernel.CapabilityRevocationController
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

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def require (label : String) (condition : Bool) : IO Unit :=
  if condition then IO.println s!"PASS {label}"
  else throw (IO.userError s!"FAIL native host CLI: {label}")

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
  NativeHostGenesis.rootCapability config.profile genesis .program controlId ⟨7⟩ targetId
    {.installPolicy, .revokeCapability}

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

structure PublicView where
  challenge : NativeObservationCodec.Challenge
  header : CredentialSignedEnvelopeController.SignedHeader
  bytes : List UInt8

/-- Client command construction has no administrator store access. Its roots,
current source rules, grants and resource bytes arrive through the same signed
query path that an external owner uses. Administrator reads below are assertions. -/
def Client.query (client : Client) (label : String) (query : NativeObservationCodec.Query)
    (capability : CapabilityId) (custody : Custody) : IO PublicView := do
  let signedPath ← client.observeSigned label (.query query)
    [⟨query.kind, query.target, capability⟩] custody
  let signed ← need "canonical signed query"
    (NativeObservationCodec.signedCodec.decode (← IO.FS.readBinFile signedPath).toList)
  let [headerBytes] := signed.challenge.headers
    | throw (IO.userError "FAIL public query: expected one actual signing header")
  let header ← need "canonical query header"
    ((ResourceBirthCodec.strictCodec CredentialSignedEnvelopeController.headerCodec).decode headerBytes)
  let output := client.directory / s!"{label}-view.bin"
  client.command #["query", signedPath.toString, output.toString]
  pure ⟨signed.challenge, header, (← IO.FS.readBinFile output).toList⟩

def PublicView.object (view : PublicView) :
    IO (CellState.Materialized DeclaredEffectPageMaterializer.materializer) := do
  let (bytes, balances) ← need "source-owned object view"
    (NativeObservationController.resourceViewCodec.decode view.bytes)
  require "object view has no account balances" balances.isEmpty
  let packed ← need "canonical public object" (CanonicalCellRegistry.cellCodec.decode bytes)
  let ⟨.declaredObject, payload⟩ := packed
    | throw (IO.userError "FAIL public query: expected declared object")
  pure payload

def Client.signedWith (client : Client) (label : String) (draft : Draft) (custody : Custody)
    (grants : List NativeObservationCodec.GrantRef) :
    IO (System.FilePath × SigningPlan) := do
  let planPath := client.directory / s!"{label}-plan.bin"
  let signedPath ← client.observeSigned label (.prepare draft) grants custody
  client.command #["prepare", signedPath.toString, planPath.toString]
  let plan ← need "canonical CLI signing plan"
    (signingPlanCodec.decode (← IO.FS.readBinFile planPath).toList)
  require "host selects actual profile and deployment"
    (plan.domain == client.config.deployment.domain && plan.semantics == client.config.profile.semantics)
  pure (← client.assemble label plan custody, plan)

def Client.signed (client : Client) (label : String) (draft : Draft) (custody : Custody) :
    IO (System.FilePath × SigningPlan) := do
  let grants : List NativeObservationCodec.GrantRef := match draft with
    | .birth _ _ =>
        [⟨.object, client.config.deployment.factoryId,
          if custody.subject.value = 7 then ⟨54⟩ else ⟨55⟩⟩,
         ⟨.account, 7, ⟨41⟩⟩]
    | _ => [⟨.object, targetId, if custody.subject.value = 7 then ownerId else childId⟩]
  client.signedWith label draft custody grants

def Client.outcome (client : Client) (command : String) (call : System.FilePath) : IO Outcome := do
  let path := client.directory / s!"{command}-{call.fileName.getD "call"}-outcome.bin"
  client.command #[command, call.toString, path.toString]
  need "canonical CLI outcome" (outcomeCodec.decode (← IO.FS.readBinFile path).toList)

/-- The attacker controls only a scratch image. The live fixture store is
never temporarily disarmed, rewritten, or restored after a red proof. -/
def scratchImageRefused (client : Client) (image : DurableReceiver.Image)
    (label : String) (expectedSeed : Digest) : IO Unit := do
  require s!"{label}: malformed image remains physically replayable"
    (image.restore ResourceBirthCodec.rootBytes).isSome
  let bytes := DurableReceiverCodec.encode image
  let scratchConfig := { client.config with
    expectedSeed := expectedSeed
    storage := { client.config.storage with root := client.directory / s!"scratch-{label}" } }
  let observation ← scratchConfig.storage.cas none bytes
  match observation with
  | .installed => pure ()
  | _ => throw (IO.userError s!"FAIL {label}: scratch image was not installed")
  let settings := client.directory / s!"scratch-{label}.json"
  IO.FS.writeFile settings (settingsJson scratchConfig).pretty
  let output ← runProcess client.host #[settings.toString, "describe"]
  require s!"{label}: real public open refuses malformed semantics"
    (output.exitCode != 0 && output.stdout == "")
  let actual ← IO.ofExcept (← scratchConfig.storage.read)
  require s!"{label}: refused open never mutates scratch image" (decide (actual = some bytes))

def forgedHistoryRefused (client : Client) (image : DurableReceiver.Image)
    (label : String) (edit : DurableReceiver.IntentRecord → DurableReceiver.IntentRecord) : IO Unit := do
  let first :: rest := image.accepted
    | throw (IO.userError "FAIL replay tooth: expected actual accepted history")
  scratchImageRefused client { image with accepted := edit first :: rest }
    label client.config.expectedSeed

def hiddenBookRefused (client : Client) (image : DurableReceiver.Image)
    (genesis : NativeHostGenesis.Config) : IO Unit := do
  let hiddenAccount := 123456789
  require "malformed Book fixture account is absent"
    (decide (hiddenAccount ∉ genesis.initialBook.accounts))
  let hidden := { genesis.initialBook with
    balances := genesis.initialBook.balances + DFinsupp.single (hiddenAccount, genesis.tariff.asset) 1 }
  let cell : PackedCell CanonicalCellRegistry.registry := ⟨.resourceBook,
    materialize CanonicalResourcePageMaterializer.materializer
      (CanonicalResourcePageMaterializer.stateOfOption (some hidden))⟩
  let bytes := ResourceBirthCodec.LifecycleImage.bytes _ (.live cell)
  let seed := { image.seed with cells := image.seed.cells.map fun (identifier, original) =>
    (identifier, if identifier.value = client.config.deployment.resourceBookId then bytes else original) }
  -- Pin this scratch seed explicitly so refusal tests the actual Book law,
  -- rather than merely hitting the independent genesis-identity check.
  scratchImageRefused client ⟨seed, []⟩ "hidden-unregistered-balance" (NativeHost.seedIdentity seed)

def installed (label : String) : Outcome → IO Receipt
  | .confirmed .installed receipt => do
      IO.println s!"PASS installed event {receipt.acceptedCount}: {label}"
      pure receipt
  | .refused phase detail => throw (IO.userError s!"FAIL {label}: {phase} {detail}")
  | _ => throw (IO.userError s!"FAIL {label}: not installed")

def replayed (label : String) (original : Receipt) : Outcome → IO Unit
  | .confirmed .replayed receipt => require label (receipt == original)
  | _ => throw (IO.userError s!"FAIL {label}: did not return original replay receipt")

/-- Fail delivery after the real host commits, then recover solely from the
retained signed call. The missing output parent is local test scaffolding;
neither the receiver nor storage is modified. -/
def committedWithoutReply (client : Client) (call : System.FilePath) : IO Receipt := do
  let missingParent := client.directory / "missing-reply-parent"
  require "lost-reply fixture output parent is absent" (!(← missingParent.pathExists))
  let output := missingParent / "outcome.bin"
  let before ← client.physicalBytes
  let sent ← runProcess client.host
    #[client.settings.toString, "submit", call.toString, output.toString]
  require "caller receives failure and no outcome after submission"
    (sent.exitCode != 0 && !(← output.pathExists))
  let committed ← client.physicalBytes
  require "actual durable commit occurred before reply delivery failed" (before != committed)
  let receipt ← match ← client.outcome "lookup" call with
    | .confirmed .replayed receipt => pure receipt
    | _ => throw (IO.userError "FAIL lost reply: exact lookup did not recover committed receipt")
  replayed "retry after undelivered reply returns recovered original receipt" receipt
    (← client.outcome "submit" call)
  require "lost-reply recovery never republishes or recharges"
    ((← client.physicalBytes) == committed)
  IO.println s!"PASS committed event {receipt.acceptedCount}: recovered after undelivered reply"
  pure receipt

def rejected (label : String) : Outcome → IO Unit
  | .refused phase detail =>
      IO.println s!"PASS refusal: {label}; canonical outcome {repr (outcomeCodec.encode (.refused phase detail))}"
  | _ => throw (IO.userError s!"FAIL {label}: did not refuse")

def invocation (client : Client) (custody : Custody) (capability : CapabilityId)
    (nonce : Nat) (before after : Int) : IO Draft := do
  let view ← client.query s!"invoke-{nonce}" ⟨.object, targetId, .resource⟩ capability custody
  let target ← view.object
  let command : DeclaredResourceController.Command :=
    { subject := custody.subject, expectedAuthorityRoot := view.header.authorityRoot,
      nonce := nonce, targets := [
        { kind := .object, target := targetId,
          capability := capability, observeCapability := none,
          schemaVersion := 1, expectedTargetRoot := target.root,
          payload := .scalar [.write (.objectField ⟨targetId⟩ ⟨1⟩) (some before) after]}] }
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

def installDraft (client : Client) (custody : Custody) (nonce : Nat) (rule : PolicyRecord) : IO Draft := do
  let view ← client.query s!"policy-{nonce}" ⟨.object, targetId, .policy⟩ ownerId custody
  let current ← need "canonical queried current policy" (PolicyRecordCodec.decode view.bytes)
  let declaration : PolicyInstallController.Declaration :=
    ⟨view.header.authorityRoot, some ⟨current.version, PolicyRecordCodec.digest current⟩, nonce, rule⟩
  pure (.install custody.subject controlId (PolicyInstallController.declarationCodec.encode declaration))

def delegationDraft (client : Client) (custody : Custody) :
    IO (Draft × Capability .object) := do
  let view ← client.query "delegation-object" ⟨.object, targetId, .resource⟩ ownerId custody
  let target ← view.object
  let grantView ← client.query "delegation-parent" ⟨.object, targetId, .capability⟩ ownerId custody
  require "resource and parent queries use one image"
    (view.challenge.imageBoundary == grantView.challenge.imageBoundary)
  let stored ← need "canonical queried parent grant"
    ((ResourceBirthCodec.strictCodec
      (CredentialAuthorityEntryCodec.storedCapabilityStream .object).toLawful).decode grantView.bytes)
  let parent := stored.head
  let child : Capability .object :=
    { parent with
      id := childId
      parent := some ownerId
      holder := .subject ⟨8⟩
      scope := ⟨{⟨targetId⟩}, {.observeObject, .mutateObject}, 50000⟩
      notBefore := view.challenge.height
      notAfter := client.config.genesisHeight + 5
      ancestors := {ownerId} }
  let draft : CapabilityDelegationController.Command .object :=
    { subject := custody.subject, nonce := 15001, expectedTargetRoot := target.root,
      declaration := ⟨child, ownerId, ⟨targetId⟩, view.header.authorityRoot, 0⟩ }
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
    let birthReceipt ← installed "public birth" (← client.outcome "submit" birth)
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
    let (ownerCall, _) ← client.signed "owner" (← invocation client alice ownerId 14002 0 1) alice
    let ownerReceipt ← installed "public owner invocation" (← client.outcome "submit" ownerCall)
    let rule1 := nextRule client 1 (PolicyRecordCodec.digest (initialRule cfg source)) false
    let (install1, _) ← client.signed "rule-1" (← installDraft client alice 14003 rule1) alice
    let receipt1 ← installed "first public rule update" (← client.outcome "submit" install1)
    let once ← client.open
    require "rule replacement preserves grants and increments only revision"
      (once.authority.snapshot.authState.policyEpoch ⟨targetId⟩ == 0 &&
       once.authority.snapshot.authState.policyRevision ⟨targetId⟩ == 1 &&
       decide (readCapability once.authority.snapshot.cell .object ownerId = some ⟨owner cfg source, []⟩) &&
       decide (readCapability once.authority.snapshot.cell .program controlId = some ⟨control cfg source, []⟩))
    let beforeRefusal ← client.physicalBytes
    let (denied, _) ← client.signed "new-law-denies-owner"
      (← invocation client alice ownerId 14004 1 2) alice
    rejected "new law applies to retained owner grant" (← client.outcome "submit" denied)
    require "policy refusal leaves physical bytes unchanged" ((← client.physicalBytes) == beforeRefusal)
    let rule2 := nextRule client 2 (PolicyRecordCodec.digest rule1) true
    let (install2, _) ← client.signed "rule-2" (← installDraft client alice 14005 rule2) alice
    let receipt2 ← installed "same original controller changes rules again" (← client.outcome "submit" install2)
    let (delegation, child) ← delegationDraft client alice
    let (delegate, _) ← client.signed "delegate" delegation alice
    let delegationReceipt ← installed "actual Alice to Bob delegation" (← client.outcome "submit" delegate)
    let delegated ← client.open
    let stored ← need "actual received child" (readCapability delegated.authority.snapshot.cell .object childId)
    require "canonical current lineage and exact narrow child"
      (decide (stored.head = child) && CredentialLineageAdmission.storedLineageCheck delegated.authority.snapshot.cell stored)
    let recipientDraft ← invocation client bob childId 15002 1 2
    let beforeWrongSigner ← client.physicalBytes
    let (recipient, recipientPlan) ← client.signed "recipient" recipientDraft bob
    let wrongSigner ← client.assemble "wrong-recipient-signature" recipientPlan alice
    rejected "Alice cannot sign Bob's received grant" (← client.outcome "submit" wrongSigner)
    require "signature refusal leaves physical bytes unchanged" ((← client.physicalBytes) == beforeWrongSigner)
    require "clock derives from accepted history only" (recipientPlan.height == cfg.genesisHeight + 5)
    let recipientReceipt ← installed "public Bob invocation" (← client.outcome "submit" recipient)
    let finished ← client.open
    require "reopen verifies history at its original height after child expiry"
      (child.notAfter < NativeHost.logicalHeight cfg finished.durable)
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
    hiddenBookRefused client finished.durable.image source
    forgedHistoryRefused client finished.durable.image "unknown-ingress"
      (fun record => { record with event := { record.event with canonicalBytes := [255] } })
    forgedHistoryRefused client finished.durable.image "changed-event"
      (fun record => { record with event := { record.event with eventId := ⟨record.event.eventId.value + 1⟩ } })
    forgedHistoryRefused client finished.durable.image "changed-charge"
      (fun record => { record with exactCharge :=
        (fun lane => record.exactCharge lane + (if lane = .proofWork then 1 else 0)) })
    for (call, original) in [(birth, birthReceipt), (ownerCall, ownerReceipt), (install1, receipt1),
        (install2, receipt2), (delegate, delegationReceipt), (recipient, recipientReceipt)] do
      replayed "fresh-process historical lookup" original (← client.outcome "lookup" call)
      replayed "fresh-process exact retry" original (← client.outcome "submit" call)
    let malformed := directory / "malformed.bin"
    IO.FS.writeBinFile malformed ((← IO.FS.readBinFile recipient) ++ [0].toByteArray)
    rejected "noncanonical outer frame" (← client.outcome "submit" malformed)
    require "all restarted receipt lookups/retries/refusals preserve exact final bytes"
      ((← client.physicalBytes) == finalBytes)
    IO.println "PASS public host CLI: fresh external Ed25519 custody; source genesis/bootstrap; prepare/sign/assemble/submit birth; original owner invocation; two rule changes retain grants; narrowed Bob delegation and current-rule invocation; process restart lookup/exact retry; policy/signature/encoding refusals; exact conserved Book and unchanged replay image. BabyBear/scalar29 native execution, no succinct-proof or chain-funds claim."

/-! The New World cycle uses the same public client boundary. Administrator
access creates genesis, asserts the resulting SQLite image, and constructs one
explicitly marked adversarial signing plan after observation is denied. Every
mutation is externally signed and submitted to a fresh public host process;
the fixture never bypasses receiving admission. Artifacts are retained. -/

namespace NewWorld

open Minidregg.Theory.Hyperdocument

def taskId : Nat := 1600
def contentId : Nat := 1601
def taskOwner : CapabilityId := ⟨161⟩
def taskControl : CapabilityId := ⟨162⟩
def taskWorker : CapabilityId := ⟨163⟩
def contentOwner : CapabilityId := ⟨164⟩
def contentControl : CapabilityId := ⟨165⟩
def contentWorker : CapabilityId := ⟨166⟩
def atomId : AtomId := ⟨⟨1700⟩⟩

def ordinaryGrant (config : NativeHost.Config) (genesis : NativeHostGenesis.Config)
    (identifier : CapabilityId) (target : Nat) : Capability .object :=
  NativeHostGenesis.rootCapability config.profile genesis .object identifier ⟨7⟩ target
    (ResourceBirthPolicyController.Concrete.ownerVerbs .object)

def managementGrant (config : NativeHost.Config) (genesis : NativeHostGenesis.Config)
    (identifier : CapabilityId) (target : Nat) : Capability .program :=
  NativeHostGenesis.rootCapability config.profile genesis .program identifier ⟨7⟩ target
    {.installPolicy, .revokeCapability}

def ownerManagement : Minidregg.Pred.Pred := .eq "request/subject" 7

/-- Observation still requires its own native capability. A participant may
publish content only in a joint generation-one task operation. -/
def contentPolicy : Minidregg.Pred.Pred := .any [
  .memberOf "request/verb" [1,3],
  .all [.eq "request/subject" 7,
    .memberOf "request/verb" [2,4,
      Int.ofNat (CredentialAuthorityEntryCodec.verbTag (.revokeCapability))]],
  .all [.eq "request/subject" 8, .eq "request/verb" 2,
    .eq s!"joint/target/{taskId}/resource/field/0/before" 1,
    .eq s!"joint/target/{taskId}/resource/field/0/after" 1]]

def taskPolicy : Minidregg.Pred.Pred := .all [AgentGrain.policy ownerManagement,
  .any [.eq "request/subject" 7, .memberOf "request/verb" [1,3],
    .all [.eq "request/subject" 8, AgentGrain.executionCaveat 1]]]

def birth (config : NativeHost.Config) (genesis : NativeHostGenesis.Config) : Draft :=
  let identity := ResourceBirthController.Concrete.sourceIdentity config.profile.compilerProfile
    config.deployment ⟨7⟩ 30001
  let task : PackedCell CanonicalCellRegistry.registry := ⟨.declaredObject,
    CellState.materialize DeclaredEffectPageMaterializer.materializer
      (DeclaredEffectPageMaterializer.stateOfOption
        (some (AgentGrain.initialPage config.deployment.domain taskId 100)))⟩
  let content : PackedCell CanonicalCellRegistry.registry := ⟨.content,
    CellState.materialize HyperdocumentContentPageMaterializer.materializer
      (HyperdocumentContentPageMaterializer.stateOfOption
        (some (ContentResource.initialPage config.deployment.domain contentId)))⟩
  let policies := [NativeHostGenesis.policy config.profile genesis taskId taskPolicy,
    NativeHostGenesis.policy config.profile genesis contentId contentPolicy]
  let descriptor : Descriptor CanonicalCellRegistry.registry :=
    { factory := ⟨config.deployment.factoryId⟩, creator := ⟨7⟩,
      transactionId := identity, nonce := 30001,
      births := [⟨⟨taskId, CellSlot.root CanonicalCellRegistry.registry .absent, task⟩, .object, ⟨7⟩⟩,
        ⟨⟨contentId, CellSlot.root CanonicalCellRegistry.registry .absent, content⟩, .object, ⟨7⟩⟩],
      auxiliaryCreates := [],
      grants := [⟨.object, ⟨ordinaryGrant config genesis taskOwner taskId, []⟩⟩,
        ⟨.program, ⟨managementGrant config genesis taskControl taskId, []⟩⟩,
        ⟨.object, ⟨ordinaryGrant config genesis contentOwner contentId, []⟩⟩,
        ⟨.program, ⟨managementGrant config genesis contentControl contentId, []⟩⟩],
      initialPolicies := policies.map fun rule =>
        ⟨rule.policyId, PolicyRecordCodec.digest rule, PolicyRecordCodec.encode rule⟩,
      authorityNullifier := identity.value, funding := [],
      fee := ⟨7, config.tariff.collector, config.tariff.asset, 0⟩ }
  let priced := { descriptor with fee := { descriptor.fee with amount := descriptor.quotedFee config.tariff } }
  .birth (CanonicalCellRegistry.sourceEncoding.codec.encode priced) [⟨41⟩]

def PublicView.packed (view : PublicView) : IO (PackedCell CanonicalCellRegistry.registry) := do
  let (bytes, balances) ← need "canonical resource view"
    (NativeObservationController.resourceViewCodec.decode view.bytes)
  require "task/content view has no hidden balances" balances.isEmpty
  need "canonical resource bytes" (CanonicalCellRegistry.cellCodec.decode bytes)

def PublicView.content (view : PublicView) : IO HyperdocumentContentPageMaterializer.Page := do
  let ⟨.content, cell⟩ ← PublicView.packed view
    | throw (IO.userError "FAIL expected canonical content resource")
  need "actual typed content page" (HyperdocumentContentPageMaterializer.pageAt cell.logical)

def PublicView.task (view : PublicView) : IO AgentGrain.State := do
  let cell ← view.object
  let page ← need "actual task page" (DeclaredEffectPageMaterializer.pageAt cell.logical)
  need "actual source-authored task state" (AgentGrain.readState taskId page)

def atom (page : HyperdocumentContentPageMaterializer.Page) : IO AtomRecord :=
  need "existing exact atom record" (page.entries.findSome? fun entry => match entry with
    | .atom identifier record => if identifier == atomId then some record else none
    | _ => none)

def grants (custody : Custody) : List NativeObservationCodec.GrantRef :=
  [⟨.object, taskId, if custody.subject.value = 7 then taskOwner else taskWorker⟩,
   ⟨.object, contentId, if custody.subject.value = 7 then contentOwner else contentWorker⟩]

def challengeRefused (client : Client) (label : String)
    (purpose : NativeObservationCodec.Purpose) (selected : List NativeObservationCodec.GrantRef)
    (custody : Custody) : IO Unit := do
  let input := client.directory / s!"{label}-intent.bin"
  let output := client.directory / s!"{label}-challenge.bin"
  let intent : NativeObservationCodec.Intent := ⟨custody.subject, 39000 + label.length, purpose, selected⟩
  IO.FS.writeBinFile input (NativeObservationCodec.intentCodec.encode intent).toByteArray
  let result ← runProcess client.host
    #[client.settings.toString, "challenge", input.toString, output.toString]
  require label (result.exitCode != 0 && result.stdout == "" && !(← output.pathExists))

def joint (client : Client) (custody : Custody) (label : String) (nonce : Nat)
    (operation : AgentGrain.Operation) (text : String) (create : Bool := false)
    (contentFirst : Bool := false) : IO Draft := do
  let taskGrant := if custody.subject.value = 7 then taskOwner else taskWorker
  let contentGrant := if custody.subject.value = 7 then contentOwner else contentWorker
  let taskView ← client.query (label ++ "-task") ⟨.object, taskId, .resource⟩ taskGrant custody
  let contentView ← client.query (label ++ "-content") ⟨.object, contentId, .resource⟩ contentGrant custody
  require "joint authoring observes one exact image"
    (taskView.challenge.imageBoundary == contentView.challenge.imageBoundary)
  let before ← PublicView.task taskView
  let page ← PublicView.content contentView
  let edit : ContentResource.Action ← if create then pure (.createAtom atomId .text text.toUTF8.toList)
    else do
      let previous ← atom page
      pure (.editAtom ⟨atomId, previous, .text, text.toUTF8.toList, false⟩)
  let taskCell ← PublicView.packed taskView
  let contentCell ← PublicView.packed contentView
  let command : DeclaredResourceController.Command :=
    operation.command custody.subject taskView.header.authorityRoot nonce taskId taskGrant
      taskCell.payload.root before [
        {kind := .object, target := contentId, capability := contentGrant, schemaVersion := 1,
         observeCapability := some contentGrant,
         expectedTargetRoot := contentCell.payload.root, payload := .content ⟨[edit]⟩}]
      (some taskGrant)
  let command := if contentFirst then {command with targets := command.targets.reverse} else command
  pure (.invoke (DeclaredResourceController.commandCodec.encode command))

def taskOnly (client : Client) (custody : Custody) (label : String) (nonce : Nat)
    (operation : AgentGrain.Operation) : IO Draft := do
  let capability := if custody.subject.value = 7 then taskOwner else taskWorker
  let view ← client.query (label ++ "-task") ⟨.object, taskId, .resource⟩ capability custody
  let before ← PublicView.task view
  let packed ← PublicView.packed view
  let command := operation.command custody.subject view.header.authorityRoot nonce taskId
    capability packed.payload.root before
  pure (.invoke (DeclaredResourceController.commandCodec.encode command))

/-- Hostile wire mutation retains the legitimate mutation signatures and
exact command. Only required read witnesses are removed. No fixture kernel or
administrator preparation path participates. -/
def omitReadWitnesses (client : Client) (original : System.FilePath) : IO System.FilePath := do
  let call ← need "canonical signed joint call"
    (callCodec.decode (← IO.FS.readBinFile original).toList)
  let .invoke ingress := call | throw (IO.userError "FAIL expected signed invocation")
  require "real joint signing plan includes both source-bound read witnesses"
    (ingress.observeEnvelopes.length == 2)
  let path := client.directory / "missing-read-witnesses-call.bin"
  IO.FS.writeBinFile path (callCodec.encode (.invoke {ingress with observeEnvelopes := []})).toByteArray
  pure path

def wrongContentReadGrant (draft : Draft) : IO Draft := do
  let .invoke bytes := draft | throw (IO.userError "FAIL expected invocation draft")
  let command ← need "canonical authored joint command" (DeclaredResourceController.commandCodec.decode bytes)
  let changed := {command with
    nonce := 30014,
    targets := command.targets.map fun target => if target.target = contentId then
      {target with observeCapability := some contentOwner} else target}
  pure (.invoke (DeclaredResourceController.commandCodec.encode changed))

/-- An arbitrary direct caller can submit malformed or guessed expected
records. This variant deliberately retains the earlier signatures; if it got
past the stale-record check those signatures would also fail. The assertion is
public error-byte uniformity, not successful authorization of this variant. -/
def staleContentGuess (client : Client) (original : System.FilePath) : IO System.FilePath := do
  let call ← need "canonical hostile input base" (callCodec.decode (← IO.FS.readBinFile original).toList)
  let .invoke ingress := call | throw (IO.userError "FAIL expected joint base")
  let command ← need "canonical hostile command base"
    (DeclaredResourceController.commandCodec.decode ingress.commandBytes)
  let changed := {command with nonce := 30017, targets := command.targets.map fun target =>
    match target.payload with
    | .content content => {target with payload := .content ⟨content.actions.map fun action =>
        match action with
        | .editAtom edit => .editAtom {edit with before := {edit.before with payload := [255]}}
        | other => other⟩}
    | .scalar _ => target}
  let path := client.directory / "hidden-stale-content-guess-call.bin"
  IO.FS.writeBinFile path (callCodec.encode (.invoke
    {ingress with commandBytes := DeclaredResourceController.commandCodec.encode changed})).toByteArray
  pure path

def delegate (client : Client) (alice : Custody) (target : Nat)
    (parentId childId : CapabilityId) (nonce : Nat) : IO Draft := do
  let view ← client.query s!"delegate-{target}" ⟨.object, target, .resource⟩ parentId alice
  let parentView ← client.query s!"delegate-parent-{target}" ⟨.object, target, .capability⟩ parentId alice
  require "delegation observes one exact image"
    (view.challenge.imageBoundary == parentView.challenge.imageBoundary)
  let packed ← PublicView.packed view
  let stored ← need "canonical parent capability" ((ResourceBirthCodec.strictCodec
    (CredentialAuthorityEntryCodec.storedCapabilityStream .object).toLawful).decode parentView.bytes)
  let child : Capability .object := {stored.head with
    id := childId, parent := some parentId, holder := .subject ⟨8⟩,
    scope := ⟨{⟨target⟩}, {.observeObject, .mutateObject}, 50000⟩,
    notBefore := view.challenge.height, notAfter := client.config.genesisHeight + 100,
    ancestors := {parentId} }
  let command : CapabilityDelegationController.Command .object :=
    { subject := alice.subject, nonce := nonce, expectedTargetRoot := packed.payload.root,
      declaration := ⟨child, parentId, ⟨target⟩, view.header.authorityRoot, 0⟩ }
  let marker := CapabilityDelegationController.operationMarker client.config.deployment.domain
    client.config.profile.semantics command
  let command := {command with declaration := {command.declaration with operationNullifier := marker}}
  pure (.delegate (CapabilityDelegationController.commandCodec.encode ⟨.object, command⟩))

def revoke (client : Client) (alice : Custody) : IO Draft := do
  let view ← client.query "revoke-content" ⟨.object, contentId, .resource⟩ contentOwner alice
  let packed ← PublicView.packed view
  let command : CapabilityRevocationController.Command .object :=
    { subject := alice.subject, nonce := 30009, target := ⟨contentId⟩,
      victimKind := .object, capability := contentWorker, controlCapability := contentControl,
      expectedTargetRoot := packed.payload.root, expectedAuthorityRoot := view.header.authorityRoot }
  pure (.revoke (CapabilityRevocationController.commandCodec.encode ⟨.object, command⟩))

def installResource (client : Client) (alice : Custody) (target : Nat)
    (owner control : CapabilityId) (nonce : Nat)
    (predicate : Minidregg.Pred.Pred) : IO Draft := do
  let view ← client.query s!"rule-{nonce}" ⟨.object, target, .policy⟩ owner alice
  let current ← need "current installed resource law" (PolicyRecordCodec.decode view.bytes)
  let rule := {current with
    version := current.version + 1,
    previous := some (PolicyRecordCodec.digest current), predicate := predicate}
  pure (.install alice.subject control (PolicyInstallController.declarationCodec.encode
    ⟨view.header.authorityRoot, some ⟨current.version, PolicyRecordCodec.digest current⟩, nonce, rule⟩))

def installTask (client : Client) (alice : Custody) (nonce : Nat)
    (predicate : Minidregg.Pred.Pred) : IO Draft :=
  installResource client alice taskId taskOwner taskControl nonce predicate

/-- Adversarial fixture construction ONLY. The user-facing prepare gate should
refuse this hidden resource, so this test computes a complete fresh signing plan
from the operator's image using the same source definitions, then signs outside
the host and submits through the real public receiver. This tests that bypassing
public preparation cannot bypass the receiving read-law check. No production
endpoint or alternative admission implementation is introduced. -/
def offlineHiddenJoint (client : Client) (alice : Custody) : IO System.FilePath := do
  let opened ← client.open
  let task ← need "adversarial fixture task"
    (ResourceBirthController.Concrete.observeCell client.config.deployment opened.directory.directory
      taskId .declaredObject)
  let content ← need "adversarial fixture hidden content"
    (ResourceBirthController.Concrete.observeCell client.config.deployment opened.directory.directory
      contentId .content)
  let taskPage ← need "adversarial task page" (DeclaredEffectPageMaterializer.pageAt task.payload.logical)
  let before ← need "adversarial task state" (AgentGrain.readState taskId taskPage)
  let contentPage ← need "adversarial content page"
    (HyperdocumentContentPageMaterializer.pageAt content.payload.logical)
  let previous ← atom contentPage
  let operation : AgentGrain.Operation := .attach false
  let command := operation.command alice.subject opened.authority.snapshot.cell.root 30016
    taskId taskOwner task.payload.root before
    [{kind := .object, target := contentId, capability := contentOwner,
      observeCapability := some contentOwner, schemaVersion := 1,
      expectedTargetRoot := content.payload.root,
      payload := .content ⟨[.editAtom ⟨atomId, previous, .text,
        "HIDDEN CONTENT MUST NOT BECOME AN ORACLE".toUTF8.toList, false⟩]⟩}]
    (some taskOwner)
  let plan ← IO.ofExcept (NativeHost.prepareLoaded client.config opened
    (.invoke (DeclaredResourceController.commandCodec.encode command)))
  client.assemble "offline-hidden-content-policy" plan alice

def run (host verifier store openssl directory : System.FilePath) : IO Unit := do
  let binary ← IO.FS.Handle.mk host .read
  let magic := (← binary.read 4).toList
  require "public host is a linked native executable, not an interpreter wrapper"
    (magic == [127,69,76,70] || magic == [207,250,237,254] || magic == [254,237,250,207] ||
      magic == [202,254,186,190] || magic == [202,254,186,191])
  require "acceptance artifact directory has no previous deployment"
    (!(← (directory / "pinned.json").pathExists))
  IO.FS.createDirAll directory
  let alice ← freshCustody openssl directory "alice" 7
  let bob ← freshCustody openssl directory "bob" 8
  let initial := hostConfig store verifier directory
  let genesis := genesisConfig initial alice bob
  let settings := directory / "initial.json"
  let pinnedSettings := directory / "pinned.json"
  let source := directory / "genesis-source.bin"
  let image := directory / "genesis.bin"
  IO.FS.writeFile settings (settingsJson initial).pretty
  IO.FS.writeBinFile source (NativeHostGenesis.configCodec.encode genesis).toByteArray
  processOk host #[settings.toString, "genesis", source.toString, image.toString, pinnedSettings.toString]
  let pinned ← IO.ofExcept (Json.parse (← IO.FS.readFile pinnedSettings))
  let expected ← IO.ofExcept (pinned.getObjValAs? Nat "expectedSeed")
  let config := {initial with expectedSeed := ⟨expected⟩}
  let client : Client := ⟨host, openssl, directory, pinnedSettings, config⟩
  client.command #["bootstrap", image.toString]
  let (birthCall, _) ← client.signedWith "cycle-birth" (birth config genesis) alice
    [⟨.object, config.deployment.factoryId, ⟨54⟩⟩, ⟨.account, 7, ⟨41⟩⟩]
  let birthReceipt ← installed "task and content birth" (← client.outcome "submit" birthCall)
  let afterBirth ← client.physicalBytes
  for kind in [.account, .program] do
    challengeRefused client s!"content-wrong-kind-{repr kind}"
      (.query ⟨kind, contentId, .resource⟩) [⟨kind, contentId, contentOwner⟩] alice
  for target in [config.deployment.resourceBookId, config.deployment.authorityCatalogueId] do
    challengeRefused client s!"internal-role-{target}"
      (.query ⟨.object, target, .resource⟩) [⟨.object, target, taskOwner⟩] alice
  let attachDraft ← joint client alice "attach" 30002 (.attach false) "A shared research room" true
  let correct := grants alice
  for (label, selected) in [("missing-joint-observation", correct.take 1),
      ("excess-joint-observation", correct ++ [⟨.account, 7, ⟨41⟩⟩]),
      ("duplicate-joint-observation", correct ++ correct.take 1),
      ("reordered-joint-observation", correct.reverse)] do
    challengeRefused client label (.prepare attachDraft) selected alice
  require "wrong kinds, internal roles and footprint refusals never change image"
    ((← client.physicalBytes) == afterBirth)
  let (attachCall, _) ← client.signedWith "cycle-attach"
    attachDraft alice (grants alice)
  let attachReceipt ← installed "atomic attach and typed content creation" (← client.outcome "submit" attachCall)
  let (taskDelegation, _) ← client.signedWith "cycle-task-delegation"
    (← delegate client alice taskId taskOwner taskWorker 30003)
    alice [⟨.object, taskId, taskOwner⟩]
  let _ ← installed "task worker delegation" (← client.outcome "submit" taskDelegation)
  let (contentDelegation, _) ← client.signedWith "cycle-content-delegation"
    (← delegate client alice contentId contentOwner contentWorker 30004)
    alice [⟨.object, contentId, contentOwner⟩]
  let _ ← installed "content participant delegation" (← client.outcome "submit" contentDelegation)
  let (updatedCall, _) ← client.signedWith "cycle-retained-grants"
    (← installTask client alice 30005 taskPolicy) alice [⟨.object, taskId, taskOwner⟩]
  let _ ← installed "task law revision preserves grants" (← client.outcome "submit" updatedCall)
  let updated ← client.open
  require "task revision leaves grant generation unchanged"
    (updated.authority.snapshot.authState.policyEpoch ⟨taskId⟩ == 0 &&
      updated.authority.snapshot.authState.policyRevision ⟨taskId⟩ == 1)
  require "original owner and control grants survive replacement"
    (decide (readCapability updated.authority.snapshot.cell .object taskOwner =
      some ⟨ordinaryGrant config genesis taskOwner taskId, []⟩) &&
      decide (readCapability updated.authority.snapshot.cell .program taskControl =
        some ⟨managementGrant config genesis taskControl taskId, []⟩))
  let reserveDraft ← joint client bob "reserve" 30006 (.reserve 40) "Bob is researching"
  let (reserveCall, _) ← client.signedWith "cycle-reserve" reserveDraft bob (grants bob)
  let beforeReadAttacks ← client.physicalBytes
  let missingReadCall ← omitReadWitnesses client reserveCall
  rejected "direct submit without joint read witnesses is refused"
    (← client.outcome "submit" missingReadCall)
  let (wrongReadCall, _) ← client.signedWith "cycle-wrong-read-grant"
    (← wrongContentReadGrant reserveDraft) bob (grants bob)
  rejected "direct submit cannot use Alice's content read grant as Bob"
    (← client.outcome "submit" wrongReadCall)
  require "both direct read-authority attacks preserve complete physical image"
    ((← client.physicalBytes) == beforeReadAttacks)
  let reserveReceipt ← committedWithoutReply client reserveCall
  let beforeRefusal ← client.physicalBytes
  let (badCall, _) ← client.signedWith "cycle-invalid-leg"
    (← joint client bob "invalid" 30007 (.settle (-1)) "THIS MUST NOT APPEAR" false true) bob (grants bob).reverse
  rejected "invalid second task leg rejects otherwise valid first content edit" (← client.outcome "submit" badCall)
  require "joint refusal preserves whole durable image" ((← client.physicalBytes) == beforeRefusal)
  let (settleCall, _) ← client.signedWith "cycle-settle"
    (← joint client bob "settle" 30008 (.settle 30) "Research result: exact typed bytes") bob (grants bob)
  let settleReceipt ← installed "participant atomically settles and publishes result"
    (← client.outcome "submit" settleCall)
  let (disconnectCall, _) ← client.signedWith "cycle-hard-disconnect"
    (← taskOnly client alice "hard-disconnect" 30012 .disconnect)
    alice [⟨.object, taskId, taskOwner⟩]
  let disconnectReceipt ← installed "hard disconnect advances task execution generation"
    (← client.outcome "submit" disconnectCall)
  let disconnected ← client.physicalBytes
  let (staleWorkerCall, _) ← client.signedWith "cycle-stale-worker"
    (← taskOnly client bob "stale-worker" 30013 (.reserve 1))
    bob [⟨.object, taskId, taskWorker⟩]
  rejected "freshly signed old worker is fenced by current task law"
    (← client.outcome "submit" staleWorkerCall)
  require "fenced worker creates no durable event" ((← client.physicalBytes) == disconnected)
  let (revokeCall, _) ← client.signedWith "cycle-revoke" (← revoke client alice)
    alice [⟨.object, contentId, contentOwner⟩]
  let _ ← installed "actual source-owned participant revocation" (← client.outcome "submit" revokeCall)
  let revoked ← client.open
  require "revocation is recorded in the canonical authority plane"
    (decide (.capability contentWorker ∈ revoked.authority.snapshot.authState.revoked))
  require "nine accepted events before lock; failed operations have no history"
    (revoked.durable.image.accepted.length == 9)
  let book ← need "actual conserved Book after mixed-resource journey"
    (ResourceBirthController.Concrete.observeCell config.deployment revoked.directory.directory
      config.deployment.resourceBookId .resourceBook)
  let balances := CanonicalResourceKernel.logicalBook book.payload.logical
  require "two-resource birth is charged once with conserved synthetic supply"
    (balances.balance 7 0 == 89 && balances.balance 8 0 == 200 &&
      balances.balance 99 0 == 11 && balances.balance 0 0 == -300 && balances.totalAsset 0 == 0)
  let revokedImage ← client.physicalBytes
  let deniedQuery ← client.observeSigned "revoked-bob"
    (.query ⟨.object, contentId, .resource⟩) [⟨.object, contentId, contentWorker⟩] bob
  let deniedOutput := directory / "revoked-bob-view.bin"
  let refusal ← runProcess host #[pinnedSettings.toString, "query", deniedQuery.toString, deniedOutput.toString]
  require "revoked participant cannot freshly observe content"
    (refusal.exitCode != 0 && !(← deniedOutput.pathExists))
  require "revoked fresh request leaves image unchanged" ((← client.physicalBytes) == revokedImage)
  let finalTask ← PublicView.task (← client.query "final-task" ⟨.object, taskId, .resource⟩ taskOwner alice)
  let finalContent ← PublicView.content (← client.query "final-content" ⟨.object, contentId, .resource⟩ contentOwner alice)
  require "paused task retains exact settled budget at the new generation"
    (decide (finalTask = ⟨2,0,70,0⟩))
  require "exact participant result bytes are committed"
    ((← atom finalContent).payload == "Research result: exact typed bytes".toUTF8.toList)
  for (call, receipt) in [(birthCall, birthReceipt), (attachCall, attachReceipt),
      (reserveCall, reserveReceipt), (settleCall, settleReceipt), (disconnectCall, disconnectReceipt)] do
    replayed "restarted lookup after revocation returns historical receipt" receipt (← client.outcome "lookup" call)
    replayed "restarted exact retry after revocation returns original receipt" receipt (← client.outcome "submit" call)
  require "historical retries never republish or recharge" ((← client.physicalBytes) == revokedImage)
  let (hideCall, _) ← client.signedWith "cycle-hide-content"
    (← installResource client alice contentId contentOwner contentControl 30015
      (.memberOf "request/verb" [2,3,4,5])) alice [⟨.object, contentId, contentOwner⟩]
  let _ ← installed "content law allows mutation but deliberately denies observation"
    (← client.outcome "submit" hideCall)
  let hiddenImage ← client.physicalBytes
  let hiddenQuery ← client.observeSigned "current-law-denies-read"
    (.query ⟨.object, contentId, .resource⟩) [⟨.object, contentId, contentOwner⟩] alice
  let hiddenOutput := directory / "hidden-content-view.bin"
  let hiddenRefusal ← runProcess host
    #[pinnedSettings.toString, "query", hiddenQuery.toString, hiddenOutput.toString]
  require "current resource law denies a grant that still contains observe scope"
    (hiddenRefusal.exitCode != 0 && !(← hiddenOutput.pathExists))
  let offlineCall ← offlineHiddenJoint client alice
  let deniedCurrentRead ← client.outcome "submit" offlineCall
  rejected "direct submit cannot expose content denied by its current observation law"
    deniedCurrentRead
  let guessedCall ← staleContentGuess client offlineCall
  let deniedGuess ← client.outcome "submit" guessedCall
  rejected "direct guessed expected-content record is refused" deniedGuess
  require "public refusal bytes do not distinguish guessed state from denied current observation"
    (outcomeCodec.encode deniedGuess == outcomeCodec.encode deniedCurrentRead)
  require "bypassing prepare does not bypass read laws or commit a foreign-policy probe"
    ((← client.physicalBytes) == hiddenImage)
  let lockRule : Minidregg.Pred.Pred := .eq "request/verb" 1
  let (lockCall, _) ← client.signedWith "cycle-lock-management"
    (← installTask client alice 30010 lockRule) alice [⟨.object, taskId, taskOwner⟩]
  let _ ← installed "resource deliberately locks its own management" (← client.outcome "submit" lockCall)
  let locked ← client.physicalBytes
  let (repairCall, _) ← client.signedWith "cycle-no-owner-bypass"
    (← installTask client alice 30011 taskPolicy) alice [⟨.object, taskId, taskOwner⟩]
  rejected "owner cannot bypass deliberately locked management" (← client.outcome "submit" repairCall)
  require "denied owner repair preserves exact durable image" ((← client.physicalBytes) == locked)
  let final ← client.open
  require "eleven accepted events; no refusal or retry adds history"
    (final.durable.image.accepted.length == 11)
  IO.FS.writeBinFile (directory / "final-image.bin") locked.toByteArray
  IO.FS.writeFile (directory / "summary.json") (Json.mkObj [
    ("result", toJson "PASS"), ("acceptedEvents", toJson final.durable.image.accepted.length),
    ("committedWithoutReplyRecovered", toJson true),
    ("semantics", toJson config.profile.semantics.value),
    ("fieldCharacteristic", toJson config.profile.characteristic),
    ("scalarOrderWidth", toJson NativeHostProfile.orderWidth),
    ("resourceCommandFrame", toJson (DeclaredResourceController.commandFrame.map UInt8.toNat)),
    ("domain", toJson config.deployment.domain.value),
    ("federation", toJson config.federation.value),
    ("genesisHeight", toJson config.genesisHeight),
    ("taskGeneration", toJson finalTask.generation), ("taskStatus", toJson finalTask.status),
    ("remainingPermissionUnits", toJson finalTask.remaining),
    ("reservedPermissionUnits", toJson finalTask.reserved),
    ("workerRestriction", toJson "Current per-subject resource law; no native Pred grant caveat"),
    ("privacyScope", toJson "Public refusal bytes; no timing noninterference claim"),
    ("assuranceScope", toJson "Native execution, fresh fixture keys and synthetic local genesis; no provider dispatch, physical interruption, succinct proof or real asset claim")]).pretty
  IO.println "PASS NEW WORLD CYCLE: fresh keys, BabyBear/scalar29, compiled public host, SQLite; task+typed content birth; atomic task/content mutation; participant grants survive rule revision; invalid leg rollback; exact result; hard-disconnect generation fence; real revocation; restarted historical retries; deliberate management lockout. Worker generation is an authored per-subject resource law, not a native Pred grant caveat. No provider dispatch, physical interruption, succinct proof, or real asset claim."

end NewWorld

end NativeHostCliProbe

def main (args : List String) : IO Unit := do
  match args with
  | [host, verifier, store, openssl] => NativeHostCliProbe.run host verifier store openssl
  | ["--new-world", host, verifier, store, openssl, directory] =>
      NativeHostCliProbe.NewWorld.run host verifier store openssl directory
  | _ => throw (IO.userError "usage: lean --run scripts/probe-native-host-cli.lean [--new-world] HOST VERIFIER SQLITE-STORE OPENSSL [ARTIFACT-DIRECTORY]")
