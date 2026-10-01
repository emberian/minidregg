/-
# Explicit source-owned native host genesis

This is deployment administration, not a public mutation endpoint. The host
supplies its actual arithmetic/runtime profile and public enrollment records.
No test signer, private key, fixture identity, existing image, or caller-built
authority cell is accepted. The complete zero-history image is derived here.

Initial funds are exact mint postings against the named asset's issuer well;
meter allowance remains a separate resource quantity. Admission checks the
same canonical cell laws and the one-cell authority loader used by turns.
Key shape/enrollment is checked, not private-key possession or policy liveness.
A deliberately denying factory policy is valid deployment configuration.
-/
import Kernel.ResourceBirthPolicyController
import Theory.AssertAxioms

namespace Minidregg.Kernel.NativeHostGenesis

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

/-- A supplied public subject and its initial, explicitly budgeted account.
The account may differ from the subject; neither is inferred from key bytes. -/
structure Enrollment where
  key : KeyRecord
  accountId : Nat
  spendCapabilityId : CapabilityId
  controlCapabilityId : CapabilityId
  /-- Separate observe authority for private factory preparation. Birth or
  policy-control authority does not silently grant this read permission. -/
  factoryObserveCapabilityId : CapabilityId
  initialBalance : Nat
  /-- The account's actual law, also checked after explicit delegation. A
  subject-fixed law intentionally refuses another holder until updated. -/
  accountPredicate : Minidregg.Pred.Pred
  deriving DecidableEq, Repr

structure FactoryController where
  subject : SubjectId
  capabilityId : CapabilityId
  deriving DecidableEq, Repr

/-- A subject that advances the deployment's one clock cell, and the
identifier of its `C_tick`: a root capability on the clock cell
(`ClockCell.physicalId`) carrying the one verb `tickClock`
(`tickCapability`).  The clock cell's genesis law admits exactly these
subjects and that verb (`clockPredicate`), and the factory law refuses them
everything (`factoryLaw`): a ticker can advance the clock and do nothing else
(`clock_subject_confined`).  The operator's wall-clock ticker is one; a chain
observer that asserts chain time is another. -/
structure ClockTicker where
  subject : SubjectId
  capabilityId : CapabilityId
  deriving DecidableEq, Repr

structure Config where
  deployment : CanonicalCellRegistry.Deployment
  federation : FederationId
  tariff : CreationTariff
  expectedSemantics : Digest
  issuerEpoch : Minidregg.Theory.TypedAuthorization.Epoch
  genesisHeight : Height
  factoryPredicate : Minidregg.Pred.Pred
  enrollments : List Enrollment
  factoryController : FactoryController
  meterAllowance : ResourceCost.Charge
  /-- Every subject that may tick the clock.  Empty means the clock stays at
  genesis for the life of the deployment: the clock law admits no one. -/
  clockTickers : List ClockTicker

/-- Reuse the policy source's typed postfix language. No Boolean host policy
or parallel evaluator enters the genesis codec. -/
def predicateStream : StreamCodec Minidregg.Pred.Pred where
  encode predicate := (StreamCodec.list PolicyRecordCodec.tokenStream).encode
    (PolicyRecordCodec.encodePred predicate)
  decodePrefix bytes := do
    let (tokens, suffix) ← (StreamCodec.list PolicyRecordCodec.tokenStream).decodePrefix bytes
    let predicate ← PolicyRecordCodec.decodePred tokens
    some (predicate, suffix)
  decodePrefix_encode := by
    intro predicate suffix
    simp [(StreamCodec.list PolicyRecordCodec.tokenStream).decodePrefix_encode,
      PolicyRecordCodec.decodePred_encode]

def enrollmentStream : StreamCodec Enrollment :=
  StreamCodec.xmap
    (StreamCodec.product CredentialSigningKeyCodec.keyRecordStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
          (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
              (StreamCodec.product StreamCodec.nat predicateStream))))))
    (fun enrollment => (enrollment.key, enrollment.accountId,
      enrollment.spendCapabilityId, enrollment.controlCapabilityId,
      enrollment.factoryObserveCapabilityId, enrollment.initialBalance, enrollment.accountPredicate))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2.1, wire.2.2.2.2.2.2⟩)
    (by intro enrollment; cases enrollment; rfl)

/-- Finite transport over the existing public-key, predicate, and metering
codecs. Exact scalar arity is required, and the outer codec requires canonical
re-encoding; no optional coordinate acquires an implicit default. -/
abbrev ConfigWire :=
  List Nat × List PolicyRecordCodec.Token × List Enrollment × ResourceCost.Charge × List (Nat × Nat)

def configWireStream : StreamCodec ConfigWire :=
  StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.product (StreamCodec.list PolicyRecordCodec.tokenStream)
      (StreamCodec.product (StreamCodec.list enrollmentStream)
        (StreamCodec.product DurableReceiverCodec.chargeStream
          (StreamCodec.list (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))

def tickerWire (ticker : ClockTicker) : Nat × Nat := (ticker.subject.value, ticker.capabilityId.value)

def tickerOfWire (wire : Nat × Nat) : ClockTicker := ⟨⟨wire.1⟩, ⟨wire.2⟩⟩

@[simp] theorem tickerOfWire_comp_tickerWire : tickerOfWire ∘ tickerWire = _root_.id := by
  funext ticker
  rfl

def Config.toWire (config : Config) : ConfigWire :=
  ([config.deployment.domain.value, config.deployment.factoryId,
    config.deployment.resourceBookId, config.deployment.authorityCellId,
    config.federation.value, config.tariff.base, config.tariff.perBirth,
    config.tariff.perGrant, config.tariff.perInitialPayloadByte,
    config.tariff.collector, config.tariff.asset, config.expectedSemantics.value,
    config.issuerEpoch, config.genesisHeight, config.factoryController.subject.value,
    config.factoryController.capabilityId.value],
   PolicyRecordCodec.encodePred config.factoryPredicate,
   config.enrollments, config.meterAllowance, config.clockTickers.map tickerWire)

def Config.ofWire (wire : ConfigWire) : Option Config := do
  let [domain, factory, book, authority, federation, base, perBirth, perGrant,
      perByte, collector, asset, semantics, issuerEpoch, height, controller,
      controlCapability] := wire.1 | none
  let predicate ← PolicyRecordCodec.decodePred wire.2.1
  some
    { deployment := ⟨⟨domain⟩, factory, book, authority⟩
      federation := ⟨federation⟩
      tariff := ⟨base, perBirth, perGrant, perByte, collector, asset⟩
      expectedSemantics := ⟨semantics⟩
      issuerEpoch := issuerEpoch
      genesisHeight := height
      factoryPredicate := predicate
      enrollments := wire.2.2.1
      factoryController := ⟨⟨controller⟩, ⟨controlCapability⟩⟩
      meterAllowance := wire.2.2.2.1
      clockTickers := wire.2.2.2.2.map tickerOfWire }

@[simp] theorem Config.ofWire_toWire (config : Config) :
    Config.ofWire config.toWire = some config := by
  cases config
  simp [Config.ofWire, Config.toWire]

/-- Version 3: the source names the clock tickers (the clock cell's law and
each ticker's `C_tick` are derived from them).  Version 2 named the authority
cell as the fourth deployment coordinate and had no tickers. -/
def configFrame : List UInt8 := "DREGG/NATIVE-HOST/GENESIS-SOURCE/v3".toUTF8.toList

def configRawCodec : LawfulCodec Config where
  encode config := configFrame ++ configWireStream.encode config.toWire
  decode bytes :=
    if bytes.take configFrame.length = configFrame then do
      let wire ← configWireStream.toLawful.decode (bytes.drop configFrame.length)
      Config.ofWire wire
    else none
  decode_encode := by
    intro config
    have wire := configWireStream.toLawful.decode_encode config.toWire
    change configWireStream.toLawful.decode (configWireStream.encode config.toWire) =
      some config.toWire at wire
    simp [wire]

def configCodec : LawfulCodec Config := ResourceBirthCodec.strictCodec configRawCodec

@[simp] theorem config_roundtrip (config : Config) :
    configCodec.decode (configCodec.encode config) = some config :=
  configCodec.decode_encode config

theorem config_canonical {bytes : List UInt8} {config : Config}
    (accepted : configCodec.decode bytes = some config) :
    configCodec.encode config = bytes :=
  ResourceBirthCodec.strictCodec_canonical configRawCodec accepted

def retiredConfigFrame : List UInt8 := "DREGG/NATIVE-HOST/GENESIS-SOURCE/v2".toUTF8.toList

/-- A version-2 genesis source (no clock tickers) refuses. -/
theorem v2_config_refused (payload : List UInt8) :
    configCodec.decode (retiredConfigFrame ++ payload) = none := by
  have lengthExact : configFrame.length = retiredConfigFrame.length := by decide +kernel
  have different : retiredConfigFrame ≠ configFrame := by decide +kernel
  have raw : configRawCodec.decode (retiredConfigFrame ++ payload) = none := by
    simp [configRawCodec, lengthExact, different]
  simp [configCodec, ResourceBirthCodec.strictCodec, raw]

/-- The authority clock at genesis: no record has been accepted
(`genesis_revision` below). Key activation uses this clock (the durable
height, `CredentialAuthorityDomainReceiver.clockOf`), not a key epoch. -/
def initialAuthorityRevision : Nat := 0

def Config.Valid {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) : Prop :=
  config.expectedSemantics = profile.semantics ∧
  config.deployment.Valid ∧
  config.enrollments ≠ [] ∧
  (config.enrollments.map (·.key.subject)).Nodup ∧
  (config.enrollments.map (·.key.keyId)).Nodup ∧
  (config.enrollments.map (·.key.publicKey)).Nodup ∧
  (config.enrollments.map (·.accountId) ++
    [config.deployment.factoryId, config.deployment.resourceBookId,
     config.deployment.authorityCellId]).Nodup ∧
  config.tariff.asset ∉ config.enrollments.map (·.accountId) ∧
  (config.factoryController.capabilityId ::
    config.enrollments.flatMap (fun enrollment =>
      [enrollment.spendCapabilityId, enrollment.controlCapabilityId,
       enrollment.factoryObserveCapabilityId])).Nodup ∧
  config.factoryController.subject.value ∈ config.enrollments.map (·.key.subject) ∧
  profile.template.lifetime > 0 ∧
  (∀ enrollment ∈ config.enrollments,
    enrollment.key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
    enrollment.key.publicKey.length = 32 ∧
    enrollment.key.activeFrom ≤ initialAuthorityRevision ∧
    initialAuthorityRevision ≤ enrollment.key.activeUntil) ∧
  -- The clock tickers: enrolled, distinct, never the factory controller, and
  -- their `C_tick` identifiers distinct from every other genesis capability.
  (config.clockTickers.map (·.subject.value)).Nodup ∧
  (∀ ticker ∈ config.clockTickers,
    ticker.subject.value ∈ config.enrollments.map (·.key.subject)) ∧
  config.factoryController.subject.value ∉ config.clockTickers.map (·.subject.value) ∧
  (config.clockTickers.map (·.capabilityId) ++
    config.factoryController.capabilityId ::
    config.enrollments.flatMap (fun enrollment =>
      [enrollment.spendCapabilityId, enrollment.controlCapabilityId,
       enrollment.factoryObserveCapabilityId])).Nodup

instance configValidDecidable {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) :
    Decidable (config.Valid profile) := by
  unfold Config.Valid
  infer_instance

def Config.accounts (config : Config) : Finset Nat :=
  (config.enrollments.map (·.accountId) ++
    [config.tariff.asset, config.tariff.collector]).toFinset

/-- Each initial allocation executes the existing conserved posting operation. -/
def fund (asset : Nat) : Book → List Enrollment → Book
  | book, [] => book
  | book, enrollment :: rest =>
      fund asset (book.applyPosting
        ⟨asset, enrollment.accountId, asset, enrollment.initialBalance⟩) rest

@[simp] theorem fund_accounts (asset : Nat) (book : Book) (enrollments : List Enrollment) :
    (fund asset book enrollments).accounts = book.accounts := by
  induction enrollments generalizing book with
  | nil => rfl
  | cons enrollment rest ih => exact ih _

theorem fund_conserves (asset : Nat) (book : Book) (enrollments : List Enrollment)
    (issuerPresent : asset ∈ book.accounts)
    (recipientsPresent : ∀ enrollment ∈ enrollments, enrollment.accountId ∈ book.accounts)
    (selectedAsset : Nat) :
    (fund asset book enrollments).totalAsset selectedAsset = book.totalAsset selectedAsset := by
  induction enrollments generalizing book with
  | nil => rfl
  | cons enrollment rest ih =>
      change (fund asset (book.applyPosting
        ⟨asset, enrollment.accountId, asset, enrollment.initialBalance⟩) rest).totalAsset _ = _
      rw [ih (book.applyPosting
        ⟨asset, enrollment.accountId, asset, enrollment.initialBalance⟩)
        issuerPresent (fun selected member =>
        recipientsPresent selected (List.mem_cons_of_mem _ member))]
      exact Book.applyPosting_conserves book _ issuerPresent
        (recipientsPresent enrollment (List.mem_cons_self)) selectedAsset

def Config.initialBook (config : Config) : Book :=
  fund config.tariff.asset ⟨config.accounts, 0, 0⟩ config.enrollments

/-- Every asset, including the explicit issuer well, starts with total zero.
This holds for all configurations, not just one allocation fixture. -/
theorem initialBook_conserved (config : Config) (asset : Nat) :
    config.initialBook.totalAsset asset = 0 := by
  unfold Config.initialBook
  rw [fund_conserves]
  · simp [Book.totalAsset, Book.balance]
  · simp [Config.accounts]
  · intro enrollment member
    simp only [Config.accounts, List.mem_toFinset, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨enrollment, member, rfl⟩)

def policy {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) (identifier : Nat) (predicate : Minidregg.Pred.Pred) : PolicyRecord :=
  ⟨⟨identifier⟩, 0, config.deployment.domain, profile.semantics, none, predicate⟩

/-- The factory law with every clock ticker confined: a ticker's request is
refused whatever the deployment's own law says (`factory_refuses_ticker`), and
every other request meets exactly that law (`factory_law_others`). -/
def confinedFactoryLaw (tickers : List ClockTicker) (base : Minidregg.Pred.Pred) :
    Minidregg.Pred.Pred :=
  .all (tickers.map (fun ticker =>
      .not (.eq "request/subject" (Int.ofNat ticker.subject.value))) ++ [base])

def factoryLaw (config : Config) : Minidregg.Pred.Pred :=
  confinedFactoryLaw config.clockTickers config.factoryPredicate

def factoryPolicy {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) : PolicyRecord :=
  policy profile config config.deployment.factoryId (factoryLaw config)

/-- The request-verb tag of a tick (`CredentialAuthorityEntryCodec.verbTag`). -/
def tickVerbTag : Nat := CredentialAuthorityEntryCodec.verbTag (Verb.tickClock : Verb .program)

/-- The clock cell's law: the verb is `tickClock` and the subject is a ticker. -/
def clockPredicate (tickers : List ClockTicker) : Minidregg.Pred.Pred :=
  .all [.eq "request/verb" (Int.ofNat tickVerbTag),
    .any (tickers.map fun ticker => .eq "request/subject" (Int.ofNat ticker.subject.value))]

def clockTarget (config : Config) : Nat := Kernel.ClockCell.physicalId config.deployment.domain

def clockPolicy {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) : PolicyRecord :=
  policy profile config (clockTarget config) (clockPredicate config.clockTickers)

def accountPolicy {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) (enrollment : Enrollment) : PolicyRecord :=
  policy profile config enrollment.accountId enrollment.accountPredicate

def rootCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (kind : ResourceKind) (identifier : CapabilityId) (subject : SubjectId)
    (target : Nat) (verbs : Finset (Verb kind)) : Capability kind where
  id := identifier
  root := identifier
  parent := none
  issuer := profile.template.issuer
  holder := .subject subject
  scope := ⟨{⟨target⟩}, verbs, profile.template.ownerBudget⟩
  notBefore := config.genesisHeight
  notAfter := config.genesisHeight + profile.template.lifetime
  issuerEpoch := config.issuerEpoch
  policyId := ⟨target⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def accountCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (enrollment : Enrollment) : Capability .account :=
  rootCapability profile config .account enrollment.spendCapabilityId
    ⟨enrollment.key.subject⟩ enrollment.accountId
    (ResourceBirthPolicyController.Concrete.ownerVerbs .account)

def controlCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) : Capability .program :=
  rootCapability profile config .program config.factoryController.capabilityId
    config.factoryController.subject config.deployment.factoryId {.installPolicy, .revokeCapability}

def accountControlCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (enrollment : Enrollment) : Capability .program :=
  rootCapability profile config .program enrollment.controlCapabilityId
    ⟨enrollment.key.subject⟩ enrollment.accountId {.installPolicy, .revokeCapability}

def factoryObserveCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (enrollment : Enrollment) : Capability .object :=
  rootCapability profile config .object enrollment.factoryObserveCapabilityId
    ⟨enrollment.key.subject⟩ config.deployment.factoryId {.observeObject}

/-- A ticker's `C_tick`: target and policy the clock cell, verb `tickClock` only. -/
def tickCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) (ticker : ClockTicker) :
    Capability .program :=
  rootCapability profile config .program ticker.capabilityId ticker.subject
    (clockTarget config) {.tickClock}

def policies {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) : List PolicyRecord :=
  factoryPolicy profile config :: config.enrollments.map (accountPolicy profile config) ++
    [clockPolicy profile config]

def policyEntries (record : PolicyRecord) : List (Minidregg.Theory.Store.Entry CredentialAuthorityState.layout) :=
  [⟨⟨.policyEpoch, record.policyId⟩, (0 : TypedAuthorization.Epoch)⟩,
   ⟨⟨.policyRevision, record.policyId⟩, (record.version : PolicyRevision)⟩,
   ⟨⟨.policyAddress, (record.policyId, record.version)⟩, PolicyRecordCodec.digest record⟩]

/-- A genesis signing key: its current epoch, its record, and the registration
of its key version, exactly as enrollment writes them. -/
def keyEntries (key : KeyRecord) : List (Minidregg.Theory.Store.Entry CredentialAuthorityState.layout) :=
  [⟨⟨.subjectKeyEpoch, ⟨key.subject⟩⟩, key.keyEpoch⟩,
   ⟨⟨.subjectKey, (⟨key.subject⟩, key.keyEpoch)⟩, key⟩,
   CredentialAuthorityEffects.registrationEntry (CredentialAuthorityState.signingKeyRevocation key)]

def capabilityEntry {kind : ResourceKind} (capability : Capability kind) :
    Minidregg.Theory.Store.Entry CredentialAuthorityState.layout :=
  ⟨⟨.capability kind, capability.id⟩, (⟨capability, []⟩ : CredentialAuthorityState.StoredCapability kind)⟩

/-- A genesis capability is installed together with the registration of its
own revocation key, exactly as issuance does: "registered" is presence in the
`registered` plane, and genesis holds no capability it could not revoke. -/
def capabilityEntries {kind : ResourceKind} (capability : Capability kind) :
    List (Minidregg.Theory.Store.Entry CredentialAuthorityState.layout) :=
  [capabilityEntry capability,
   CredentialAuthorityEffects.registrationEntry (.capability capability.id)]

/-- Every genesis authority record, as entries of the one authority cell. -/
def entries {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) :
    List (Minidregg.Theory.Store.Entry CredentialAuthorityState.layout) :=
  ⟨⟨.issuerEpoch, profile.template.issuer⟩, config.issuerEpoch⟩ ::
  capabilityEntries (controlCapability profile config) ++
  (policies profile config).flatMap policyEntries ++
  config.enrollments.flatMap (fun enrollment =>
    keyEntries enrollment.key ++
    capabilityEntries (accountCapability profile config enrollment) ++
    capabilityEntries (accountControlCapability profile config enrollment) ++
    capabilityEntries (factoryObserveCapability profile config enrollment)) ++
  config.clockTickers.flatMap (fun ticker => capabilityEntries (tickCapability profile config ticker))

/-- The genesis authority store. -/
def authorityStore {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) :
    Store.Store CredentialAuthorityState.layout :=
  StoreCodec.fromEntries (entries profile config)

/-- The authority clock starts at `initialAuthorityRevision`: the genesis
durable snapshot has accepted no record. -/
theorem genesis_revision (seed : DurableReceiver.Seed) :
    CredentialAuthorityDomainReceiver.clockOf (seed.snapshot ResourceBirthCodec.rootBytes) =
      initialAuthorityRevision := rfl

def pins {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) : FactoryPins where
  factory := ⟨config.deployment.factoryId⟩
  domain := config.deployment.domain
  semantics := profile.semantics
  federation := config.federation
  policyId := (factoryPolicy profile config).policyId
  policyAddress := PolicyRecordCodec.digest (factoryPolicy profile config)
  tariff := config.tariff

/-- A declared cell holding field 1 of its own object, at zero. -/
def declaredCell (_config : Config) (identifier : Nat) (account : Bool) :
    PackedCell CanonicalCellRegistry.registry :=
  let payload := materialize DeclaredEffectCell.materializer
    (StoreCodec.fromEntries
      [⟨(EffectDeclaration.StateKey.objectField ⟨identifier⟩ ⟨1⟩).address, (0 : Int)⟩])
  if account then ⟨.accountMetadata, payload⟩ else ⟨.declaredObject, payload⟩

/-- The genesis pay cell: the invalid placeholder tariff, an empty deposit
book and no assignment (`PayCell.genesisStore`). -/
def payCell : PackedCell CanonicalCellRegistry.registry :=
  ⟨.pay, materialize Kernel.PayCell.materializer Kernel.PayCell.genesisStore⟩
/-- The genesis clock cell: the clock at zero (`ClockCell.genesisStore`). -/
def clockCell : PackedCell CanonicalCellRegistry.registry :=
  ⟨.clock, materialize Kernel.ClockCell.materializer Kernel.ClockCell.genesisStore⟩

def baseCells {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) :
    List (Nat × PackedCell CanonicalCellRegistry.registry) :=
  [(config.deployment.factoryId, declaredCell config config.deployment.factoryId
      false),
   (config.deployment.resourceBookId, ⟨.resourceBook,
      materialize CanonicalResourcePageMaterializer.materializer
        (CanonicalResourcePageMaterializer.stateOfOption (some config.initialBook))⟩)] ++
  config.enrollments.map (fun enrollment =>
    (enrollment.accountId, declaredCell config enrollment.accountId true)) ++
  (policies profile config).map (fun record =>
    (PolicySourceCell.physicalId config.deployment.domain (PolicyRecordCodec.digest record),
      CanonicalCellRegistry.policySourceCell record)) ++
  [(Kernel.PayCell.physicalId config.deployment.domain, payCell),
   (Kernel.ClockCell.physicalId config.deployment.domain, clockCell)]

def physicalCells (cells : List (Nat × PackedCell CanonicalCellRegistry.registry)) :
    List (Digest × List UInt8) :=
  cells.map fun (identifier, cell) =>
    (⟨identifier⟩, ResourceBirthCodec.LifecycleImage.bytes _ (.live cell))

def CellListValid (config : Config)
    (cells : List (Nat × PackedCell CanonicalCellRegistry.registry)) : Prop :=
  (cells.map Prod.fst).Nodup ∧
    ∀ row ∈ cells, CanonicalCellRegistry.CellLaw config.deployment row.1 row.2

instance cellListValidDecidable (config : Config)
    (cells : List (Nat × PackedCell CanonicalCellRegistry.registry)) :
    Decidable (CellListValid config cells) := by
  unfold CellListValid
  infer_instance

attribute [local irreducible] ResourceBirthCodec.rootBytes

set_option genSizeOf false in
/-- A checked bootstrap product. The private constructor prevents arbitrary
seeds from being presented as this source's genesis. No accepted turns exist. -/
structure Built {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) where
  private mk ::
  configured : config.Valid profile
  cells : List (Nat × PackedCell CanonicalCellRegistry.registry)
  cellLaws : CellListValid config cells
  seed : DurableReceiver.Seed
  exactSeed : seed = ⟨[], physicalCells cells, config.meterAllowance⟩
  authority : CredentialAuthorityDomainReceiver.Loaded config.deployment
    (seed.snapshot ResourceBirthCodec.rootBytes)

def Built.image {F : Type} [Field F] {profile : CanonicalRuntimeProfile.Profile F}
    {config : Config} (built : Built profile config) : DurableReceiver.Image :=
  ⟨built.seed, []⟩

@[simp] theorem Built.no_history {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {config : Config}
    (built : Built profile config) : built.image.accepted = [] := rfl

theorem Built.profile_exact {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {config : Config}
    (built : Built profile config) : config.expectedSemantics = profile.semantics :=
  built.configured.1

theorem Built.restore {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {config : Config}
    (built : Built profile config) :
    built.image.restore ResourceBirthCodec.rootBytes =
      some (built.seed.snapshot ResourceBirthCodec.rootBytes) := by
  have unique : (built.seed.cells.map Prod.fst).Nodup := by
    rw [built.exactSeed]
    simpa [physicalCells, List.map_map, Function.comp_def] using
      built.cellLaws.1.map (fun _ _ equal => Digest.mk.inj equal)
  simp [Built.image, DurableReceiver.Image.restore, unique, DurableReceiver.replay]

inductive Error where
  | wireEncoding
  | configuration
  | authorityEntries
  | cellLaws
  | physicalAuthority
  deriving DecidableEq, Repr

/-- Source derivation followed by the actual receiving checks. A profile
disagreement, duplicate enrollment or physical collision refuses before a
native write can be requested. -/
def build {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) : Except Error (Built profile config) := do
  if valid : config.Valid profile then
    if !decide ((entries profile config).map Sigma.fst).Nodup then
      throw .authorityEntries
    let authorityCell := materialize CredentialAuthorityCell.materializer (authorityStore profile config)
    let cells := baseCells profile config ++
      [(config.deployment.authorityCellId,
        CredentialAuthorityDomainReceiver.packedCell authorityCell)]
    if cellLaws : CellListValid config cells then
      let seed : DurableReceiver.Seed := ⟨[], physicalCells cells, config.meterAllowance⟩
      let authority ← match CredentialAuthorityDomainReceiver.loadDeployment config.deployment
          (seed.snapshot ResourceBirthCodec.rootBytes) with
        | none => .error .physicalAuthority
        | some authority => .ok authority
      .ok ⟨valid, cells, cellLaws, seed, rfl, authority⟩
    else .error .cellLaws
  else .error .configuration

theorem invalid_configuration_refused {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (invalid : ¬config.Valid profile) : build profile config = .error .configuration := by
  simp [build, invalid]

theorem incompatible_profile_refused {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (incompatible : config.expectedSemantics ≠ profile.semantics) :
    build profile config = .error .configuration :=
  invalid_configuration_refused profile config (fun valid => incompatible valid.1)

theorem duplicate_subjects_refused {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (duplicate : ¬(config.enrollments.map (·.key.subject)).Nodup) :
    build profile config = .error .configuration := by
  apply invalid_configuration_refused profile config
  rintro ⟨_, _, _, unique, _⟩
  exact duplicate unique

theorem duplicate_key_ids_refused {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (duplicate : ¬(config.enrollments.map (·.key.keyId)).Nodup) :
    build profile config = .error .configuration := by
  apply invalid_configuration_refused profile config
  rintro ⟨_, _, _, _, unique, _⟩
  exact duplicate unique

theorem duplicate_public_keys_refused {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (duplicate : ¬(config.enrollments.map (·.key.publicKey)).Nodup) :
    build profile config = .error .configuration := by
  apply invalid_configuration_refused profile config
  rintro ⟨_, _, _, _, _, unique, _⟩
  exact duplicate unique

/-- Decoding supplies no authority. The same builder and checks admit every
decoded source, and malformed/noncanonical bytes refuse before derivation. -/
def buildBytes {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (bytes : List UInt8) : Except Error ((config : Config) × Built profile config) := do
  let config ← match configCodec.decode bytes with
    | none => .error .wireEncoding
    | some config => .ok config
  let built ← build profile config
  pure ⟨config, built⟩

/-! ## The clock subject (CLOCK-SUBJECT)

Genesis names the clock tickers.  Each holds one `C_tick` (`tickCapability`):
the clock cell as target and policy, the verb `tickClock` alone.  The clock
cell's law admits exactly a ticker's `tickClock` (`clockPredicate_eval`); the
factory law refuses every ticker request (`factory_refuses_ticker`) and leaves
every other request to the deployment's own law (`factory_law_others`).  No
genesis capability of the factory controller carries `tickClock`, and the
clock law refuses the controller (`tick_requires_clock_capability`). -/

theorem tickVerbTag_eq : tickVerbTag = 7 := rfl

/-- The clock law, decided: a request is admitted exactly when its verb is
`tickClock` and its subject is a ticker. -/
theorem clockPredicate_eval (tickers : List ClockTicker) (old new : Minidregg.Pred.State)
    (subject verb : Nat)
    (named : new.get "request/subject" = some (Int.ofNat subject))
    (verbed : new.get "request/verb" = some (Int.ofNat verb)) :
    Minidregg.Pred.eval (clockPredicate tickers) old new = true ↔
      verb = tickVerbTag ∧ subject ∈ tickers.map (·.subject.value) := by
  unfold Minidregg.Pred.eval clockPredicate
  rw [Minidregg.Pred.evalWith_all]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [Minidregg.Pred.evalWith_any]
  simp only [List.any_map, List.any_eq_true, Function.comp_apply, Minidregg.Pred.evalWith,
    named, verbed, decide_eq_true_eq, Option.some.injEq, Int.ofNat.injEq, List.mem_map]
  constructor
  · rintro ⟨verbExact, ticker, member, subjectExact⟩
    exact ⟨verbExact, ticker, member, subjectExact.symm⟩
  · rintro ⟨verbExact, ticker, member, subjectExact⟩
    exact ⟨verbExact, ticker, member, subjectExact.symm⟩

/-- Refuting pole of the clock law: a subject that is not a ticker is refused,
whatever its verb. -/
theorem clock_law_refuses_nonticker (tickers : List ClockTicker) (old new : Minidregg.Pred.State)
    (subject : Nat) (named : new.get "request/subject" = some (Int.ofNat subject))
    (other : subject ∉ tickers.map (·.subject.value)) :
    Minidregg.Pred.eval (clockPredicate tickers) old new = false := by
  unfold Minidregg.Pred.eval clockPredicate
  rw [Minidregg.Pred.evalWith_all]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [Minidregg.Pred.evalWith_any]
  have none_ : (tickers.map fun ticker =>
      (Minidregg.Pred.Pred.eq "request/subject" (Int.ofNat ticker.subject.value))).any
      (fun q => Minidregg.Pred.evalWith Minidregg.Pred.failClosed q old new) = false := by
    rw [Bool.eq_false_iff]
    intro some_
    obtain ⟨q, member, holds⟩ := List.any_eq_true.mp some_
    obtain ⟨ticker, tickerMember, rfl⟩ := List.mem_map.mp member
    simp only [Minidregg.Pred.evalWith, named, decide_eq_true_eq, Option.some.injEq,
      Int.ofNat.injEq] at holds
    exact other (List.mem_map.mpr ⟨ticker, tickerMember, holds.symm⟩)
  rw [none_, Bool.and_false]

/-- **`factory_refuses_ticker`**: under the confined factory law a ticker's
request is refused, whatever the deployment's own law says: no birth, no key
enrollment, no provisioning, no policy install. -/
theorem factory_refuses_ticker (tickers : List ClockTicker) (base : Minidregg.Pred.Pred)
    (ticker : ClockTicker) (member : ticker ∈ tickers) (old new : Minidregg.Pred.State)
    (byTicker : new.get "request/subject" = some (Int.ofNat ticker.subject.value)) :
    Minidregg.Pred.eval (confinedFactoryLaw tickers base) old new = false := by
  have refused : Minidregg.Pred.evalWith Minidregg.Pred.failClosed
      (.not (.eq "request/subject" (Int.ofNat ticker.subject.value))) old new = false := by
    simp [Minidregg.Pred.evalWith, byTicker]
  unfold Minidregg.Pred.eval confinedFactoryLaw
  rw [Minidregg.Pred.evalWith_all, Bool.eq_false_iff]
  intro all_
  have holds := List.all_eq_true.mp all_ _
    (List.mem_append_left _ (List.mem_map.mpr ⟨ticker, member, rfl⟩))
  rw [refused] at holds
  exact Bool.false_ne_true holds

/-- Every request whose subject is not a ticker meets exactly the deployment's
own factory law. -/
theorem factory_law_others (tickers : List ClockTicker) (base : Minidregg.Pred.Pred)
    (old new : Minidregg.Pred.State) (subject : Nat)
    (named : new.get "request/subject" = some (Int.ofNat subject))
    (other : subject ∉ tickers.map (·.subject.value)) :
    Minidregg.Pred.eval (confinedFactoryLaw tickers base) old new =
      Minidregg.Pred.eval base old new := by
  unfold Minidregg.Pred.eval confinedFactoryLaw
  rw [Minidregg.Pred.evalWith_all, List.all_append]
  have guards : (tickers.map fun ticker =>
      (Minidregg.Pred.Pred.not (.eq "request/subject" (Int.ofNat ticker.subject.value)))).all
      (fun q => Minidregg.Pred.evalWith Minidregg.Pred.failClosed q old new) = true := by
    rw [List.all_eq_true]
    intro q member
    obtain ⟨ticker, tickerMember, rfl⟩ := List.mem_map.mp member
    simp only [Minidregg.Pred.evalWith, named, Option.some.injEq, Int.ofNat.injEq,
      Bool.not_eq_true', decide_eq_false_iff_not]
    intro same
    exact other (List.mem_map.mpr ⟨ticker, tickerMember, same.symm⟩)
  rw [guards]
  simp

/-- **`clock_subject_confined`**: a ticker's `C_tick` is held by the ticker,
names the clock cell as its only target and policy and `tickClock` as its only
verb (no delegation, no policy install, no revocation), and is installed at
genesis; and the factory refuses the ticker every request.  `C_tick` covers
the tick verb on the clock cell and nothing else. -/
theorem clock_subject_confined {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) (ticker : ClockTicker) (member : ticker ∈ config.clockTickers) :
    (tickCapability profile config ticker).holder = .subject ticker.subject ∧
      (tickCapability profile config ticker).scope.targets = {⟨clockTarget config⟩} ∧
      (tickCapability profile config ticker).scope.verbs = {.tickClock} ∧
      (tickCapability profile config ticker).policyId = ⟨clockTarget config⟩ ∧
      capabilityEntry (tickCapability profile config ticker) ∈ entries profile config ∧
      (factoryPolicy profile config).predicate =
        confinedFactoryLaw config.clockTickers config.factoryPredicate ∧
      (∀ old new, new.get "request/subject" = some (Int.ofNat ticker.subject.value) →
        Minidregg.Pred.eval (factoryPolicy profile config).predicate old new = false) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, fun old new byTicker =>
    factory_refuses_ticker _ _ ticker member old new byTicker⟩
  simp only [entries, capabilityEntries, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false]
  exact Or.inr ⟨ticker, member, Or.inl rfl⟩

/-- **`tick_requires_clock_capability`** (K-CLOCK's `tick_requires_capability`
at the genesis shape): the factory controller's genesis program capabilities
do not carry `tickClock`, and the clock cell's law refuses the factory
controller (a valid genesis never makes it a ticker).  The sponsor cannot
tick: with no evidence the receiver refuses `capabilityRejected`
(`ClockTickReceiver.tick_requires_capability`), and with any evidence the law
refuses. -/
theorem tick_requires_clock_capability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) (valid : config.Valid profile) :
    Verb.tickClock ∉ (controlCapability profile config).scope.verbs ∧
      (∀ enrollment ∈ config.enrollments,
        Verb.tickClock ∉ (accountControlCapability profile config enrollment).scope.verbs) ∧
      (∀ old new, new.get "request/subject" =
          some (Int.ofNat config.factoryController.subject.value) →
        Minidregg.Pred.eval (clockPolicy profile config).predicate old new = false) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, notTicker, -⟩ := valid
  refine ⟨by simp [controlCapability, rootCapability], fun _ _ => by
    simp [accountControlCapability, rootCapability], fun old new named => ?_⟩
  exact clock_law_refuses_nonticker _ old new _ named notTicker

/-- Request states for the poles: clock ticker 70 (the journey's clock subject),
sponsor 7, the journeys' permit-all base law. -/
def requestState (subject verb : Nat) : Minidregg.Pred.State :=
  ⟨[("request/subject", Int.ofNat subject), ("request/verb", Int.ofNat verb)]⟩

def poleTickers : List ClockTicker := [⟨⟨70⟩, ⟨71⟩⟩]

theorem ticker_tick_admitted :
    Minidregg.Pred.eval (clockPredicate poleTickers) ⟨[]⟩ (requestState 70 7) = true := by
  decide +kernel

theorem sponsor_tick_refused :
    Minidregg.Pred.eval (clockPredicate poleTickers) ⟨[]⟩ (requestState 7 7) = false := by
  decide +kernel

theorem ticker_install_refused :
    Minidregg.Pred.eval (clockPredicate poleTickers) ⟨[]⟩ (requestState 70 4) = false := by
  decide +kernel

theorem ticker_factory_refused :
    Minidregg.Pred.eval (confinedFactoryLaw poleTickers (.all [])) ⟨[]⟩ (requestState 70 4) = false := by
  decide +kernel

theorem sponsor_factory_admitted :
    Minidregg.Pred.eval (confinedFactoryLaw poleTickers (.all [])) ⟨[]⟩ (requestState 7 4) = true := by
  decide +kernel

#assert_axioms clockPredicate_eval
#assert_axioms clock_law_refuses_nonticker
#assert_axioms factory_refuses_ticker
#assert_axioms factory_law_others
#assert_axioms clock_subject_confined
#assert_axioms tick_requires_clock_capability
#assert_axioms ticker_tick_admitted
#assert_axioms sponsor_tick_refused
#assert_axioms ticker_install_refused
#assert_axioms ticker_factory_refused
#assert_axioms sponsor_factory_admitted

/-- info: 'Minidregg.Kernel.NativeHostGenesis.genesis_revision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms genesis_revision
/-- info: 'Minidregg.Kernel.NativeHostGenesis.v2_config_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v2_config_refused

end Minidregg.Kernel.NativeHostGenesis
