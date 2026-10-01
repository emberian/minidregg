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
abbrev ConfigWire := List Nat × List PolicyRecordCodec.Token × List Enrollment × ResourceCost.Charge

def configWireStream : StreamCodec ConfigWire :=
  StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.product (StreamCodec.list PolicyRecordCodec.tokenStream)
      (StreamCodec.product (StreamCodec.list enrollmentStream) DurableReceiverCodec.chargeStream))

def Config.toWire (config : Config) : ConfigWire :=
  ([config.deployment.domain.value, config.deployment.factoryId,
    config.deployment.resourceBookId, config.deployment.authorityCellId,
    config.federation.value, config.tariff.base, config.tariff.perBirth,
    config.tariff.perGrant, config.tariff.perInitialPayloadByte,
    config.tariff.collector, config.tariff.asset, config.expectedSemantics.value,
    config.issuerEpoch, config.genesisHeight, config.factoryController.subject.value,
    config.factoryController.capabilityId.value],
   PolicyRecordCodec.encodePred config.factoryPredicate,
   config.enrollments, config.meterAllowance)

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
      meterAllowance := wire.2.2.2 }

@[simp] theorem Config.ofWire_toWire (config : Config) :
    Config.ofWire config.toWire = some config := by
  cases config
  simp [Config.ofWire, Config.toWire]

/-- Version 2: the fourth deployment coordinate is the one authority cell's
identifier (it was the retired catalogue's). -/
def configFrame : List UInt8 := "DREGG/NATIVE-HOST/GENESIS-SOURCE/v2".toUTF8.toList

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

def retiredConfigFrame : List UInt8 := "DREGG/NATIVE-HOST/GENESIS-SOURCE/v1".toUTF8.toList

/-- A version-1 genesis source (naming a catalogue identifier) refuses. -/
theorem v1_config_refused (payload : List UInt8) :
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
    initialAuthorityRevision ≤ enrollment.key.activeUntil)

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

def factoryPolicy {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) : PolicyRecord :=
  policy profile config config.deployment.factoryId config.factoryPredicate

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
  scope := ⟨.explicit {⟨target⟩}, verbs, profile.template.ownerBudget⟩
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

def policies {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) : List PolicyRecord :=
  factoryPolicy profile config :: config.enrollments.map (accountPolicy profile config)

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
    capabilityEntries (factoryObserveCapability profile config enrollment))

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

/-- The genesis pay cell: the invalid placeholder tariff, the zero clock, an
empty deposit book and no assignment (`PayCell.genesisStore`). -/
def payCell : PackedCell CanonicalCellRegistry.registry :=
  ⟨.pay, materialize Kernel.PayCell.materializer Kernel.PayCell.genesisStore⟩

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
  [(Kernel.PayCell.physicalId config.deployment.domain, payCell)]

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

/-- info: 'Minidregg.Kernel.NativeHostGenesis.genesis_revision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms genesis_revision
/-- info: 'Minidregg.Kernel.NativeHostGenesis.v1_config_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v1_config_refused

end Minidregg.Kernel.NativeHostGenesis
