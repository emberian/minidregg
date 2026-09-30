/-
Shared source-owned host configuration and structural validation. Semantic
history verification imports this module; ordinary host APIs import the verifier.
There is one profile, one world-root commitment, and one validation path.
-/
import Compiler.NativeHostCodec
import Compiler.GrainResourceBirthController

namespace Minidregg.Kernel.NativeHost

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.NativeHostCodec

set_option autoImplicit false

abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes

/-- Operator-pinned identity for the local fn application gateway. The current
resource law is checked separately against this pin before new fn work. -/
structure FnGatewayPin where
  application : List UInt8
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  policyAddress : Digest
  deriving DecidableEq, Repr

/-- Permission micro-units charged to a previously reserved tool grain for a
composite birth. This is independent of the conserved Book creation tariff. -/
structure GrainBirthTariffPin where
  base : Nat
  perBirth : Nat
  deriving DecidableEq, Repr

structure Config where
  deployment : CanonicalCellRegistry.Deployment
  federation : FederationId
  template : CanonicalRuntimeProfile.FactoryTemplate
  tariff : CreationTariff
  genesisHeight : Nat
  expectedSeed : Digest
  storage : DurableReceiverIO.NativeConfig
  signature : CredentialSignatureIO.NativeConfig
  fnGateway : Option FnGatewayPin := none
  grainBirthTariff : Option GrainBirthTariffPin := none
  /-- Public Ed25519 key of the separately controlled physical host custodian.
  Absence preserves the legacy profile and disables checked completion. -/
  completionCustodianKey : Option (List UInt8) := none

def Config.grainBirthTariffValue (config : Config) :
    Except String GrainResourceBirthController.Tariff := do
  let some pinned := config.grainBirthTariff
    | throw "grain-backed birth tariff is not enabled"
  if positive : 0 < pinned.base then
    pure ⟨pinned.base, pinned.perBirth, positive⟩
  else throw "grain-backed birth tariff base must be positive"

/-- This manifest enters runtime semantics. The seed commitment is separate
because the genesis's source policies themselves contain that semantics. -/
def Config.runtimeParameters (config : Config) : List UInt8 :=
  "DREGG.NATIVE-HOST.PARAMETERS/v1".toUTF8.toList ++
  (StreamCodec.list StreamCodec.nat).encode
    [config.deployment.domain.value, config.deployment.factoryId,
     config.deployment.resourceBookId, config.deployment.authorityCellId,
     config.federation.value, config.genesisHeight, config.tariff.base,
     config.tariff.perBirth, config.tariff.perGrant, config.tariff.perInitialPayloadByte,
     config.tariff.collector, config.tariff.asset] ++
  (match config.grainBirthTariff with
  | none => []
  | some tariff =>
      "DREGG/NATIVE-HOST/GRAIN-BIRTH-TARIFF/v1".toUTF8.toList ++
        (StreamCodec.product StreamCodec.nat StreamCodec.nat).encode
          (tariff.base, tariff.perBirth)) ++
  (match config.completionCustodianKey with
  | none => []
  | some key =>
      "DREGG/NATIVE-HOST/COMPLETION-CUSTODIAN/v1".toUTF8.toList ++
        bytesStream.encode key)

/-- Disabling the new mode preserves the complete pre-existing parameter
preimage, hence its legacy semantics/profile and genesis interpretation. -/
theorem Config.runtimeParameters_withoutOptionalModes (config : Config) :
    ({ config with grainBirthTariff := none, completionCustodianKey := none } : Config).runtimeParameters =
      "DREGG.NATIVE-HOST.PARAMETERS/v1".toUTF8.toList ++
        (StreamCodec.list StreamCodec.nat).encode
          [config.deployment.domain.value, config.deployment.factoryId,
           config.deployment.resourceBookId, config.deployment.authorityCellId,
           config.federation.value, config.genesisHeight, config.tariff.base,
           config.tariff.perBirth, config.tariff.perGrant,
           config.tariff.perInitialPayloadByte, config.tariff.collector,
           config.tariff.asset] := by simp [Config.runtimeParameters]

def Config.profile (config : Config) :=
  NativeHostProfile.profile config.template config.runtimeParameters

attribute [local irreducible] Config.profile CanonicalRuntimeProfile.Profile.compilerProfile

def seedIdentity (seed : DurableReceiver.Seed) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.GENESIS/v1".toUTF8.toList
    (DurableReceiverCodec.seedStream.encode seed)).digest

/-- The world root of an image under this deployment (`NativeHostCodec.worldRoot`). -/
def worldRoot (config : Config) (image : DurableReceiver.Image) : Digest :=
  NativeHostCodec.worldRoot config.deployment.domain config.profile.semantics image

/-- The log chain's start for this deployment: C1's genesis log root, binding
domain, semantics and seed. The Store's MAC chain and the world root's system
slot are this one chain. -/
def Config.logStart (config : Config) (seed : DurableReceiver.Seed) : Digest :=
  NativeHostCodec.logRoot0 config.deployment.domain config.profile.semantics seed

/-- The Store transport for this deployment. -/
def Config.transport (config : Config) : DurableReceiverIO.Transport :=
  config.storage.transport config.logStart

def logicalHeight (config : Config) (durable : Durable) : Height :=
  config.genesisHeight + durable.image.accepted.length

theorem logicalHeight_exact (config : Config) (durable : Durable) :
    logicalHeight config durable = config.genesisHeight + durable.image.accepted.length := rfl

/-- Every policy whose revision the authority cell records has a complete
current head, and that head's address loads a source cell of the same policy,
the same revision and this runtime's semantics. -/
def policySourced (config : Config) (directory : Directory Nat CanonicalCellRegistry.registry)
    (logical : Store.Store CredentialAuthorityState.layout) :
    Store.Address CredentialAuthorityState.layout → Bool
  | ⟨.policyRevision, identifier⟩ =>
      match CredentialAuthorityDomain.headAt logical identifier with
      | none => false
      | some head =>
          match CanonicalCellRegistry.loadPolicySource config.deployment.domain directory head.address with
          | none => false
          | some source => decide (source.record.policyId = identifier ∧
              source.record.version = head.version ∧ source.record.semantics = config.profile.semantics)
  | _ => true

def policiesSourced (config : Config) (directory : Directory Nat CanonicalCellRegistry.registry)
    (logical : Store.Store CredentialAuthorityState.layout) : Bool :=
  decide (∀ address ∈ logical.support, policySourced config directory logical address = true)

structure Opened (config : Config) where
  private mk ::
  durable : Durable
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded config.deployment durable.snapshot
  pins : FactoryPins

def need {α : Type} (detail : String) : Option α → Except String α
  | none => .error detail
  | some value => .ok value

def check (condition : Bool) (detail : String) : Except String Unit :=
  if condition then .ok () else .error detail

/-- Everything `validateLoaded` derives from one loaded image. -/
structure Validated (config : Config) (durable : Durable) where
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded config.deployment durable.snapshot
  pins : FactoryPins

def validateParts (config : Config) (durable : Durable) :
    Except String (Validated config durable) := do
  if config.grainBirthTariff.isSome then
    let _ ← config.grainBirthTariffValue
  if let some key := config.completionCustodianKey then
    check (decide (key.length = 32)) "physical completion custodian key must be 32 bytes"
  check (decide config.deployment.Valid) "invalid deployment role identities"
  check (seedIdentity durable.image.seed == config.expectedSeed) "genesis identity mismatch"
  check (durable.logStart == config.logStart durable.image.seed) "log chain not rooted at this deployment's genesis"
  let directory ← need "noncanonical native directory"
    (CredentialAuthorityDomainReceiver.loadDirectory durable)
  let authority ← need "complete deployment authority unavailable"
    (CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot)
  check (durable.image.cellIds.all fun identifier =>
    match directory.directory.slots identifier.value with
    | .absent => true
    | .present cell => CanonicalCellRegistry.cellCheck config.deployment identifier.value cell)
    "native cell role or domain law refused"
  check (policiesSourced config directory.directory authority.snapshot.logical)
    "selected policy source/profile mismatch"
  let factoryHead ← need "factory policy head unavailable"
    (CredentialAuthorityDomain.headAt authority.snapshot.logical ⟨config.deployment.factoryId⟩)
  let pins : FactoryPins :=
    { factory := ⟨config.deployment.factoryId⟩
      domain := config.deployment.domain
      semantics := config.profile.semantics
      federation := config.federation
      policyId := ⟨config.deployment.factoryId⟩
      policyAddress := factoryHead.address
      tariff := config.tariff }
  pure ⟨directory, authority, pins⟩

def validateLoaded (config : Config) (durable : Durable) : Except String (Opened config) :=
  (validateParts config durable).map fun parts =>
    ⟨durable, parts.directory, parts.authority, parts.pins⟩

/-- Validation wraps exactly the image it was given. -/
theorem validateLoaded_durable {config : Config} {durable : Durable} {opened : Opened config}
    (validated : validateLoaded config durable = .ok opened) : opened.durable = durable := by
  unfold validateLoaded at validated
  cases parts : validateParts config durable with
  | error detail => simp [parts, Except.map] at validated
  | ok value =>
      simp only [parts, Except.map, Except.ok.injEq] at validated
      subst validated
      rfl

end Minidregg.Kernel.NativeHost
