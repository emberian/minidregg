/-
Shared source-owned host configuration and structural validation. Semantic
history verification imports this module; ordinary host APIs import the verifier.
There is one profile, one image-boundary commitment, and one validation path.
-/
import Compiler.NativeHostCodec

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

structure Config where
  deployment : CanonicalCellRegistry.Deployment
  federation : FederationId
  template : CanonicalRuntimeProfile.FactoryTemplate
  tariff : CreationTariff
  genesisHeight : Nat
  expectedSeed : Digest
  storage : DurableReceiverIO.NativeConfig
  signature : CredentialSignatureIO.NativeConfig

/-- This manifest enters runtime semantics. The seed commitment is separate
because the genesis's source policies themselves contain that semantics. -/
def Config.runtimeParameters (config : Config) : List UInt8 :=
  "DREGG.NATIVE-HOST.PARAMETERS/v1".toUTF8.toList ++
  (StreamCodec.list StreamCodec.nat).encode
    [config.deployment.domain.value, config.deployment.factoryId,
     config.deployment.resourceBookId, config.deployment.authorityCatalogueId,
     config.federation.value, config.genesisHeight, config.tariff.base,
     config.tariff.perBirth, config.tariff.perGrant, config.tariff.perInitialPayloadByte,
     config.tariff.collector, config.tariff.asset]

def Config.profile (config : Config) :=
  NativeHostProfile.profile config.template config.runtimeParameters

attribute [local irreducible] Config.profile CanonicalRuntimeProfile.Profile.compilerProfile

def seedIdentity (seed : DurableReceiver.Seed) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.GENESIS/v1".toUTF8.toList
    (DurableReceiverCodec.seedStream.encode seed)).digest

def imageBoundary (config : Config) (image : DurableReceiver.Image) : Digest :=
  NativeHostCodec.imageBoundary config.deployment.domain config.profile.semantics image

def logicalHeight (config : Config) (durable : Durable) : Height :=
  config.genesisHeight + durable.image.accepted.length

theorem logicalHeight_exact (config : Config) (durable : Durable) :
    logicalHeight config durable = config.genesisHeight + durable.image.accepted.length := rfl

structure Opened (config : Config) where
  private mk ::
  durable : Durable
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded config.deployment.authorityAnchor durable.snapshot
  pins : FactoryPins

def need {α : Type} (detail : String) : Option α → Except String α
  | none => .error detail
  | some value => .ok value

def check (condition : Bool) (detail : String) : Except String Unit :=
  if condition then .ok () else .error detail

def validateLoaded (config : Config) (durable : Durable) : Except String (Opened config) := do
  check (decide config.deployment.Valid) "invalid deployment role identities"
  check (seedIdentity durable.image.seed == config.expectedSeed) "genesis identity mismatch"
  let directory ← need "noncanonical native directory"
    (CredentialAuthorityDomainReceiver.loadDirectory durable)
  let authority ← need "complete deployment authority unavailable"
    (CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot)
  check (durable.image.cellIds.all fun identifier =>
    match directory.directory.slots identifier.value with
    | .absent => true
    | .present cell => CanonicalCellRegistry.cellCheck config.deployment identifier.value cell)
    "native cell role or domain law refused"
  check (authority.snapshot.entries.all fun entry =>
    match entry with
    | .policy identifier _ revision address =>
        match CanonicalCellRegistry.loadPolicySource config.deployment.domain directory.directory address with
        | none => false
        | some source => decide (source.record.policyId = identifier ∧
            source.record.version = revision ∧ source.record.semantics = config.profile.semantics)
    | _ => true) "selected policy source/profile mismatch"
  let factoryHead ← need "factory policy head unavailable"
    (CredentialAuthorityDomain.headAt authority.snapshot ⟨config.deployment.factoryId⟩)
  let pins : FactoryPins :=
    { factory := ⟨config.deployment.factoryId⟩
      domain := config.deployment.domain
      semantics := config.profile.semantics
      federation := config.federation
      policyId := ⟨config.deployment.factoryId⟩
      policyAddress := factoryHead.address
      tariff := config.tariff }
  pure ⟨durable, directory, authority, pins⟩

end Minidregg.Kernel.NativeHost
