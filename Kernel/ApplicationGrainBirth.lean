/- Source-owned authoring of one application resource and its two manifest
resources. Existing native resource-birth admission must still check the
factory, charge, grants, policy sources, freshness and durable receiving. No
caller supplies a replacement policy AST or arbitrary initial app page. -/
import Kernel.ApplicationGrain
import Kernel.NativeHostGenesis
import Kernel.ResourceBirthController
import Kernel.ContentResource

namespace Minidregg.Kernel.ApplicationGrainBirth
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.IntStream (intStream)
set_option autoImplicit false

/-- Six independent capability identities are required by the existing
factory template: one object owner grant and one program control grant for
each of the three born resources. -/
structure Spec where
  app : Nat
  packageManifest : Nat
  snapshotManifest : Nat
  owner : SubjectId
  appOwnerCapability : CapabilityId
  appControlCapability : CapabilityId
  packageOwnerCapability : CapabilityId
  packageControlCapability : CapabilityId
  snapshotOwnerCapability : CapabilityId
  snapshotControlCapability : CapabilityId
  deriving DecidableEq, Repr

def Spec.targets (spec : Spec) : List Nat :=
  [spec.app, spec.packageManifest, spec.snapshotManifest]

def Spec.capabilities (spec : Spec) : List CapabilityId :=
  [spec.appOwnerCapability, spec.appControlCapability,
   spec.packageOwnerCapability, spec.packageControlCapability,
   spec.snapshotOwnerCapability, spec.snapshotControlCapability]

def Spec.Valid (spec : Spec) : Prop :=
  spec.targets.Nodup ∧ spec.capabilities.Nodup

instance validDecidable (spec : Spec) : Decidable spec.Valid := by
  unfold Spec.Valid
  infer_instance

structure Ready where
  private mk ::
  spec : Spec
  valid : spec.Valid

def prepare (spec : Spec) : Except String Ready :=
  if valid : spec.Valid then .ok ⟨spec, valid⟩
  else .error "application birth targets and capability IDs must each be distinct"

theorem Ready.targets_distinct (ready : Ready) : ready.spec.targets.Nodup := ready.valid.1
theorem Ready.capabilities_distinct (ready : Ready) : ready.spec.capabilities.Nodup := ready.valid.2

private def appCell (_config : NativeHostGenesis.Config) (app : Nat) :
    PackedCell CanonicalCellRegistry.registry :=
  ⟨.declaredObject, materialize DeclaredEffectCell.materializer (ApplicationGrain.initialStore app)⟩

private def manifestCell (_config : NativeHostGenesis.Config) (_target : Nat) :
    PackedCell CanonicalCellRegistry.registry :=
  ⟨.content, materialize HyperdocumentCell.contentMaterializer ContentResource.initialStore⟩

private def birthItem (target : Nat) (owner : SubjectId)
    (cell : PackedCell CanonicalCellRegistry.registry) :
    BirthItem CanonicalCellRegistry.registry :=
  ⟨⟨target, CellSlot.root CanonicalCellRegistry.registry .absent, cell⟩, .object, owner⟩

def Ready.births (ready : Ready) (config : NativeHostGenesis.Config) :
    List (BirthItem CanonicalCellRegistry.registry) :=
  [birthItem ready.spec.app ready.spec.owner (appCell config ready.spec.app),
   birthItem ready.spec.packageManifest ready.spec.owner
     (manifestCell config ready.spec.packageManifest),
   birthItem ready.spec.snapshotManifest ready.spec.owner
     (manifestCell config ready.spec.snapshotManifest)]

private def ownerGrant {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : NativeHostGenesis.Config)
    (height target : Nat) (owner : SubjectId) (identifier : CapabilityId) : AuthorityGrant :=
  ⟨.object, ⟨{ NativeHostGenesis.rootCapability profile config .object identifier owner target
      (ResourceBirthPolicyController.Concrete.ownerVerbs .object) with
      notBefore := height, notAfter := height + profile.template.lifetime }, []⟩⟩

private def controlGrant {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : NativeHostGenesis.Config)
    (height target : Nat) (owner : SubjectId) (identifier : CapabilityId) : AuthorityGrant :=
  ⟨.program, ⟨{ NativeHostGenesis.rootCapability profile config .program identifier owner target
      {.installPolicy, .revokeCapability} with
      notBefore := height, notAfter := height + profile.template.lifetime }, []⟩⟩

def Ready.grants {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) (height : Nat) : List AuthorityGrant :=
  [ownerGrant profile config height ready.spec.app ready.spec.owner ready.spec.appOwnerCapability,
   controlGrant profile config height ready.spec.app ready.spec.owner ready.spec.appControlCapability,
   ownerGrant profile config height ready.spec.packageManifest ready.spec.owner
     ready.spec.packageOwnerCapability,
   controlGrant profile config height ready.spec.packageManifest ready.spec.owner
     ready.spec.packageControlCapability,
   ownerGrant profile config height ready.spec.snapshotManifest ready.spec.owner
     ready.spec.snapshotOwnerCapability,
   controlGrant profile config height ready.spec.snapshotManifest ready.spec.owner
     ready.spec.snapshotControlCapability]

/-- A post-genesis birth takes grant epochs from the currently loaded
authority. The genesis configuration still fixes issuer, scope, budget and
policy identity, but it is not an authority snapshot after rotation. -/
private def currentRootCapability {F : Type} [Field F] (kind : ResourceKind)
    (profile : CanonicalRuntimeProfile.Profile F) (config : NativeHostGenesis.Config)
    (authority : AuthState) (height target : Nat) (owner : SubjectId)
    (identifier : CapabilityId) (verbs : Finset (Verb kind)) : Capability kind :=
  { NativeHostGenesis.rootCapability profile config kind identifier owner target verbs with
    notBefore := height
    notAfter := height + profile.template.lifetime
    issuerEpoch := authority.issuerEpoch profile.template.issuer
    policyEpoch := authority.policyEpoch ⟨target⟩ }

private theorem currentRootCapability_current {F : Type} [Field F]
    (kind : ResourceKind) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) (authority : AuthState)
    (height target : Nat) (owner : SubjectId) (identifier : CapabilityId)
    (verbs : Finset (Verb kind)) :
    (currentRootCapability kind profile config authority height target owner identifier verbs).issuerEpoch =
        authority.issuerEpoch profile.template.issuer ∧
      (currentRootCapability kind profile config authority height target owner identifier verbs).policyEpoch =
        authority.policyEpoch ⟨target⟩ ∧
      (currentRootCapability kind profile config authority height target owner identifier verbs).notBefore =
        height := by
  exact ⟨rfl, rfl, rfl⟩

private def ownerGrantCurrent {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : NativeHostGenesis.Config)
    (authority : AuthState) (height target : Nat) (owner : SubjectId)
    (identifier : CapabilityId) : AuthorityGrant :=
  ⟨.object, ⟨currentRootCapability .object profile config authority height target owner identifier
    (ResourceBirthPolicyController.Concrete.ownerVerbs .object), []⟩⟩

private def controlGrantCurrent {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : NativeHostGenesis.Config)
    (authority : AuthState) (height target : Nat) (owner : SubjectId)
    (identifier : CapabilityId) : AuthorityGrant :=
  ⟨.program, ⟨currentRootCapability .program profile config authority height target owner identifier
    {.installPolicy, .revokeCapability}, []⟩⟩

def Ready.grantsCurrent {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) (authority : AuthState) (height : Nat) :
    List AuthorityGrant :=
  [ownerGrantCurrent profile config authority height ready.spec.app ready.spec.owner
     ready.spec.appOwnerCapability,
   controlGrantCurrent profile config authority height ready.spec.app ready.spec.owner
     ready.spec.appControlCapability,
   ownerGrantCurrent profile config authority height ready.spec.packageManifest ready.spec.owner
     ready.spec.packageOwnerCapability,
   controlGrantCurrent profile config authority height ready.spec.packageManifest ready.spec.owner
     ready.spec.packageControlCapability,
   ownerGrantCurrent profile config authority height ready.spec.snapshotManifest ready.spec.owner
     ready.spec.snapshotOwnerCapability,
   controlGrantCurrent profile config authority height ready.spec.snapshotManifest ready.spec.owner
     ready.spec.snapshotControlCapability]

def Ready.policyRecords {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) : List PolicyRecord :=
  [NativeHostGenesis.policy profile config ready.spec.app
      (ApplicationGrain.policy ready.spec.packageManifest ready.spec.snapshotManifest
        (.eq "request/subject" ready.spec.owner.value)),
   NativeHostGenesis.policy profile config ready.spec.packageManifest
      (ApplicationGrain.packageManifestPolicy ready.spec.app
        (.eq "request/subject" ready.spec.owner.value)),
   NativeHostGenesis.policy profile config ready.spec.snapshotManifest
      (ApplicationGrain.snapshotManifestPolicy ready.spec.app
        (.eq "request/subject" ready.spec.owner.value))]

private def initialPolicy (record : PolicyRecord) : InitialPolicy :=
  ⟨record.policyId, PolicyRecordCodec.digest record, PolicyRecordCodec.encode record⟩

def Ready.initialPolicies {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) : List InitialPolicy :=
  (ready.policyRecords profile config).map initialPolicy

/-- The complete three-resource birth draft uses the same identity and fee
calculation as Host.Json.birth. The existing birth receiver, not this helper,
checks current factory law, exact grants, source bytes and physical placement. -/
def Ready.descriptor {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) (height : Nat)
    (creator : SubjectId) (nonce payer : Nat)
    (funding : List InitialFunding := []) :
    Descriptor CanonicalCellRegistry.registry :=
  let identity := ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
    config.deployment creator nonce
  let draft : Descriptor CanonicalCellRegistry.registry :=
    { factory := ⟨config.deployment.factoryId⟩, creator := creator,
      transactionId := identity, nonce := nonce,
      births := ready.births config, auxiliaryCreates := [],
      grants := ready.grants profile config height,
      initialPolicies := ready.initialPolicies profile config,
      authorityNullifier := identity.value,
      funding := funding,
      fee := ⟨payer, config.tariff.collector, config.tariff.asset, 0⟩ }
  { draft with fee := { draft.fee with amount := draft.quotedFee config.tariff } }

/-- Loaded-state authoring alters only the authority epochs and the resulting
quoted fee. The birth cells, policies, identities and funding are unchanged. -/
def Ready.descriptorCurrent {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) (authority : AuthState) (height : Nat)
    (creator : SubjectId) (nonce payer : Nat)
    (funding : List InitialFunding := []) :
    Descriptor CanonicalCellRegistry.registry :=
  let previous := ready.descriptor profile config height creator nonce payer funding
  let updated := { previous with grants := ready.grantsCurrent profile config authority height }
  let draft := { updated with fee := { updated.fee with amount := 0 } }
  { draft with fee := { draft.fee with amount := draft.quotedFee config.tariff } }

theorem Ready.descriptorCurrent_grants {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) (authority : AuthState) (height : Nat)
    (creator : SubjectId) (nonce payer : Nat) (funding : List InitialFunding) :
    (ready.descriptorCurrent profile config authority height creator nonce payer funding).grants =
      ready.grantsCurrent profile config authority height := rfl

theorem Ready.current_grant_count {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) (authority : AuthState) (height : Nat) :
    (ready.grantsCurrent profile config authority height).length = 6 := rfl

theorem Ready.birth_count (ready : Ready) (config : NativeHostGenesis.Config) :
    (ready.births config).length = 3 := rfl

theorem Ready.grant_count {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) (height : Nat) :
    (ready.grants profile config height).length = 6 := rfl

theorem Ready.policy_count {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) :
    (ready.initialPolicies profile config).length = 3 := rfl

end Minidregg.Kernel.ApplicationGrainBirth
