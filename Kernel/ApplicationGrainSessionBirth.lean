/- Source-owned two-resource session and enrollment-descriptor birth draft.
Native factory admission still checks all current grants, sources, charge,
uniqueness and durable receiving. Initial descriptor content is empty; explicit
authorized enrollment creates a canonical stable atom, then each governed
renewal edits that atom with the new generation-bound payload. -/
import Kernel.ApplicationGrainSession
import Kernel.ApplicationGrainSessionEnrollment
import Kernel.NativeHostGenesis
import Kernel.ResourceBirthController
import Kernel.ContentResource

namespace Minidregg.Kernel.ApplicationGrainSessionBirth
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.DeclaredEffectPageMaterializer
open Minidregg.Compiler.HyperdocumentContentPageMaterializer
set_option autoImplicit false

structure Spec where
  app : Nat
  session : Nat
  descriptor : Nat
  participant : SubjectId
  kind : ApplicationGrainSession.Kind
  sessionOwnerCapability : CapabilityId
  sessionControlCapability : CapabilityId
  descriptorOwnerCapability : CapabilityId
  descriptorControlCapability : CapabilityId
  deriving DecidableEq, Repr

def Spec.targets (spec : Spec) : List Nat :=
  [spec.app, spec.session, spec.descriptor]

def Spec.capabilities (spec : Spec) : List CapabilityId :=
  [spec.sessionOwnerCapability, spec.sessionControlCapability,
   spec.descriptorOwnerCapability, spec.descriptorControlCapability]

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
  else .error "session, app, descriptor and capability IDs must be distinct"

theorem Ready.targets_distinct (ready : Ready) : ready.spec.targets.Nodup := ready.valid.1

theorem Ready.capabilities_distinct (ready : Ready) :
    ready.spec.capabilities.Nodup := ready.valid.2

private def sessionCell (config : NativeHostGenesis.Config) (spec : Spec) :
    PackedCell CanonicalCellRegistry.registry :=
  ⟨.declaredObject, materialize DeclaredEffectPageMaterializer.materializer
    (DeclaredEffectPageMaterializer.stateOfOption
      (some (ApplicationGrainSession.initialPage config.deployment.domain
        spec.session spec.app spec.kind)))⟩

private def descriptorCell (config : NativeHostGenesis.Config) (target : Nat) :
    PackedCell CanonicalCellRegistry.registry :=
  ⟨.content, materialize HyperdocumentContentPageMaterializer.materializer
    (HyperdocumentContentPageMaterializer.stateOfOption
      (some (ContentResource.initialPage config.deployment.domain target)))⟩

private def birthItem (target : Nat) (owner : SubjectId)
    (cell : PackedCell CanonicalCellRegistry.registry) :
    BirthItem CanonicalCellRegistry.registry :=
  ⟨⟨target, CellSlot.root CanonicalCellRegistry.registry .absent, cell⟩, .object, owner⟩

def Ready.births (ready : Ready) (config : NativeHostGenesis.Config) :
    List (BirthItem CanonicalCellRegistry.registry) :=
  [birthItem ready.spec.session ready.spec.participant (sessionCell config ready.spec),
   birthItem ready.spec.descriptor ready.spec.participant
     (descriptorCell config ready.spec.descriptor)]

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
  [ownerGrant profile config height ready.spec.session ready.spec.participant
     ready.spec.sessionOwnerCapability,
   controlGrant profile config height ready.spec.session ready.spec.participant
     ready.spec.sessionControlCapability,
   ownerGrant profile config height ready.spec.descriptor ready.spec.participant
     ready.spec.descriptorOwnerCapability,
   controlGrant profile config height ready.spec.descriptor ready.spec.participant
     ready.spec.descriptorControlCapability]

def Ready.policyRecords {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) : List PolicyRecord :=
  [NativeHostGenesis.policy profile config ready.spec.session
      (ApplicationGrainSession.policy ready.spec.descriptor ready.spec.kind
        ready.spec.participant (.eq "request/subject" ready.spec.participant.value)),
   NativeHostGenesis.policy profile config ready.spec.descriptor
      (ApplicationGrainSession.descriptorPolicy ready.spec.session ready.spec.kind
        ready.spec.participant (.eq "request/subject" ready.spec.participant.value))]

private def initialPolicy (record : PolicyRecord) : InitialPolicy :=
  ⟨record.policyId, PolicyRecordCodec.digest record, PolicyRecordCodec.encode record⟩

def Ready.initialPolicies {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) : List InitialPolicy :=
  (ready.policyRecords profile config).map initialPolicy

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

theorem Ready.birth_count (ready : Ready) (config : NativeHostGenesis.Config) :
    (ready.births config).length = 2 := rfl

theorem Ready.grant_count {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) (height : Nat) :
    (ready.grants profile config height).length = 4 := rfl

theorem Ready.policy_count {F : Type} [Field F]
    (ready : Ready) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHostGenesis.Config) :
    (ready.initialPolicies profile config).length = 2 := rfl

end Minidregg.Kernel.ApplicationGrainSessionBirth
