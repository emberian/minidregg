/-
Source construction for a grain-backed resource birth. This module does not
admit a birth: the receiving composition must check both grain incidences,
the existing birth branches, and one coalesced authority update against the
same loaded durable image before emitting one DataIntent.

The tool settles a prior reservation. The parent is an exact, no-op witness
of its reserved generation. The conserved Book birth fee is independent of
the tool's permission-unit charge.
-/
import Kernel.AgentGrain
import Kernel.ResourceBirthController
import Kernel.DeclaredResourceController
import Compiler.ResourceBirthCodec
import Compiler.CredentialAuthorityDomainReceiver
import Compiler.GrainResourceBirthAuthority
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Compiler.GrainResourceBirthController

open Minidregg.Theory
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A future receiver must obtain this tariff from its pinned profile, never
from an untrusted birth request. The positive base rules out a free birth even
when the descriptor contains no additional resources. -/
structure Tariff where
  base : Nat
  perBirth : Nat
  positiveBase : 0 < base

def Tariff.charge (tariff : Tariff)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) : Nat :=
  tariff.base + tariff.perBirth * descriptor.births.length

theorem Tariff.charge_positive (tariff : Tariff)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) :
    0 < tariff.charge descriptor := by
  unfold Tariff.charge
  exact lt_of_lt_of_le tariff.positiveBase (Nat.le_add_right _ _)

/-- Only source coordinates live here. No supplied post-state, authority
projection, policy verdict, or physical write is accepted as a field. -/
structure Source where
  birth : ResourceBirth.Descriptor CanonicalCellRegistry.registry
  toolTask : Nat
  toolCapability : CapabilityId
  toolObserveCapability : CapabilityId
  toolRoot : Digest
  toolBefore : AgentGrain.State
  parentTask : Nat
  parentCapability : CapabilityId
  parentObserveCapability : CapabilityId
  parentRoot : Digest
  parentBefore : AgentGrain.State

/-- The parent action writes the same four-field state. Its current root,
generation, installed law, and delegated witness capability still require
native receiving admission; this constructor grants none of them. -/
def Source.parentTarget (source : Source) : DeclaredResourceController.Target :=
  AgentGrain.Operation.input.target source.parentTask source.parentCapability
    source.parentRoot source.parentBefore (some source.parentObserveCapability)

theorem Source.parent_after_exact (source : Source) :
    AgentGrain.Operation.input.after source.parentBefore = source.parentBefore := rfl

/-- Physical shard allocation must not alter the user-signed grain command.
The source commitment includes the complete user draft, including births,
grants, funding, fee and the user's birth identity. -/
def Source.userDraft (source : Source) :
    ResourceBirth.Descriptor CanonicalCellRegistry.registry :=
  { source.birth with auxiliaryCreates := [] }

def Source.grainNonce (source : Source) : Nat :=
  (Sp800185Cshake256.hash
    "DREGG/GRAIN-RESOURCE-BIRTH/USER-DRAFT-NONCE/v1".toUTF8.toList
    ((StreamCodec.product StreamCodec.nat bytesStream).encode
      (source.birth.nonce,
        (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode
          source.userDraft))).digest.value

/-- Exactly two existing resource incidences: settle the tool reservation and
carry the parent as an exact-state witness. The subject is the birth creator;
the nonce commits to the canonical user draft under the hash's collision
resistance assumption. The operation marker remains domain separated from
the birth identity. -/
def Source.grainCommand (tariff : Tariff) (source : Source) :
    DeclaredResourceController.Command :=
  AgentGrain.Operation.command (.settle (Int.ofNat (tariff.charge source.birth)))
    source.birth.creator source.grainNonce
    source.toolTask source.toolCapability source.toolRoot source.toolBefore
    [source.parentTarget] (some source.toolObserveCapability)

/-- Physical authority lowering may discover shard creates only after the
user draft is supplied. These creates cannot alter the two grain actions. -/
def Source.withAuxiliaryCreates (source : Source)
    (creates : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)) : Source :=
  { source with birth := { source.birth with auxiliaryCreates := creates } }

theorem Source.grainCommand_auxiliary_independent (tariff : Tariff) (source : Source)
    (creates : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)) :
    (source.withAuxiliaryCreates creates).grainCommand tariff = source.grainCommand tariff := rfl

theorem Source.grainCommand_subject (tariff : Tariff) (source : Source) :
    (source.grainCommand tariff).subject = source.birth.creator := rfl

theorem Source.grainCommand_nonce (tariff : Tariff) (source : Source) :
    (source.grainCommand tariff).nonce = source.grainNonce := rfl

theorem Source.grainCommand_targets (tariff : Tariff) (source : Source) :
    (source.grainCommand tariff).targets =
      [(.settle (Int.ofNat (tariff.charge source.birth)) : AgentGrain.Operation).target
          source.toolTask source.toolCapability source.toolRoot source.toolBefore
          (some source.toolObserveCapability), source.parentTarget] := rfl

theorem Source.tool_settlement_exact (tariff : Tariff) (source : Source) :
    ((AgentGrain.Operation.settle (Int.ofNat (tariff.charge source.birth))).after
      source.toolBefore).remaining =
        source.toolBefore.remaining + source.toolBefore.reserved -
          Int.ofNat (tariff.charge source.birth) ∧
    ((AgentGrain.Operation.settle (Int.ofNat (tariff.charge source.birth))).after
      source.toolBefore).reserved = 0 := by
  exact ⟨rfl, rfl⟩

/-- A future signed event and factory request must bind these complete bytes,
not merely the birth descriptor or a Rust-selected task ID. Both components
use the existing canonical codecs; the outer length framing prevents an
ambiguous concatenation. -/
def Source.canonicalBytes (tariff : Tariff) (source : Source) : List UInt8 :=
  "DREGG/GRAIN-RESOURCE-BIRTH/SOURCE/v1".toUTF8.toList ++
    (StreamCodec.product bytesStream bytesStream).encode
      ((ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode source.birth,
        DeclaredResourceController.commandCodec.encode (source.grainCommand tariff))

/-- A composite factory request is a distinct source-visible request over the
complete descriptor and grain command. The receiving policy projection must
expose these same bytes; the existing bare factory request is unchanged. -/
def Source.factoryRequest (tariff : Tariff) (source : Source)
    (pins : FactoryPins)
    (encoding : SourceEncoding CanonicalCellRegistry.registry)
    (oldAuthority : AuthState) (factoryPreRoot : Digest) (height : Height) :
    Request .object :=
  { ResourceBirth.factoryRequest pins encoding oldAuthority factoryPreRoot height source.birth with
    argsDigest := encoding.hashBytes
      ("DREGG/GRAIN-RESOURCE-BIRTH/ARGS/v1".toUTF8.toList ++ source.canonicalBytes tariff)
    effectsDigest := encoding.hashBytes
      ("DREGG/GRAIN-RESOURCE-BIRTH/EFFECTS/v1".toUTF8.toList ++ source.canonicalBytes tariff) }

theorem Source.factoryRequest_subject (tariff : Tariff) (source : Source)
    (pins : FactoryPins) (encoding : SourceEncoding CanonicalCellRegistry.registry)
    (oldAuthority : AuthState) (factoryPreRoot : Digest) (height : Height) :
    (source.factoryRequest tariff pins encoding oldAuthority factoryPreRoot height).subject =
      source.birth.creator := rfl

/-- Domain-separated existing replay markers are both retained. The receiving
path must install both in one durable intent, after checking they differ. -/
def Source.replayMarkers (domain semantics : Digest) (tariff : Tariff)
    (source : Source) : List Nat :=
  [source.birth.authorityNullifier,
    DeclaredResourceController.operationMarker domain semantics (source.grainCommand tariff)]

/-- The birth's grant batch is one patch of the one authority cell, generated
from the old store; both replay markers are consumed in the durable set by the
receiver's intent.  Authorizing its composite request remains a receiving
obligation. -/
def Source.authorityPatch (snapshot : CredentialAuthorityDomain.Snapshot)
    (source : Source) :
    Store.Patch CredentialAuthorityState.layout :=
  GrainResourceBirthAuthority.patch snapshot source.birth

theorem Source.authorityPatch_auxiliary_independent
    (snapshot : CredentialAuthorityDomain.Snapshot) (source : Source)
    (creates : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)) :
    (source.withAuxiliaryCreates creates).authorityPatch snapshot =
      source.authorityPatch snapshot := rfl

/-- This is only the checkable source shape. The receiver must establish that
both supplied roots and states are the actual old loaded cells and that the
current laws and signatures authorize the two incidences. -/
def SourceShape (domain semantics : Digest) (tariff : Tariff) (source : Source) : Prop :=
  source.toolTask ≠ source.parentTask ∧
  source.toolTask ∉ source.birth.births.map (fun item => item.create.cellId) ∧
  source.parentTask ∉ source.birth.births.map (fun item => item.create.cellId) ∧
  (source.toolBefore.status = 3 ∨ source.toolBefore.status = 4) ∧
  (source.parentBefore.status = 3 ∨ source.parentBefore.status = 4) ∧
  0 ≤ source.toolBefore.remaining ∧
  0 ≤ source.toolBefore.reserved ∧
  Int.ofNat (tariff.charge source.birth) ≤ source.toolBefore.reserved ∧
  0 < source.parentBefore.reserved ∧
  source.birth.authorityNullifier ≠
    DeclaredResourceController.operationMarker domain semantics (source.grainCommand tariff)

instance sourceShapeDecidable (domain semantics : Digest) (tariff : Tariff) (source : Source) :
    Decidable (SourceShape domain semantics tariff source) := by
  unfold SourceShape
  infer_instance

def checkSourceShape (domain semantics : Digest) (tariff : Tariff) (source : Source) :
    Option { actual : Source // SourceShape domain semantics tariff actual } :=
  if shape : SourceShape domain semantics tariff source then some ⟨source, shape⟩ else none

theorem checkSourceShape_iff (domain semantics : Digest) (tariff : Tariff) (source : Source) :
    (checkSourceShape domain semantics tariff source).isSome = true ↔
      SourceShape domain semantics tariff source := by
  by_cases shape : SourceShape domain semantics tariff source <;>
    simp [checkSourceShape, shape]

theorem tool_after_nonnegative (domain semantics : Digest) (tariff : Tariff) (source : Source)
    (shape : SourceShape domain semantics tariff source) :
    0 ≤ ((AgentGrain.Operation.settle (Int.ofNat (tariff.charge source.birth))).after
      source.toolBefore).remaining := by
  rcases shape with ⟨_, _, _, _, _, remaining, _, bounded, _, _⟩
  simp only [AgentGrain.Operation.after, AgentGrain.settle]
  omega

theorem tool_after_running (domain semantics : Digest) (tariff : Tariff) (source : Source)
    (shape : SourceShape domain semantics tariff source) :
    ((AgentGrain.Operation.settle (Int.ofNat (tariff.charge source.birth))).after
      source.toolBefore).status = 1 ∨
    ((AgentGrain.Operation.settle (Int.ofNat (tariff.charge source.birth))).after
      source.toolBefore).status = 2 := by
  rcases shape with ⟨_, _, _, status, _, _, _, _, _, _⟩
  rcases status with first | second
  · left
    simp [AgentGrain.Operation.after, AgentGrain.settle, first]
  · right
    simp [AgentGrain.Operation.after, AgentGrain.settle, second]

/-- One checked authority post for the birth grant batch and the tool
operation marker, as one patch of the one authority cell. It is
preparation only: current policy, capability, signature, factory and grain
incidences still need admission over the same durable image. -/
structure PreparedSourceAuthority {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (semantics : Digest) (tariff : Tariff) (source : Source) where
  private mk ::
  shape : SourceShape loaded.snapshot.domain semantics tariff source
  combined : GrainResourceBirthAuthority.Prepared profile deployment loaded
    source.birth (DeclaredResourceController.operationMarker loaded.snapshot.domain semantics
      (source.grainCommand tariff))

def prepareSourceAuthority {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (semantics : Digest) (tariff : Tariff) (source : Source) :
    Option (PreparedSourceAuthority profile deployment loaded semantics tariff source) := do
  if shape : SourceShape loaded.snapshot.domain semantics tariff source then
    let combined ← GrainResourceBirthAuthority.prepare profile deployment loaded
      source.birth (DeclaredResourceController.operationMarker loaded.snapshot.domain semantics
        (source.grainCommand tariff))
    some ⟨shape, combined⟩
  else none

def PreparedSourceAuthority.auxiliaryCreates {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {semantics : Digest} {tariff : Tariff} {source : Source}
    (prepared : PreparedSourceAuthority profile deployment loaded semantics tariff source) :
    List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry) :=
  prepared.combined.auxiliaryCreates

/-- The only high-level preparation entry fixes the operation marker from the
source-derived grain command. The lower controller's Nat parameter is never
an independent ingress field here. This is still preparation, not signature
or current-law admission. -/
structure PreparedSourceBirth {F : Type} [Field F]
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment) (pins : FactoryPins)
    (durable : ResourceBirthController.Concrete.Durable)
    (semantics : Digest) (tariff : Tariff) (source : Source) where
  private mk ::
  shape : SourceShape deployment.domain semantics tariff source
  prepared : ResourceBirthController.Concrete.PreparedGrainBirth profile deployment pins
    durable source.birth (DeclaredResourceController.operationMarker deployment.domain semantics
      (source.grainCommand tariff))

def prepareSourceBirth {F : Type} [Field F]
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F) (disabled : List Digest)
    (deployment : CanonicalCellRegistry.Deployment) (pins : FactoryPins)
    (durable : ResourceBirthController.Concrete.Durable)
    (semantics : Digest) (tariff : Tariff) (source : Source) :
    Except ResourceBirthController.Concrete.PreparationReject
      (PreparedSourceBirth profile deployment pins durable semantics tariff source) := do
  if shape : SourceShape deployment.domain semantics tariff source then
    let prepared ← ResourceBirthController.Concrete.prepareGrainBirth profile disabled deployment
      pins durable source.birth
      (DeclaredResourceController.operationMarker deployment.domain semantics
        (source.grainCommand tariff))
    .ok ⟨shape, prepared⟩
  else .error .authorityBatch

/-- The birth's authority patch validated at the loaded cell's own root. -/
def PreparedSourceBirth.authorityValidated {F : Type} [Field F]
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment} {pins : FactoryPins}
    {durable : ResourceBirthController.Concrete.Durable}
    {semantics : Digest} {tariff : Tariff} {source : Source}
    (prepared : PreparedSourceBirth profile deployment pins durable semantics tariff source) :
    CellState.ValidatedPatch CredentialAuthorityCell.materializer
      prepared.prepared.pre.authority.snapshot.cell
      prepared.prepared.pre.authority.snapshot.cell.root
      (source.authorityPatch prepared.prepared.pre.authority.snapshot) := by
  exact prepared.prepared.authorityCombined.checked.validated

end Minidregg.Compiler.GrainResourceBirthController
