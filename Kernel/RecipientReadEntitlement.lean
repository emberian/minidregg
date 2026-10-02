/- Recipient entitlement without a live query signature. `checkView` certifies
the exact indexed materialized
candidate/current view chosen by a source-owned outer controller. Neither
manufactures Authorized nor releases bytes. Candidate provenance, authenticated
complete enrollment/device records and final CAS composition remain outer
controller obligations. The genesisHeight argument is a deployment receiver
parameter, never an untrusted request value. -/
import Kernel.ResourceObservationAdmission
import Compiler.ObjectAudienceRoster
import Kernel.ResourceTransaction
import Compiler.PhysicalLawResolution
import Compiler.WorldKindLawDependencies
namespace Minidregg.Kernel.RecipientReadEntitlement
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialLineageAdmission
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false
abbrev Entry := Minidregg.Theory.ObjectAudienceRoster.Entry
variable {F : Type} [Field F] [DecidableEq F]
variable {deployment : ResourceObservationAdmission.Deployment}
variable {durable : ResourceObservationAdmission.Durable}
variable {context : ResourceObservationAdmission.Context deployment durable}
variable {profile : CanonicalRuntimeProfile.Profile F}
variable {wanted : Request .object} {marker : Nat} {capability : CapabilityId}
variable {contextBytes : List UInt8}
abbrev Preparation := ResourceObservationAdmission.Prepared context profile wanted marker capability contextBytes
/-- All-field access is deliberately conservative: a whole opaque payload must
not be distributed under a grant authorizing only one narrowed field. -/
def entryMatches (entry : Entry) (stored : StoredCapability .object) : Prop :=
  entry.subject = wanted.subject.value ∧ entry.capability = capability.value ∧
  stored.head.id = capability ∧ stored.head.holder = .subject wanted.subject ∧
  wanted.subjectKeyEpoch = context.authority.snapshot.authState.subjectKeyEpoch wanted.subject ∧
  stored.head.scope.fields = none
instance (e : Entry) (s : StoredCapability .object) : Decidable (entryMatches (wanted := wanted) (capability := capability) (context := context) e s) := by
  unfold entryMatches; infer_instance
/-- Kind exports are derived from the actual old physical instance. The outer
controller proves the candidate post preserves that immutable descriptor. -/
def composedConfig (prepared : Preparation (context := context) (profile := profile)
    (wanted := wanted) (marker := marker) (capability := capability) (contextBytes := contextBytes))
    (view : Minidregg.Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry)
    (step : PolicyStepContext) : Option (ComposedPolicyAdmission.Config F) :=
  if preserved : CanonicalCellRegistry.instanceBinding prepared.observed.before =
      CanonicalCellRegistry.instanceBinding view then
    match WorldKindLawDependencies.loadPost deployment
      context.directory.directory wanted.target.value prepared.observed.before view
      prepared.observed.present preserved with
    | none => none
    | some dependencies =>
      some (PhysicalLawResolution.config profile.compilerProfile context.authority.snapshot
        context.directory.directory (sourceCapabilityPortal context.authority.snapshot marker)
        step wanted.target.value dependencies.additional)
  else none

/-- Guard the full authenticated closure (including historical source chains),
kind definition/instance lifecycle, authority, clock and current resource image.
No request-selected list may replace the source-derived kind dependencies. -/
def readGuards (prepared : Preparation (context := context) (profile := profile)
    (wanted := wanted) (marker := marker) (capability := capability) (contextBytes := contextBytes)) : Option (List ReadGuard) := do
  let dependencies ← WorldKindLawDependencies.loadTarget deployment
    context.directory.directory wanted.target.value
  let sources ← PhysicalLawResolution.readGuards context.authority.snapshot
    context.directory.directory profile.semantics wanted.target.value dependencies.additional
  pure (context.authority.readGuards ++ [prepared.clock.readGuard,
    ⟨⟨wanted.target.value⟩, durable.snapshot.model.roots ⟨wanted.target.value⟩⟩] ++
    (dependencies.readGuards ++ sources).map (fun guard => ⟨⟨guard.1⟩, guard.2⟩))

/-- The view is an exact materialized resource selected by a source-owned outer
controller: current observation or actual validated transaction post. This API
certifies that indexed view, not its provenance or permission to publish. -/
def viewRequest (view : Minidregg.Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry) : Request .object :=
  { wanted with preStateRoot := view.payload.root }

def viewProject (prepared : Preparation (context := context) (profile := profile)
    (wanted := wanted) (marker := marker) (capability := capability) (contextBytes := contextBytes))
    (view : Minidregg.Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry)
    (logical : Minidregg.Theory.Store.Store (CanonicalCellRegistry.layout view.1)) : Minidregg.Pred.State :=
  ⟨[("target/storageKind", Int.ofNat view.1.tag.toNat)] ++
    Kernel.ClockCell.slots prepared.clock.clock ++
    CanonicalRuntimeProfile.requestSlots (viewRequest (wanted := wanted) view) ++
    ResourceAuthorityProjection.bytesSlots "context/bytes" 0 contextBytes ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      ((CanonicalCellRegistry.materializer view.1).codec.encode logical) ++
    ResourceAuthorityProjection.bytesSlots "account/bytes" 0
      (CanonicalAccountView.balanceStream.encode []) ++
    ResourceObservationAdmission.resourceSlots wanted.subject wanted.target.value view.1 logical⟩

def viewStep (prepared : Preparation (context := context) (profile := profile)
    (wanted := wanted) (marker := marker) (capability := capability) (contextBytes := contextBytes))
    (view : Minidregg.Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (viewProject prepared view) profile.semantics
    (ResourceObservationAdmission.readCandidate (viewRequest (wanted := wanted) view)
      view.1 view.payload rfl)

def viewConfig (prepared : Preparation (context := context) (profile := profile)
    (wanted := wanted) (marker := marker) (capability := capability) (contextBytes := contextBytes))
    (view : Minidregg.Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry) :
    Option (ComposedPolicyAdmission.Config F) :=
  composedConfig prepared view (viewStep prepared view)

structure CheckedView (genesisHeight : Nat) (prepared : Preparation (context := context) (profile := profile)
    (wanted := wanted) (marker := marker) (capability := capability) (contextBytes := contextBytes)) (entry : Entry)
    (view : Minidregg.Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry) : Type where
  private mk ::
  heightExact : wanted.height = genesisHeight + durable.height
  objectRole : view.1 = .content ∨ view.1 = .declaredObject ∨ view.1 = .stream ∨ view.1 = .worldInstance
  stored : StoredCapability .object
  storedExact : readCapability context.authority.snapshot.cell .object capability = some stored
  principal : entryMatches (wanted := wanted) (capability := capability) (context := context) entry stored
  lineage : storedLineageCheck context.authority.snapshot.cell context.authority.snapshot.authState.parent stored = true
  admissible : capabilityAdmissibleCheck stored.head context.authority.snapshot.authState
    (viewRequest (wanted := wanted) view) = true
  witness : ComposedPolicyAdmission.Witness F
  /-- The composed portal is reconstructed from the indexed physical view.
  Keep its exact acceptance as proof, not a Type-1 runtime portal value. -/
  law : ∃ config : ComposedPolicyAdmission.Config F,
    viewConfig prepared view = some config ∧
    config.verifies (viewRequest (wanted := wanted) view) witness = true
  guards : List ReadGuard
  guardsExact : readGuards prepared = some guards

def checkView (genesisHeight : Nat) (prepared : Preparation (context := context) (profile := profile)
    (wanted := wanted) (marker := marker) (capability := capability) (contextBytes := contextBytes)) (entry : Entry)
    (view : Minidregg.Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry) :
    Option (CheckedView genesisHeight prepared entry view) := do
  if heightExact : wanted.height = genesisHeight + durable.height then
   if role : view.1 = .content ∨ view.1 = .declaredObject ∨ view.1 = .stream ∨ view.1 = .worldInstance then
    match selected : readCapability context.authority.snapshot.cell .object capability with
    | none => none
    | some stored =>
      if principal : entryMatches (wanted := wanted) (capability := capability) (context := context) entry stored then
       if lineage : storedLineageCheck context.authority.snapshot.cell context.authority.snapshot.authState.parent stored = true then
        if admissible : capabilityAdmissibleCheck stored.head context.authority.snapshot.authState
            (viewRequest (wanted := wanted) view) = true then
         match configExact : viewConfig prepared view with
         | none => none
         | some config =>
          match config.witness? with
          | none => none
          | some witness =>
           if law : config.verifies (viewRequest (wanted := wanted) view) witness = true then
            match guardsExact : readGuards prepared with
            | none => none
            | some guards =>
              some ⟨heightExact, role, stored, selected, principal, lineage, admissible,
                witness, ⟨config, configExact, law⟩, guards, guardsExact⟩
           else none
        else none
       else none
      else none
   else none
  else none

/-- Current observer-image compatibility entry point, sharing the exact same
composed entitlement and physical guard construction as candidate views. -/
abbrev Checked (genesisHeight : Nat) (prepared : Preparation (context := context) (profile := profile)
    (wanted := wanted) (marker := marker) (capability := capability) (contextBytes := contextBytes)) (entry : Entry) :=
  CheckedView genesisHeight prepared entry prepared.observed.before

def check (genesisHeight : Nat) (prepared : Preparation (context := context) (profile := profile)
    (wanted := wanted) (marker := marker) (capability := capability) (contextBytes := contextBytes)) (entry : Entry) :
    Option (Checked genesisHeight prepared entry) :=
  checkView genesisHeight prepared entry prepared.observed.before

/-- This wrapper derives exact post bytes from actual validated computation;
callers cannot replace that post with an independent payload. -/
def transactionPost {directory : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry}
    {snapshot : DeclaredResourceController.AuthoritySnapshot} {semantics : Digest}
    {ambient : DeclaredResourceController.Ambient} {command : DeclaredResourceController.Command}
    {target : DeclaredResourceController.Target}
    (prepared : DeclaredResourceController.PreparedTarget deployment directory snapshot semantics ambient command target) :
    Minidregg.Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry :=
  DeclaredResourceController.packTarget target prepared.candidate.post
end Minidregg.Kernel.RecipientReadEntitlement
