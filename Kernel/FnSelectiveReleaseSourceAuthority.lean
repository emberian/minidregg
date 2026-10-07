/-
Current source-law check for one selected public release. A signed observation
selects bytes for authoring; this distinct check requires the current source
`.delegateObject` capability, native request signature and installed policy
for a request that commits the exact owner packet and selected page root.
This module has no durable effect by itself. The publication receiver must
journal a separate event before an outbound fn POST is attributed to source
authority.
-/
import Kernel.FnSelectiveReleaseSourcePublication
import Kernel.ResourceObservationAdmission
import Kernel.PhysicalResourceReadGuard

namespace Minidregg.Kernel.FnSelectiveReleaseSourceAuthority

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.FnSelectiveRelease
open Minidregg.Kernel.FnSelectiveReleaseSignature
open Minidregg.Kernel.FnSelectiveReleaseSourcePublication

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := ResourceObservationAdmission.Durable
abbrev Context := ResourceObservationAdmission.Context

variable {deployment : Deployment}

private def currentContent (context : Context deployment)
    (spec : Spec) : Option (Digest × List UInt8) := do
  let .present packed := context.directory.slots
      spec.packet.release.source.resource | none
  match packed with
  | ⟨.content, materialized⟩ =>
      let atom : AtomId := ⟨⟨spec.packet.release.source.atom⟩⟩
      let record ← Hyperdocument.lookup materialized.logical .atoms atom
      if record.tombstonedAt.isNone then some (materialized.root, record.payload)
      else none
  | _ => none

variable {F : Type} [Field F] [DecidableEq F]

structure Prepared (context : Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (spec : Spec) where
  private mk ::
  root : Digest
  observed : ResourceTargetAdmission.Observed deployment context.directory
    .object spec.packet.release.source.resource root
  contentKind : observed.before.kind = .content
  physicalCurrent : ResourceBirthCodec.physicalRoot (.live observed.before) =
    context.view.model.roots ⟨spec.packet.release.source.resource⟩
  sourceDomain : spec.packet.release.source.domain = deployment.domain
  sourceSemantics : spec.packet.release.source.semantics = profile.semantics
  sourceRoot : spec.packet.release.source.parent = root
  selectedExact : currentContent context spec = some (root, spec.packet.release.content)

/-- Why a selected source publication is not prepared. The receiver answers every one of these with
the single undisclosed `"selected source publication refused"` (`undisclosed`), so a submitter
learns nothing about the Store from a refusal; the source's own operator, authoring the
publication locally (`Host.FnSelectiveReleaseSourceAuthoring`), is told which one (`describe`). -/
inductive PrepareRefusal where
  | packetShape | sourceAbsent | sourceUnobserved | notContent | foreignDomain
  | foreignSemantics | staleParent | selectedNotCurrent
  deriving DecidableEq, Repr

def PrepareRefusal.undisclosed (_ : PrepareRefusal) : String :=
  "selected source publication refused"

def PrepareRefusal.describe : PrepareRefusal → String
  | .packetShape => "selected source publication refused: the packet is not a 64-octet-signed, bounded, public-peerable release"
  | .sourceAbsent => "selected source publication refused: the source resource has no slot in this Store"
  | .sourceUnobserved => "selected source publication refused: the source resource cannot be observed at its current root"
  | .notContent => "selected source publication refused: the source resource is not a content resource"
  | .foreignDomain => "selected source publication refused: the release names another domain"
  | .foreignSemantics => "selected source publication refused: the release names other semantics"
  | .staleParent => "selected source publication refused: the release's parent root is not the source's current root"
  | .selectedNotCurrent => "selected source publication refused: the selected atom's current payload differs from the release content (or the atom is absent or tombstoned)"

def prepare (context : Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (spec : Spec) :
    Except PrepareRefusal (Prepared context profile federation height spec) :=
  if spec.packet.signature.length != 64 || !spec.packet.release.bounded ||
      spec.packet.release.destination.audience.visibility != .publicPeerable then
    .error .packetShape
  else match context.directory.slots spec.packet.release.source.resource with
  | .absent => .error .sourceAbsent
  | .present packed =>
      match ResourceTargetAdmission.observe deployment context.directory
          .object spec.packet.release.source.resource packed.payload.root with
      | none => .error .sourceUnobserved
      | some observed =>
          if contentKind : observed.before.kind = .content then
            let physicalCurrent := ServedBasis.Ground.physicalCurrent context
              spec.packet.release.source.resource observed.before observed.present
            if sourceDomain : spec.packet.release.source.domain = deployment.domain then
              if sourceSemantics : spec.packet.release.source.semantics = profile.semantics then
                if sourceRoot : spec.packet.release.source.parent = packed.payload.root then
                  if selectedExact : currentContent context spec =
                      some (packed.payload.root, spec.packet.release.content) then
                    .ok ⟨packed.payload.root, observed, contentKind, physicalCurrent,
                      sourceDomain, sourceSemantics, sourceRoot, selectedExact⟩
                  else .error .selectedNotCurrent
                else .error .staleParent
              else .error .foreignSemantics
            else .error .foreignDomain
          else .error .notContent

variable {context : Context deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
  {height : Nat} {spec : Spec}

def Prepared.wanted (_prepared : Prepared context profile federation height spec) :
    Request .object :=
  sourceRequest deployment.domain profile.semantics federation
    context.authority.authState height spec

def project (prepared : Prepared context profile federation height spec)
    (logical : Store.Store (CanonicalCellRegistry.layout prepared.observed.before.kind)) :
    Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots context.directory spec.packet.release.source.resource ++
    CanonicalRuntimeProfile.requestSlots prepared.wanted ++
    ResourceAuthorityProjection.bytesSlots "context/bytes" 0 (sourceBytes spec) ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      ((CanonicalCellRegistry.materializer prepared.observed.before.kind).codec.encode logical) ++
    ResourceObservationAdmission.resourceSlots prepared.wanted.subject spec.packet.release.source.resource
      prepared.observed.before.kind logical⟩

def step (prepared : Prepared context profile federation height spec) :
    PolicyStepContext :=
  let rootExact : prepared.wanted.preStateRoot =
      prepared.observed.before.payload.root := by
    simpa [Prepared.wanted, sourceRequest] using
      prepared.sourceRoot.trans prepared.observed.rootExact
  PolicyStepContext.ofCandidate (project prepared) profile.semantics
    (ResourceObservationAdmission.readCandidate prepared.wanted
      prepared.observed.before.kind prepared.observed.before.payload
      rootExact)

def kindDependencies (prepared : Prepared context profile federation height spec) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment context.directory spec.packet.release.source.resource

def lawReadGuards (prepared : Prepared context profile federation height spec) :
    Option (List (Nat × Digest)) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards context.authority
    context.directory profile.semantics spec.packet.release.source.resource structural.additional
  pure (sources ++ structural.readGuards)

def policyConfig (prepared : Prepared context profile federation height spec) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile context.authority
    context.directory (sourceCapabilityPortal context.authority (marker spec))
    (step prepared) spec.packet.release.source.resource
    ((kindDependencies prepared).map (·.additional) |>.getD [])

def portal (prepared : Prepared context profile federation height spec) : Portal :=
  (policyConfig prepared).portal

def authorize (prepared : Prepared context profile federation height spec)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority) :
    Option (Authorized (portal prepared) context.authority.authState prepared.wanted) := do
  let config := policyConfig prepared
  let _ ← lawReadGuards prepared
  let evidence ← (config.capabilityEvidenceChecked prepared.wanted
    spec.delegateCapability () signature () (fun _ => ())).toOption
  let law ← config.resolve?
  ComposedPolicyAdmission.admit config prepared.wanted evidence law.witness
    (.policy prepared.wanted.policyId prepared.wanted.policyRevision)
    (by rfl) (by rfl)

/-- A public success cannot be obtained with missing source custody. -/
theorem authorize_requires_sources (prepared : Prepared context profile federation height spec)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority)
    (accepted : (authorize prepared signature).isSome = true) :
    (lawReadGuards prepared).isSome = true := by
  cases resolved : lawReadGuards prepared with
  | none => simp [authorize, resolved] at accepted
  | some guards => simp [resolved]

attribute [irreducible] portal

structure Checked (prepared : Prepared context profile federation height spec)
    (envelope : List UInt8) where
  private mk ::
  signature : CredentialSignatureAdmission.CheckedSignature context.authority
  envelopeExact : signature.envelopeBytes = envelope
  authorization : Authorized (portal prepared) context.authority.authState
    prepared.wanted
  authorized : authorize prepared signature = some authorization

def check (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared context profile federation height spec)
    (envelope : List UInt8) : IO (Except String (Checked prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native context.authority
      (marker spec) prepared.wanted envelope with
  | .error _ => return .error "selected source publication refused"
  | .ok signature =>
      if exact : signature.envelopeBytes = envelope then
        match authorized : authorize prepared signature with
        | none => return .error "selected source publication refused"
        | some authorization =>
            return .ok ⟨signature, exact, authorization, authorized⟩
      else return .error "selected source publication refused"

/-- Complete source and structural custody. Authorization requires this exact
resolver result to exist before a Checked value can be constructed. -/
def readGuards (prepared : Prepared context profile federation height spec) :
    List DurableDataIntent.ReadGuard :=
  ((lawReadGuards prepared).getD []).map fun guard => ⟨⟨guard.1⟩, guard.2⟩

def readGuard (prepared : Prepared context profile federation height spec) :
    DurableDataIntent.ReadGuard :=
  ⟨⟨spec.packet.release.source.resource⟩,
    ResourceBirthCodec.physicalRoot (.live prepared.observed.before)⟩

theorem readGuard_current (prepared : Prepared context profile federation height spec) :
    (readGuard prepared).expectedRoot =
      context.view.model.roots (readGuard prepared).cellId :=
  prepared.physicalCurrent

end Minidregg.Kernel.FnSelectiveReleaseSourceAuthority
