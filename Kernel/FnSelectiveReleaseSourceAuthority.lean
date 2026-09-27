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

variable {deployment : Deployment} {durable : Durable}

private def currentContent (context : Context deployment durable)
    (spec : Spec) : Option (Digest × List UInt8) := do
  let .present packed := context.directory.directory.slots
      spec.packet.release.source.resource | none
  match packed with
  | ⟨.content, materialized⟩ =>
      let page ← HyperdocumentContentPageMaterializer.pageAt materialized.logical
      let atom : AtomId := ⟨⟨spec.packet.release.source.atom⟩⟩
      let record ← page.entries.findSome? fun entry => match entry with
        | HyperdocumentContentPageMaterializer.Entry.atom atomId record =>
            if atomId == atom then some record else none
        | _ => none
      if record.tombstonedAt.isNone then some (materialized.root, record.payload)
      else none
  | _ => none

variable {F : Type} [Field F] [DecidableEq F]

structure Prepared (context : Context deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (spec : Spec) where
  private mk ::
  root : Digest
  observed : ResourceTargetAdmission.Observed deployment context.directory.directory
    .object spec.packet.release.source.resource root
  contentKind : observed.before.kind = .content
  physicalCurrent : ResourceBirthCodec.physicalRoot (.live observed.before) =
    durable.snapshot.model.roots ⟨spec.packet.release.source.resource⟩
  sourceDomain : spec.packet.release.source.domain = deployment.domain
  sourceSemantics : spec.packet.release.source.semantics = profile.semantics
  sourceRoot : spec.packet.release.source.parent = root
  selectedExact : currentContent context spec = some (root, spec.packet.release.content)

def prepare (context : Context deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (spec : Spec) : Except String (Prepared context profile federation height spec) :=
  if spec.packet.signature.length != 64 || !spec.packet.release.bounded ||
      spec.packet.release.destination.audience.visibility != .publicPeerable then
    .error "selected source publication refused"
  else match context.directory.directory.slots spec.packet.release.source.resource with
  | .absent => .error "selected source publication refused"
  | .present packed =>
      match ResourceTargetAdmission.observe deployment context.directory.directory
          .object spec.packet.release.source.resource packed.payload.root with
      | none => .error "selected source publication refused"
      | some observed =>
          if contentKind : observed.before.kind = .content then
            let physicalCurrent := PhysicalResourceReadGuard.current context.directory
              spec.packet.release.source.resource observed.before observed.present
            if sourceDomain : spec.packet.release.source.domain = deployment.domain then
              if sourceSemantics : spec.packet.release.source.semantics = profile.semantics then
                if sourceRoot : spec.packet.release.source.parent = packed.payload.root then
                  if selectedExact : currentContent context spec =
                      some (packed.payload.root, spec.packet.release.content) then
                    .ok ⟨packed.payload.root, observed, contentKind, physicalCurrent,
                      sourceDomain, sourceSemantics, sourceRoot, selectedExact⟩
                  else .error "selected source publication refused"
                else .error "selected source publication refused"
              else .error "selected source publication refused"
            else .error "selected source publication refused"
          else .error "selected source publication refused"

variable {context : Context deployment durable}
  {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
  {height : Nat} {spec : Spec}

def Prepared.wanted (_prepared : Prepared context profile federation height spec) :
    Request .object :=
  sourceRequest deployment.domain profile.semantics federation
    context.authority.snapshot.authState height spec

def project (prepared : Prepared context profile federation height spec)
    (logical : LogicalState (CanonicalCellRegistry.schema prepared.observed.before.kind)) :
    Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots prepared.wanted ++
    ResourceAuthorityProjection.bytesSlots "context/bytes" 0 (sourceBytes spec) ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      ((CanonicalCellRegistry.materializer prepared.observed.before.kind).codec.encode logical) ++
    ResourceObservationAdmission.resourceSlots spec.packet.release.source.resource
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

def policyConfig (prepared : Prepared context profile federation height spec) :
    CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile
    context.authority.snapshot (ResourceObservationAdmission.sourceStore context)
    (sourceCapabilityPortal context.authority.snapshot (marker spec))
    (step prepared)

def portal (prepared : Prepared context profile federation height spec) : Portal :=
  (policyConfig prepared).portal

def authorize (prepared : Prepared context profile federation height spec)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot) :
    Option (Authorized (portal prepared) context.authority.snapshot.authState prepared.wanted) := do
  let config := policyConfig prepared
  let evidence ← sourceCapabilityOnlyEvidence profile.compilerProfile
    context.authority.snapshot (ResourceObservationAdmission.sourceStore context)
    (marker spec) (step prepared) prepared.wanted
    spec.delegateCapability signature
  let committed ← config.registry.resolve prepared.wanted.policyId
    prepared.wanted.policyRevision
  let witness := canonicalWitness profile.compilerProfile.compiler committed
    (step prepared).oldState (step prepared).newState
  CanonicalPolicyAdmission.admit config context.authority.snapshot.authState
    prepared.wanted evidence witness
    (.policy prepared.wanted.policyId prepared.wanted.policyRevision)
    (by rfl) (by rfl)

attribute [irreducible] portal

structure Checked (prepared : Prepared context profile federation height spec)
    (envelope : List UInt8) where
  private mk ::
  signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot
  envelopeExact : signature.envelopeBytes = envelope
  authorization : Authorized (portal prepared) context.authority.snapshot.authState
    prepared.wanted
  authorized : authorize prepared signature = some authorization

def check (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared context profile federation height spec)
    (envelope : List UInt8) : IO (Except String (Checked prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native context.authority.snapshot
      (marker spec) prepared.wanted envelope with
  | .error _ => return .error "selected source publication refused"
  | .ok signature =>
      if exact : signature.envelopeBytes = envelope then
        match authorized : authorize prepared signature with
        | none => return .error "selected source publication refused"
        | some authorization =>
            return .ok ⟨signature, exact, authorization, authorized⟩
      else return .error "selected source publication refused"

def readGuard (prepared : Prepared context profile federation height spec) :
    DurableDataIntent.ReadGuard :=
  ⟨⟨spec.packet.release.source.resource⟩,
    ResourceBirthCodec.physicalRoot (.live prepared.observed.before)⟩

theorem readGuard_current (prepared : Prepared context profile federation height spec) :
    (readGuard prepared).expectedRoot =
      durable.snapshot.model.roots (readGuard prepared).cellId :=
  prepared.physicalCurrent

end Minidregg.Kernel.FnSelectiveReleaseSourceAuthority
