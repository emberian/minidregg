/-
Current-image preparation for a one-shot lifecycle claim. The claim command
uses the original BEGIN subject and mutation capability; today's installed
v2 management law, app state and package content are independently checked
on the same loaded image. This lower check does not submit a durable intent
or permit a host launch.
-/
import Kernel.ApplicationLifecycleClaimHistory
import Kernel.PhysicalResourceReadGuard
import Kernel.ResourceObservationAdmission

namespace Minidregg.Kernel.ApplicationLifecycleClaimCurrent

open Minidregg.Compiler
open Minidregg.Compiler.IntStream (intStream)
open Minidregg.Compiler.CanonicalCellRegistry
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationLifecycleClaim

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Ambient := DeclaredResourceController.Ambient
abbrev Durable := DeclaredResourceController.Durable

def appState (app : Nat) (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationGrain.State := do
  match cell with
  | ⟨.declaredObject, payload⟩ =>
      let page := payload.logical
      ApplicationGrain.readState app page
  | _ => none

/-- Claim requires the currently installed v2 management law. V1 remains
available solely for historical BEGIN replay at the original prefix. -/
def linkedCurrentPolicy {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (source : Source)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command deployment.domain profile.semantics source)) : Bool :=
  let auth := prepared.authority.snapshot.logical
  let directory := prepared.directory.directory
  let appPolicy := do
    let head ← CredentialAuthorityDomain.headAt auth ⟨source.begin.source.app⟩
    let policy ← CanonicalCellRegistry.loadPolicySource deployment.domain directory head.address
    if policy.record.policyId == ⟨source.begin.source.app⟩ &&
        policy.record.version == head.version &&
        policy.record.semantics == profile.semantics then
      pure policy.record.predicate
    else none
  let packagePolicy := do
    let head ← CredentialAuthorityDomain.headAt auth ⟨source.begin.source.packageManifest⟩
    let policy ← CanonicalCellRegistry.loadPolicySource deployment.domain directory head.address
    if policy.record.policyId == ⟨source.begin.source.packageManifest⟩ &&
        policy.record.version == head.version &&
        policy.record.semantics == profile.semantics then
      pure policy.record.predicate
    else none
  let management := Minidregg.Pred.Pred.eq "request/subject"
    source.begin.source.managementSubject.value
  appPolicy == some (ApplicationGrain.policy source.begin.source.packageManifest
    source.begin.source.snapshotManifest management) &&
  packagePolicy == some (ApplicationGrain.packageManifestPolicy source.begin.source.app
    management)

def observationRequest {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (source : Source)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command deployment.domain profile.semantics source))
    (resource : Nat) (capability : CapabilityId) (root : Digest) : Request .object :=
  let target : DeclaredResourceController.Target :=
    ⟨.object, resource, capability, 1, root, .content ⟨[]⟩, none, none, none⟩
  { DeclaredResourceController.requestFor prepared.authority.snapshot profile.semantics
      ambient (command deployment.domain profile.semantics source) target root with
    verb := .observeObject }

def observationGuard (resource : Nat)
    (before : PackedCell CanonicalCellRegistry.registry) : ReadGuard :=
  ⟨⟨resource⟩, ResourceBirthCodec.physicalRoot (.live before)⟩

structure CheckedRead {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (source : Source)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command deployment.domain profile.semantics source))
    (resource : Nat) (capability : CapabilityId) (root : Digest)
    (envelope : List UInt8) where
  private mk ::
  selected : ResourceObservationAdmission.Prepared
    (DeclaredResourceController.readContext prepared) profile
    (observationRequest deployment profile ambient durable source prepared
      resource capability root)
    (DeclaredResourceController.operationMarker deployment.domain profile.semantics
      (command deployment.domain profile.semantics source))
    capability source.canonicalBytes
  checked : ResourceObservationAdmission.Checked selected envelope
  current : (observationGuard resource selected.observed.before).expectedRoot =
    durable.snapshot.model.roots
      (observationGuard resource selected.observed.before).cellId

def checkRead {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (durable : Durable) (source : Source)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command deployment.domain profile.semantics source))
    (resource : Nat) (capability : CapabilityId) (root : Digest)
    (envelope : List UInt8) :
    IO (Except String (CheckedRead deployment profile ambient durable source prepared
      resource capability root envelope)) := do
  let wanted := observationRequest deployment profile ambient durable source prepared
    resource capability root
  let context := DeclaredResourceController.readContext prepared
  let marker := DeclaredResourceController.operationMarker deployment.domain profile.semantics
    (command deployment.domain profile.semantics source)
  match ResourceObservationAdmission.prepare context profile wanted marker
      capability source.canonicalBytes with
  | .error _ => return .error "current lifecycle claim observation refused"
  | .ok selected =>
      match ← ResourceObservationAdmission.check native selected envelope with
      | .error _ => return .error "signed lifecycle claim observation refused"
      | .ok checked =>
          have current : (observationGuard resource selected.observed.before).expectedRoot =
              durable.snapshot.model.roots
                (observationGuard resource selected.observed.before).cellId :=
            PhysicalResourceReadGuard.current context.directory resource
              selected.observed.before selected.observed.present
          return .ok ⟨selected, checked, current⟩

/-- All fresh authority is current: original mutation cap under today's v2
management law, two separately signed observations and exact old physical
roots. Historical BEGIN admission is a distinct prerequisite in ClaimHistory. -/
structure Accepted {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable)
    (ingress : ApplicationLifecycleClaimIngress.Ingress) where
  sourceValid : ingress.source.valid = true
  profileExact : ingress.domain = deployment.domain ∧
    ingress.semantics = profile.semantics
  boundary : ingress.source.currentWorldRoot =
    durable.worldRoot
  prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
    (command deployment.domain profile.semantics ingress.source)
  linked : linkedCurrentPolicy deployment profile ambient durable ingress.source prepared = true
  shape : DeclaredResourceController.PhysicalShape prepared
  appRead : CheckedRead deployment profile ambient durable ingress.source prepared
    ingress.source.begin.source.app ingress.source.appObserveCapability
    ingress.source.currentAppRoot ingress.appObservationEnvelope
  appExact : appState ingress.source.begin.source.app appRead.selected.observed.before =
    some ingress.source.before
  packageRead : CheckedRead deployment profile ambient durable ingress.source prepared
    ingress.source.begin.source.packageManifest ingress.source.packageObserveCapability
    ingress.source.currentPackageRoot ingress.packageObservationEnvelope
  packageReadOnly :
    (observationGuard ingress.source.begin.source.packageManifest
      packageRead.selected.observed.before).cellId ∉
      (DeclaredResourceController.writes prepared).map DataWrite.cellId
  packageContent : packageRead.selected.observed.before.kind = .content
  installed : ApplicationLifecycleBeginReceiver.installedPackageMatches deployment
    ingress.source.begin.source packageRead.selected.observed.before = true
  invocation : DeclaredResourceController.AcceptedInvocation prepared ingress.signed

theorem stale_app_root_has_no_admission {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable}
    {ingress : ApplicationLifecycleClaimIngress.Ingress}
    (stale : ∀ before : PackedCell CanonicalCellRegistry.registry,
      ingress.source.currentAppRoot = before.payload.root →
        (observationGuard ingress.source.begin.source.app before).expectedRoot ≠
          durable.snapshot.model.roots
            (observationGuard ingress.source.begin.source.app before).cellId) :
    ¬ Nonempty (Accepted deployment profile ambient durable ingress) := by
  rintro ⟨accepted⟩
  exact stale accepted.appRead.selected.observed.before
    accepted.appRead.selected.observed.rootExact accepted.appRead.current

theorem stale_image_boundary_has_no_admission {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable}
    {ingress : ApplicationLifecycleClaimIngress.Ingress}
    (stale : ingress.source.currentWorldRoot ≠
      durable.worldRoot) :
    ¬ Nonempty (Accepted deployment profile ambient durable ingress) := by
  rintro ⟨accepted⟩
  exact stale accepted.boundary

def admitLoaded {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (durable : Durable) (ingress : ApplicationLifecycleClaimIngress.Ingress) :
    IO (Except String (Accepted deployment profile ambient durable ingress)) := do
  let source := ingress.source
  if sourceValid : source.valid = true then
    if profileExact : ingress.domain = deployment.domain ∧
        ingress.semantics = profile.semantics then
      if boundary : source.currentWorldRoot =
          durable.worldRoot then
        let expected := command deployment.domain profile.semantics source
        unless ingress.signed.commandBytes ==
            DeclaredResourceController.commandCodec.encode expected do
          return .error "signed claim command differs from source"
        match DeclaredResourceController.prepare deployment profile ambient durable expected with
        | .error _ => return .error "current lifecycle claim preparation refused"
        | .ok prepared =>
            if linked : linkedCurrentPolicy deployment profile ambient durable source prepared = true then
              if shape : DeclaredResourceController.PhysicalShape prepared then
                let appResult ← checkRead deployment profile ambient native durable source
                  prepared source.begin.source.app source.appObserveCapability
                  source.currentAppRoot ingress.appObservationEnvelope
                match appResult with
                | .error detail => return .error detail
                | .ok appRead =>
                    if appExact : appState source.begin.source.app
                        appRead.selected.observed.before = some source.before then
                      let packageResult ← checkRead deployment profile ambient native durable
                        source prepared source.begin.source.packageManifest
                        source.packageObserveCapability source.currentPackageRoot
                        ingress.packageObservationEnvelope
                      match packageResult with
                      | .error detail => return .error detail
                      | .ok packageRead =>
                          if packageReadOnly :
                              (observationGuard source.begin.source.packageManifest
                                packageRead.selected.observed.before).cellId ∉
                                (DeclaredResourceController.writes prepared).map DataWrite.cellId then
                            if packageContent : packageRead.selected.observed.before.kind = .content then
                              if installed : ApplicationLifecycleBeginReceiver.installedPackageMatches
                                  deployment source.begin.source
                                  packageRead.selected.observed.before = true then
                                match ← DeclaredResourceController.admit native prepared ingress.signed with
                                | .error _ => return .error "current lifecycle claim authority refused"
                                | .ok invocation =>
                                    return .ok ⟨sourceValid, profileExact, boundary, prepared,
                                      linked, shape, appRead, appExact, packageRead,
                                      packageReadOnly, packageContent, installed, invocation⟩
                              else return .error "current installed package identity refused"
                            else return .error "package target is not content"
                          else return .error "package observation overlaps lifecycle writes"
                    else return .error "current pending application state refused"
              else return .error "lifecycle claim physical shape refused"
            else return .error "current v2 app/package policy linkage refused"
      else return .error "claim image boundary differs from loaded image"
    else return .error "claim domain or semantics differs from current deployment"
  else return .error "invalid lifecycle claim source"

end Minidregg.Kernel.ApplicationLifecycleClaimCurrent
