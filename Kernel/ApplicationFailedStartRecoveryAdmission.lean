/- One-current-image recovery admission: configured physical custodian, exact historical claim, current app/package reads, installed laws and current signed management authorization. It produces no physical effect or CAS by itself. -/
import Kernel.ApplicationFailedStartRecoveryHistory
import Kernel.ApplicationFailedStartRecoveryIngress
import Kernel.ApplicationFailedStartRecoveryPolicy
import Kernel.ApplicationLifecycleClaimCurrent
import Kernel.PhysicalResourceReadGuard
import Kernel.ResourceObservationAdmission

namespace Minidregg.Kernel.ApplicationFailedStartRecoveryAdmission

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalCellRegistry
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

def appState (app : Nat) (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationGrain.State :=
  ApplicationLifecycleClaimCurrent.appState app cell

def currentCell {F : Type} [Field F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {durable : DeclaredResourceController.Durable}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile
      ambient durable command) (resource : Nat) :
    Option (PackedCell CanonicalCellRegistry.registry) :=
  match prepared.directory.directory.slots resource with
  | .absent => none
  | .present cell => some cell

def packageAtom (domain : Digest) (resource app : Nat)
    (cell : PackedCell CanonicalCellRegistry.registry) : Option (Option AtomRecord) := do
  match cell with
  | ⟨.content, payload⟩ =>
      match Hyperdocument.lookup payload.logical .atoms
          (ApplicationDispatchManifest.manifestAtom domain app) with
      | none => some none
      | some record =>
          if record.document != ⟨⟨resource⟩⟩ then none else some (some record)
  | _ => none

/-- An installed version is read from the actual current content cell, not
the report's duplicate manifest bytes. Installation and upgrade instead bind
that report to the prospective output of the same joint transaction. -/
def packageMatches (deployment : CanonicalCellRegistry.Deployment)
    (source : ApplicationFailedStartRecoverySource.Source)
    (cell : PackedCell CanonicalCellRegistry.registry) : Bool :=
  if source.needsPackageWrite then true
  else
    match cell with
    | ⟨.content, payload⟩ =>
            ApplicationDispatchManifest.decodeInstalled deployment.domain
              source.originalBegin.base.source.packageManifest source.app
              source.claimedState.packageVersion payload.logical ==
                some (ApplicationLifecycleBeginV3Ingress.prospectiveManifest
                  source.originalBegin)
    | _ => false

/-- A successful first-create report may install the created-volume marker
only after the one-shot claim consumed its attempt marker. A duplicate report
cannot install the marker again. The historical completion certificate needed
for later continue is checked separately by Verified. -/
def creationMarkersCurrent (config : Config) (opened : Opened config)
    (ingress : ApplicationFailedStartRecoveryIngress.Ingress) : Bool :=
  match ingress.creationMarker with
  | none => true
  | some created =>
      match ingress.source.originalBegin.start with
      | none => false
      | some binding =>
          opened.durable.snapshot.model.consumed
              (ApplicationLifecycleClaimV3Ingress.firstAttemptNullifier
                ingress.domain binding) &&
            !opened.durable.snapshot.model.consumed created

def linkedCurrentPolicies {F : Type} [Field F]
    (deployment : CanonicalCellRegistry.Deployment)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : DeclaredResourceController.Ambient)
    (durable : DeclaredResourceController.Durable)
    (source : ApplicationFailedStartRecoverySource.Source)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile
      ambient durable (source.command deployment.domain profile.semantics)) : Bool :=
  let auth := prepared.authority.snapshot.logical
  let directory := prepared.directory.directory
  let load := fun id => do
    let head ← CredentialAuthorityDomain.headAt auth ⟨id⟩
    let policy ← CanonicalCellRegistry.loadPolicySource deployment.domain directory head.address
    if policy.record.policyId == ⟨id⟩ && policy.record.version == head.version &&
        policy.record.semantics == profile.semantics then
      some policy.record.predicate
    else none
  let begin := source.originalBegin.base.source
  let management := Minidregg.Pred.Pred.eq "request/subject" begin.managementSubject.value
  (load begin.app == some (ApplicationGrain.policy begin.packageManifest
      begin.snapshotManifest management) &&
    load begin.packageManifest == some
      (ApplicationGrain.packageManifestPolicy begin.app management)) ||
  ApplicationGrain.managedPoliciesMatch begin.app begin.packageManifest
    begin.snapshotManifest begin.managementSubject.value
    (load begin.app) (load begin.packageManifest)

private def requirePresent {α : Type} (value : Option α) (detail : String) :
    Except String { selected : α // value = some selected } :=
  match value with
  | none => .error detail
  | some selected => .ok ⟨selected, rfl⟩

def packageRequest (config : Config) (opened : Opened config)
    (source : ApplicationFailedStartRecoverySource.Source)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment
      config.profile ⟨config.federation, logicalHeight config opened.durable⟩
      opened.durable (source.command config.deployment.domain config.profile.semantics)) :
    Request .object :=
  let target : DeclaredResourceController.Target :=
    ⟨.object, source.originalBegin.base.source.packageManifest,
      source.packageObserveCapability, ContentResource.commandVersion,
      source.currentPackageRoot, .content ⟨[]⟩, none, none, none⟩
  { DeclaredResourceController.requestFor prepared.authority.snapshot
      config.profile.semantics ⟨config.federation, logicalHeight config opened.durable⟩
      (source.command config.deployment.domain config.profile.semantics)
      target source.currentPackageRoot with
    verb := .observeObject }

/-- A separately signed package read is required for every completion.
Install/upgrade also have DRC's joint-target observation; start/stop use this
read to pin the foreign package cell and add its physical CAS guard. -/
structure PackageRead (config : Config) (opened : Opened config)
    (source : ApplicationFailedStartRecoverySource.Source)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment
      config.profile ⟨config.federation, logicalHeight config opened.durable⟩
      opened.durable (source.command config.deployment.domain config.profile.semantics))
    (cell : PackedCell CanonicalCellRegistry.registry) (envelope : List UInt8) where
  private mk ::
  selected : ResourceObservationAdmission.Prepared
    (DeclaredResourceController.readContext prepared) config.profile
    (packageRequest config opened source prepared)
    (DeclaredResourceController.operationMarker config.deployment.domain
      config.profile.semantics
      (source.command config.deployment.domain config.profile.semantics))
    source.packageObserveCapability source.canonicalBytes
  checked : ResourceObservationAdmission.Checked selected envelope
  observedExact : selected.observed.before = cell
  physicalCurrent :
    (ApplicationLifecycleClaimCurrent.observationGuard
      source.originalBegin.base.source.packageManifest cell).expectedRoot =
      opened.durable.snapshot.model.roots
        (ApplicationLifecycleClaimCurrent.observationGuard
          source.originalBegin.base.source.packageManifest cell).cellId

def checkPackage (config : Config) (opened : Opened config)
    (source : ApplicationFailedStartRecoverySource.Source)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment
      config.profile ⟨config.federation, logicalHeight config opened.durable⟩
      opened.durable (source.command config.deployment.domain config.profile.semantics))
    (cell : PackedCell CanonicalCellRegistry.registry) (envelope : List UInt8) :
    IO (Except String (PackageRead config opened source prepared cell envelope)) := do
  let context := DeclaredResourceController.readContext prepared
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics
    (source.command config.deployment.domain config.profile.semantics)
  let wanted := packageRequest config opened source prepared
  match ResourceObservationAdmission.prepare context config.profile wanted marker
      source.packageObserveCapability source.canonicalBytes with
  | .error _ => return .error "current package observation refused"
  | .ok selected =>
      match ← ResourceObservationAdmission.check config.signature selected envelope with
      | .error _ => return .error "signed package observation refused"
      | .ok checked =>
          if observedBytes : CanonicalCellRegistry.cellCodec.encode
              selected.observed.before = CanonicalCellRegistry.cellCodec.encode cell then
            have observedExact : selected.observed.before = cell :=
              (lawful_encode_injective CanonicalCellRegistry.cellCodec) observedBytes
            have physicalCurrent := PhysicalResourceReadGuard.current
              context.directory source.originalBegin.base.source.packageManifest
              selected.observed.before selected.observed.present
            return .ok ⟨selected, checked, observedExact,
              by simpa only [observedExact] using physicalCurrent⟩
          else return .error "signed package observation differs from current old image"

/-- This conditional candidate is not constructed from a valid report alone. It also
re-admits the exact claim at a structural prefix of the same Store, uses the custodian key
pinned into today's NativeHost profile, checks current app/package content,
and admits the source-derived management command under current signatures.
Only Replay may bind its structural historical prefix to an admitted walk. -/
structure Candidate (config : Config) (opened : Opened config)
    (ingress : ApplicationFailedStartRecoveryIngress.Ingress) where
  private mk ::
  profileExact : ingress.domain = config.deployment.domain ∧
    ingress.semantics = config.profile.semantics
  sourceValid : ingress.source.valid = true
  key : List UInt8
  keyPinned : config.completionCustodianKey = some key
  physical : ApplicationFailedStartRecoveryReport.Checked
    config.deployment.domain config.profile.semantics key
    ingress.source.originalBegin
  historical : ApplicationFailedStartRecoveryHistory.Candidate config
    opened ingress.source
  prepared : DeclaredResourceController.PreparedInvocation
    config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩
    opened.durable
    (ingress.source.command config.deployment.domain config.profile.semantics)
  linked : linkedCurrentPolicies config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩
    opened.durable ingress.source prepared = true
  shape : DeclaredResourceController.PhysicalShape prepared
  appCell : PackedCell CanonicalCellRegistry.registry
  appCurrent : currentCell prepared ingress.source.app = some appCell
  appExact : appState ingress.source.app appCell = some ingress.source.claimedState
  packageCell : PackedCell CanonicalCellRegistry.registry
  packageCurrent : currentCell prepared
    ingress.source.originalBegin.base.source.packageManifest = some packageCell
  packageAtomExact : packageAtom config.deployment.domain
    ingress.source.originalBegin.base.source.packageManifest
    ingress.source.app packageCell = some ingress.source.packageAtomBefore
  installed : packageMatches config.deployment ingress.source packageCell = true
  creationMarkers : creationMarkersCurrent config opened ingress = true
  packageRead : PackageRead config opened ingress.source prepared packageCell
    ingress.packageObservationEnvelope
  packageGuardReadOnly : ingress.source.needsPackageWrite = false →
    (ApplicationLifecycleClaimCurrent.observationGuard
      ingress.source.originalBegin.base.source.packageManifest packageCell).cellId ∉
      (DeclaredResourceController.writes prepared).map DataWrite.cellId
  invocation : ApplicationFailedStartRecoveryPolicy.Accepted prepared
    ingress.signed physical

def prepareConditional (config : Config) (opened : Opened config)
    (ingress : ApplicationFailedStartRecoveryIngress.Ingress) :
    IO (Except String (Candidate config opened ingress)) := do
  if profileExact : ingress.domain = config.deployment.domain ∧
      ingress.semantics = config.profile.semantics then
    if sourceValid : ingress.source.valid = true then
      let keySelected ← match requirePresent config.completionCustodianKey
          "physical custodian key unavailable" with
        | .error detail => return .error detail
        | .ok selected => pure selected
      let key := keySelected.val
      have keyPinned : config.completionCustodianKey = some key := keySelected.property
      let physical ← match ← ApplicationFailedStartRecoveryReport.check config.signature
          config.deployment.domain config.profile.semantics key
          ingress.source.originalBegin ingress.source.physical with
        | .error detail => return .error detail
        | .ok checked => pure checked
      let historical ← match ← ApplicationFailedStartRecoveryHistory.select config
          opened ingress.source with
        | .error detail => return .error detail
        | .ok selected => pure selected
      let ambient : DeclaredResourceController.Ambient :=
        ⟨config.federation, logicalHeight config opened.durable⟩
      let command := ingress.source.command config.deployment.domain config.profile.semantics
      let prepared ← match DeclaredResourceController.prepare config.deployment
          config.profile ambient opened.durable command with
        | .error _ => return .error "failed START recovery current transaction preparation refused"
        | .ok selected => pure selected
      if linked : linkedCurrentPolicies config.deployment config.profile ambient
          opened.durable ingress.source prepared = true then
        if shape : DeclaredResourceController.PhysicalShape prepared then
          let appSelected ← match requirePresent
              (currentCell prepared ingress.source.app) "current claimed app cell absent" with
            | .error detail => return .error detail
            | .ok selected => pure selected
          let appCell := appSelected.val
          have appCurrent : currentCell prepared ingress.source.app = some appCell :=
            appSelected.property
          if appExact : appState ingress.source.app appCell =
              some ingress.source.claimedState then
            let resource := ingress.source.originalBegin.base.source.packageManifest
            let packageSelected ← match requirePresent (currentCell prepared resource)
                "current package cell absent" with
              | .error detail => return .error detail
              | .ok selected => pure selected
            let packageCell := packageSelected.val
            have packageCurrent : currentCell prepared resource = some packageCell :=
              packageSelected.property
            if packageAtomExact : packageAtom config.deployment.domain resource
                ingress.source.app packageCell = some ingress.source.packageAtomBefore then
              if installed : packageMatches config.deployment ingress.source packageCell = true then
                if markers : creationMarkersCurrent config opened ingress = true then
                  let packageRead ← match ← checkPackage config opened ingress.source
                      prepared packageCell ingress.packageObservationEnvelope with
                    | .error detail => return .error detail
                    | .ok selected => pure selected
                  if packageGuardReadOnly : ingress.source.needsPackageWrite = false →
                      (ApplicationLifecycleClaimCurrent.observationGuard resource packageCell).cellId ∉
                        (DeclaredResourceController.writes prepared).map DataWrite.cellId then
                    match ← ApplicationFailedStartRecoveryPolicy.admit config.signature
                        prepared ingress.signed physical with
                    | .error reason => return .error s!"failed START recovery current signed policy admission refused: {repr reason}"
                    | .ok invocation =>
                        return .ok ⟨profileExact, sourceValid, key, keyPinned,
                          physical, historical, prepared, linked, shape,
                          appCell, appCurrent, appExact, packageCell, packageCurrent,
                          packageAtomExact, installed, markers, packageRead,
                          packageGuardReadOnly, invocation⟩
                  else return .error "failed START recovery package read/write overlap refused"
                else return .error "failed START recovery creation marker state refused"
              else return .error "current installed package differs from descriptor"
            else return .error "current package atom differs from signed failed START recovery source"
          else return .error "current application is no longer claimed at original generation"
        else return .error "failed START recovery union physical transaction refused"
      else return .error "current lifecycle management/package law differs"
    else return .error "failed START recovery source identities refused"
  else return .error "failed START recovery deployment profile differs"

end Minidregg.Kernel.ApplicationFailedStartRecoveryAdmission
