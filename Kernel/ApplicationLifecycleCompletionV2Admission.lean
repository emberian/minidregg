/-
Fresh checked lifecycle completion admission against one current durable image.
This joins the verified original v3 claim, the separately pinned physical
custodian, current installed law and capabilities, and exact current app and
package content. It produces no CAS or host permit by itself.
-/
import Kernel.ApplicationLifecycleCompletionV2History
import Kernel.ApplicationLifecycleCompletionV2Ingress
import Kernel.ApplicationLifecycleCompletionV2Policy
import Kernel.ApplicationLifecycleClaimCurrent
import Kernel.PhysicalResourceReadGuard
import Kernel.ResourceObservationAdmission

namespace Minidregg.Kernel.ApplicationLifecycleCompletionV2Admission

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

open Minidregg.Compiler.ServedBasis (Ground)
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (Reader)

def appState (app : Nat) (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationGrain.State :=
  ApplicationLifecycleClaimCurrent.appState app cell

def currentCell {F : Type} [Field F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile
      ambient ground command) (resource : Nat) :
    Option (PackedCell CanonicalCellRegistry.registry) :=
  match ground.directory.slots resource with
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
    (source : ApplicationLifecycleCompletionV2Source.Source)
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
for later continue is checked separately by Verified. A marker the ground
did not declare refuses (`creationMarkersDeclared`). -/
/- The nullifiers the creation-marker check reads from the spent map. -/
def creationNullifiers (ingress : ApplicationLifecycleCompletionV2Ingress.Ingress) : List StableNullifier :=
  match ingress.creationMarker with
  | none => []
  | some created =>
      match ingress.source.originalBegin.start with
      | none => []
      | some binding =>
          [ApplicationLifecycleClaimV3Ingress.firstAttemptNullifier ingress.domain binding, created]

/-- Every key the current part of this admission reads: the DRC invocation's
transaction id and operation marker, and the creation markers. -/
def keys (config : Config) (ingress : ApplicationLifecycleCompletionV2Ingress.Ingress) : DurableView.Keys :=
  let base := DeclaredResourceController.invocationKeys config.deployment.domain
    config.profile.semantics (ingress.source.command config.deployment.domain config.profile.semantics)
  ⟨base.transactions, base.nullifiers ++ creationNullifiers ingress⟩

/-- The ground answers every marker read (an undeclared marker is never read as
unconsumed). -/
def creationMarkersDeclared {deployment : CanonicalCellRegistry.Deployment}
    (ground : Ground deployment) (ingress : ApplicationLifecycleCompletionV2Ingress.Ingress) : Bool :=
  (creationNullifiers ingress).all ground.declaresNullifier

def creationMarkersCurrent (config : Config) (ground : Ground config.deployment)
    (ingress : ApplicationLifecycleCompletionV2Ingress.Ingress) : Bool :=
  creationMarkersDeclared ground ingress &&
  match ingress.creationMarker with
  | none => true
  | some created =>
      match ingress.source.originalBegin.start with
      | none => false
      | some binding =>
          ground.view.model.consumed
              (ApplicationLifecycleClaimV3Ingress.firstAttemptNullifier
                ingress.domain binding) &&
            !ground.view.model.consumed created

def linkedCurrentPolicies {F : Type} [Field F]
    (deployment : CanonicalCellRegistry.Deployment)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : DeclaredResourceController.Ambient)
    (ground : Ground deployment)
    (source : ApplicationLifecycleCompletionV2Source.Source)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile
      ambient ground (source.command deployment.domain profile.semantics)) : Bool :=
  let auth := ground.authority.logical
  let directory := ground.directory
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

def packageRequest (config : Config) (ground : Ground config.deployment)
    (source : ApplicationLifecycleCompletionV2Source.Source)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment
      config.profile ⟨config.federation, config.genesisHeight + ground.height⟩
      ground (source.command config.deployment.domain config.profile.semantics)) :
    Request .object :=
  let target : DeclaredResourceController.Target :=
    ⟨.object, source.originalBegin.base.source.packageManifest,
      source.packageObserveCapability, ContentResource.commandVersion,
      source.currentPackageRoot, .content ⟨[]⟩, none, none, none⟩
  { DeclaredResourceController.requestFor ground.authority
      config.profile.semantics ⟨config.federation, config.genesisHeight + ground.height⟩
      (source.command config.deployment.domain config.profile.semantics)
      target source.currentPackageRoot with
    verb := .observeObject }

/-- A separately signed package read is required for every completion.
Install/upgrade also have DRC's joint-target observation; start/stop use this
read to pin the foreign package cell and add its physical CAS guard. -/
structure PackageRead (config : Config) (ground : Ground config.deployment)
    (source : ApplicationLifecycleCompletionV2Source.Source)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment
      config.profile ⟨config.federation, config.genesisHeight + ground.height⟩
      ground (source.command config.deployment.domain config.profile.semantics))
    (cell : PackedCell CanonicalCellRegistry.registry) (envelope : List UInt8) where
  private mk ::
  selected : ResourceObservationAdmission.Prepared
    (DeclaredResourceController.readContext prepared) config.profile
    (packageRequest config ground source prepared)
    (DeclaredResourceController.operationMarker config.deployment.domain
      config.profile.semantics
      (source.command config.deployment.domain config.profile.semantics))
    source.packageObserveCapability source.canonicalBytes
  checked : ResourceObservationAdmission.Checked selected envelope
  observedExact : selected.observed.before = cell
  physicalCurrent :
    (ApplicationLifecycleClaimCurrent.observationGuard
      source.originalBegin.base.source.packageManifest cell).expectedRoot =
      ground.view.model.roots
        (ApplicationLifecycleClaimCurrent.observationGuard
          source.originalBegin.base.source.packageManifest cell).cellId

def checkPackage (config : Config) (ground : Ground config.deployment)
    (source : ApplicationLifecycleCompletionV2Source.Source)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment
      config.profile ⟨config.federation, config.genesisHeight + ground.height⟩
      ground (source.command config.deployment.domain config.profile.semantics))
    (cell : PackedCell CanonicalCellRegistry.registry) (envelope : List UInt8) :
    IO (Except String (PackageRead config ground source prepared cell envelope)) := do
  let context := DeclaredResourceController.readContext prepared
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics
    (source.command config.deployment.domain config.profile.semantics)
  let wanted := packageRequest config ground source prepared
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
            have physicalCurrent := Ground.physicalCurrent context source.originalBegin.base.source.packageManifest
              selected.observed.before selected.observed.present
            return .ok ⟨selected, checked, observedExact,
              by simpa only [observedExact] using physicalCurrent⟩
          else return .error "signed package observation differs from current old image"

/-- This conditional candidate is not constructed from a valid report alone. It also
re-admits the exact claim at a structural prefix of the same Store, uses the custodian key
pinned into today's NativeHost profile, checks current app/package content,
and admits the source-derived management command under current signatures.
Only Replay may bind its structural historical prefix to an admitted walk. -/
structure Candidate (config : Config) {store : StoreIdentity} (head : Head store)
    (ground : Ground config.deployment)
    (ingress : ApplicationLifecycleCompletionV2Ingress.Ingress) where
  private mk ::
  profileExact : ingress.domain = config.deployment.domain ∧
    ingress.semantics = config.profile.semantics
  sourceValid : ingress.source.valid = true
  key : List UInt8
  keyPinned : config.completionCustodianKey = some key
  physical : ApplicationLifecycleCompletionV2Report.Checked
    config.deployment.domain config.profile.semantics key
    ingress.source.originalBegin
  historical : ApplicationLifecycleCompletionV2History.Candidate config head ingress.source
  prepared : DeclaredResourceController.PreparedInvocation
    config.deployment config.profile
    ⟨config.federation, config.genesisHeight + ground.height⟩
    ground
    (ingress.source.command config.deployment.domain config.profile.semantics)
  linked : linkedCurrentPolicies config.deployment config.profile
    ⟨config.federation, config.genesisHeight + ground.height⟩
    ground ingress.source prepared = true
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
  creationMarkers : creationMarkersCurrent config ground ingress = true
  packageRead : PackageRead config ground ingress.source prepared packageCell
    ingress.packageObservationEnvelope
  packageGuardReadOnly : ingress.source.needsPackageWrite = false →
    (ApplicationLifecycleClaimCurrent.observationGuard
      ingress.source.originalBegin.base.source.packageManifest packageCell).cellId ∉
      (DeclaredResourceController.writes prepared).map DataWrite.cellId
  invocation : ApplicationLifecycleCompletionV2Policy.Accepted prepared
    ingress.signed physical

def prepareConditional (config : Config) {store : StoreIdentity}
    (reader : Reader ResourceBirthCodec.rootBytes store) (ground : Ground config.deployment)
    (ingress : ApplicationLifecycleCompletionV2Ingress.Ingress) :
    IO (Except String (Candidate config reader.head ground ingress)) := do
  if profileExact : ingress.domain = config.deployment.domain ∧
      ingress.semantics = config.profile.semantics then
    if sourceValid : ingress.source.valid = true then
      let keySelected ← match requirePresent config.completionCustodianKey
          "physical custodian key unavailable" with
        | .error detail => return .error detail
        | .ok selected => pure selected
      let key := keySelected.val
      have keyPinned : config.completionCustodianKey = some key := keySelected.property
      let physical ← match ← ApplicationLifecycleCompletionV2Report.check config.signature
          config.deployment.domain config.profile.semantics key
          ingress.source.originalBegin ingress.source.physical with
        | .error detail => return .error detail
        | .ok checked => pure checked
      let historical ← match ← ApplicationLifecycleCompletionV2History.select config reader ground.height ingress.source with
        | .error detail => return .error detail
        | .ok selected => pure selected
      let ambient : DeclaredResourceController.Ambient :=
        ⟨config.federation, config.genesisHeight + ground.height⟩
      let command := ingress.source.command config.deployment.domain config.profile.semantics
      let prepared ← match DeclaredResourceController.prepare config.deployment
          config.profile ambient ground command with
        | .error _ => return .error "completion current transaction preparation refused"
        | .ok selected => pure selected
      if linked : linkedCurrentPolicies config.deployment config.profile ambient
          ground ingress.source prepared = true then
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
                if markers : creationMarkersCurrent config ground ingress = true then
                  let packageRead ← match ← checkPackage config ground ingress.source
                      prepared packageCell ingress.packageObservationEnvelope with
                    | .error detail => return .error detail
                    | .ok selected => pure selected
                  if packageGuardReadOnly : ingress.source.needsPackageWrite = false →
                      (ApplicationLifecycleClaimCurrent.observationGuard resource packageCell).cellId ∉
                        (DeclaredResourceController.writes prepared).map DataWrite.cellId then
                    match ← ApplicationLifecycleCompletionV2Policy.admit config.signature
                        prepared ingress.signed physical with
                    | .error reason => return .error s!"completion current signed policy admission refused: {repr reason}"
                    | .ok invocation =>
                        return .ok ⟨profileExact, sourceValid, key, keyPinned,
                          physical, historical, prepared, linked, shape,
                          appCell, appCurrent, appExact, packageCell, packageCurrent,
                          packageAtomExact, installed, markers, packageRead,
                          packageGuardReadOnly, invocation⟩
                  else return .error "completion package read/write overlap refused"
                else return .error "completion creation marker state refused"
              else return .error "current installed package differs from descriptor"
            else return .error "current package atom differs from signed completion source"
          else return .error "current application is no longer claimed at original generation"
        else return .error "completion union physical transaction refused"
      else return .error "current lifecycle management/package law differs"
    else return .error "completion source identities refused"
  else return .error "completion deployment profile differs"

end Minidregg.Kernel.ApplicationLifecycleCompletionV2Admission
