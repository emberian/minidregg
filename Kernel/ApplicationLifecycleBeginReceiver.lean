/-
Special native admission for an application lifecycle BEGIN. This module
records a Mini-owned pending request only after ordinary current DRC mutation
admission and a separately authorized, same-image package observation. It
does not launch, attest, complete, or reconcile a physical process.
-/
import Kernel.ApplicationLifecycleBeginIngress
import Kernel.PhysicalResourceReadGuard
import Kernel.ApplicationDispatchManifest
import Kernel.ResourceObservationAdmission

namespace Minidregg.Kernel.ApplicationLifecycleBeginReceiver

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ApplicationLifecycleBegin
open Minidregg.Kernel.ApplicationLifecycleBeginIngress

set_option autoImplicit false

abbrev Durable := DeclaredResourceController.Durable
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Ambient := DeclaredResourceController.Ambient

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (ingress : Ingress) : Receipt :=
  ⟨ingress.transactionId, (event ingress).eventId⟩

/-- An ordinary signed invocation cannot be mistaken for the special pending
event even if it carries byte-identical app state writes. -/
theorem ordinary_event_ne (ingress : Ingress)
    (command : DeclaredResourceController.Command)
    (signed : DeclaredResourceController.SignedCommand) :
    event ingress ≠ DeclaredResourceController.invocationEvent ingress.domain
      ingress.semantics command signed := by
  intro equal
  have versions := congrArg StableEvent.codecVersion equal
  norm_num [event, DeclaredResourceController.invocationEvent] at versions

/-- A historical pending record must retain this exact special event and both
nullifiers under the source-derived operation marker. -/
private def exactRecorded (ingress : Ingress)
    (recorded : Intent TransactionId CellId StableNullifier ReplayEnvelope) : Prop :=
  recorded.transactionId = ingress.transactionId ∧
    recorded.event.event = event ingress ∧
    recorded.nullifiers =
      [CredentialAuthorityReplay.nullifier ingress.domain
        (DeclaredResourceController.operationMarker ingress.domain ingress.semantics
          (command ingress.domain ingress.semantics ingress.source)),
        stableNullifier ingress.domain ingress.semantics ingress.source]

private instance (ingress : Ingress)
    (recorded : Intent TransactionId CellId StableNullifier ReplayEnvelope) :
    Decidable (exactRecorded ingress recorded) := by
  unfold exactRecorded
  infer_instance

/-- An ordinary DRC event under the same marker is a conflict. Historical
replay does not ask today's policy or host pin to approve yesterday's event. -/
def replay (durable : Durable) (ingress : Ingress) : Option (Except String Receipt) :=
  match Snapshot.lookupRecorded ingress.transactionId durable.snapshot.model.journal with
  | none => none
  | some recorded =>
      if exactRecorded ingress recorded then
        some (.ok (receipt ingress))
      else some (.error "lifecycle begin transaction identity conflict")

theorem replay_only_exact (durable : Durable) (ingress : Ingress) (result : Receipt)
    (accepted : replay durable ingress = some (.ok result)) :
    result = receipt ingress ∧
      ∃ recorded,
        Snapshot.lookupRecorded ingress.transactionId durable.snapshot.model.journal =
          some recorded ∧ recorded.transactionId = ingress.transactionId ∧
          recorded.event.event = event ingress ∧
        recorded.nullifiers =
          [CredentialAuthorityReplay.nullifier ingress.domain
            (DeclaredResourceController.operationMarker ingress.domain ingress.semantics
              (command ingress.domain ingress.semantics ingress.source)),
            stableNullifier ingress.domain ingress.semantics ingress.source] := by
  unfold replay at accepted
  split at accepted
  · cases accepted
  · rename_i recorded found
    split at accepted
    · rename_i exact
      have equal : receipt ingress = result := by simpa using accepted
      exact ⟨equal.symm, recorded, found, (show exactRecorded ingress recorded from exact)⟩
    · cases accepted

/-- Exact source restriction for the first implementation. A future source-
authored provenance relation may admit equivalent policy revisions without
allowing a caller to nominate an unrelated content cell as the package. -/
def appPolicyMatches (packageTarget snapshotTarget : Nat)
    (management : Minidregg.Pred.Pred)
    (installed : Option Minidregg.Pred.Pred) : Bool :=
  installed == some (ApplicationGrain.policyV1 packageTarget snapshotTarget management) ||
  installed == some (ApplicationGrain.policy packageTarget snapshotTarget management)

theorem appPolicyMatches_v1 (packageTarget snapshotTarget : Nat)
    (management : Minidregg.Pred.Pred) :
    appPolicyMatches packageTarget snapshotTarget management
      (some (ApplicationGrain.policyV1 packageTarget snapshotTarget management)) = true := by
  simp [appPolicyMatches]

theorem appPolicyMatches_current (packageTarget snapshotTarget : Nat)
    (management : Minidregg.Pred.Pred) :
    appPolicyMatches packageTarget snapshotTarget management
      (some (ApplicationGrain.policy packageTarget snapshotTarget management)) = true := by
  simp [appPolicyMatches]

def linkedCurrentPolicy {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (source : Source)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command deployment.domain profile.semantics source)) : Bool :=
  let auth := prepared.authority.snapshot.logical
  let directory := prepared.directory.directory
  let appPolicy := do
    let head ← CredentialAuthorityDomain.headAt auth ⟨source.app⟩
    let policy ← CanonicalCellRegistry.loadPolicySource deployment.domain directory head.address
    if policy.record.policyId == ⟨source.app⟩ &&
        policy.record.version == head.version &&
        policy.record.semantics == profile.semantics then
      pure policy.record.predicate
    else none
  let packagePolicy := do
    let head ← CredentialAuthorityDomain.headAt auth ⟨source.packageManifest⟩
    let policy ← CanonicalCellRegistry.loadPolicySource deployment.domain directory head.address
    if policy.record.policyId == ⟨source.packageManifest⟩ &&
        policy.record.version == head.version &&
        policy.record.semantics == profile.semantics then
      pure policy.record.predicate
    else none
  let management := Minidregg.Pred.Pred.eq "request/subject" source.managementSubject.value
  appPolicyMatches source.packageManifest source.snapshotManifest management appPolicy &&
  packagePolicy == some (ApplicationGrain.packageManifestPolicy source.app
    management)

/-- The package observation uses the same signed command identity and current
policy epoch/revision as the mutation. It is not satisfied by the app's
mutation capability alone. -/
def packageRequest {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (source : Source)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command deployment.domain profile.semantics source)) :=
  let target : DeclaredResourceController.Target :=
    ⟨.object, source.packageManifest, source.packageObserveCapability, 1,
      source.packageRoot, .content ⟨[]⟩, none⟩
  { DeclaredResourceController.requestFor prepared.authority.snapshot profile.semantics
      ambient (command deployment.domain profile.semantics source) target source.packageRoot with
    verb := .observeObject }

/-- The signed package root selects the logical content state. Durable CAS
guards the enclosing physical cell, whose root includes its materialization. -/
def packageGuard (source : Source)
    (before : PackedCell CanonicalCellRegistry.registry) : ReadGuard :=
  ⟨⟨source.packageManifest⟩, ResourceBirthCodec.physicalRoot (.live before)⟩

/-- Derive the durable payload from the checked DRC invocation. The old app
write, authority write, and all source guards remain exactly those admitted
by DRC; the extra package guard is checked against this same old image.
The new event and second nullifier distinguish an executable pending request
from a generic begin mutation. The source charge replaces ordinary turn bytes
with this full ingress, adds one authorized package-observation incidence and
proof unit, and counts the one extra read guard. Ordinary DRC `storageBytes`
counts only post-write bytes; this special source tariff additionally counts
the ingress and new nullifier bytes. Neither ordinary nor special charge is a
claim to measure every physical journal byte. No external physical effect is
charged, because none has occurred. -/
def intent {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable}
    {source : Source} {ingress : Ingress}
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command deployment.domain profile.semantics source))
    (shape : DeclaredResourceController.PhysicalShape prepared)
    (accepted : DeclaredResourceController.AcceptedInvocation prepared ingress.signed)
    (packageBefore : PackedCell CanonicalCellRegistry.registry)
    (_sourceExact : ingress.domain = deployment.domain ∧
      ingress.semantics = profile.semantics ∧ ingress.source = source)
    (_guardCurrent : (packageGuard source packageBefore).expectedRoot =
      durable.snapshot.model.roots (packageGuard source packageBefore).cellId)
    (guardReadOnly : (packageGuard source packageBefore).cellId ∉
      (DeclaredResourceController.writes prepared).map DataWrite.cellId) :
    DataIntent rootBytes := by
  let ordinary := accepted.dataIntent shape
  have guarded : ∀ guard ∈ ordinary.readGuards ++ [packageGuard source packageBefore],
      guard.cellId ∉ ordinary.writes.map DataWrite.cellId := by
    intro guard member
    rcases List.mem_append.mp member with old | extra
    · exact ordinary.guardsReadOnly guard old
    · simp only [List.mem_singleton] at extra
      subst guard
      exact guardReadOnly
  exact
    { transactionId := ordinary.transactionId
      writes := ordinary.writes
      readGuards := ordinary.readGuards ++ [packageGuard source packageBefore]
      nullifiers := ordinary.nullifiers ++
        [stableNullifier deployment.domain profile.semantics source]
      exactCharge := fun dimension => match dimension with
        | .incidences => ordinary.exactCharge .incidences + 1
        | .turnBytes => ingress.canonicalBytes.length
        | .witnessBytes => ingress.canonicalBytes.length
        | .proofWork => ordinary.exactCharge .proofWork + 1
        | .memoryTouches => ordinary.exactCharge .memoryTouches + 1
        | .storageBytes => ordinary.exactCharge .storageBytes +
            ingress.canonicalBytes.length +
            (stableNullifier deployment.domain profile.semantics source).canonicalBytes.length
        | other => ordinary.exactCharge other
      event := event ingress
      postRootsBound := ordinary.postRootsBound
      guardsReadOnly := guarded }

inductive Result where
  | historical (receipt : Receipt)
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)
  deriving Repr

/-- Only start and stop depend on an already installed package descriptor.
Install/upgrade bind a proposed SPK digest now; a later checked completion
must write the corresponding installed manifest in the same app transaction. -/
def installedPackageMatches (deployment : Deployment) (source : Source)
    (cell : PackedCell CanonicalCellRegistry.registry) : Bool :=
  if source.kind == .start || source.kind == .stop then
    match cell with
    | ⟨.content, payload⟩ =>
        match HyperdocumentContentPageMaterializer.pageAt payload.logical with
        | none => false
        | some page =>
            match ApplicationDispatchManifest.decodeInstalled deployment.domain
                source.packageManifest source.app source.before.packageVersion page with
            | none => false
            | some manifest => manifest.packageRoot == source.packageDigest
    | _ => false
  else true

/-- Exact replay is checked before today's policy/profile, while fresh
admission checks both current policy links and current native signatures.
No operator-supplied Boolean is interpreted as physical completion. -/
structure Accepted {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (ingress : Ingress) where
  profileExact : ingress.domain = deployment.domain ∧ ingress.semantics = profile.semantics
  sourceValid : ingress.source.valid = true
  prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
    (command deployment.domain profile.semantics ingress.source)
  linked : linkedCurrentPolicy deployment profile ambient durable ingress.source prepared = true
  shape : DeclaredResourceController.PhysicalShape prepared
  selected : ResourceObservationAdmission.Prepared
    (DeclaredResourceController.readContext prepared) profile
    (packageRequest deployment profile ambient durable ingress.source prepared)
    (DeclaredResourceController.operationMarker deployment.domain profile.semantics
      (command deployment.domain profile.semantics ingress.source))
    ingress.source.packageObserveCapability ingress.source.canonicalBytes
  content : selected.observed.before.kind = .content
  installed : installedPackageMatches deployment ingress.source selected.observed.before = true
  observed : ResourceObservationAdmission.Checked selected ingress.packageObservationEnvelope
  guardCurrent : (packageGuard ingress.source selected.observed.before).expectedRoot =
    durable.snapshot.model.roots
      (packageGuard ingress.source selected.observed.before).cellId
  guardReadOnly : (packageGuard ingress.source selected.observed.before).cellId ∉
    (DeclaredResourceController.writes prepared).map DataWrite.cellId
  invocation : DeclaredResourceController.AcceptedInvocation prepared ingress.signed

def Accepted.intent {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {ingress : Ingress}
    (accepted : Accepted deployment profile ambient durable ingress) : DataIntent rootBytes :=
  ApplicationLifecycleBeginReceiver.intent accepted.prepared accepted.shape accepted.invocation
    accepted.selected.observed.before
    ⟨accepted.profileExact.1, accepted.profileExact.2, rfl⟩
    accepted.guardCurrent accepted.guardReadOnly

/-- The executable pending event is the exact canonical ingress, not the
ordinary DRC event that would accompany the same admitted state transition. -/
theorem Accepted.intent_event {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {ingress : Ingress}
    (accepted : Accepted deployment profile ambient durable ingress) :
    accepted.intent.event = event ingress := rfl

/-- The special receiver retains every DRC-admitted write unchanged. -/
theorem Accepted.intent_writes {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {ingress : Ingress}
    (accepted : Accepted deployment profile ambient durable ingress) :
    accepted.intent.writes =
      (accepted.invocation.dataIntent accepted.shape).writes := rfl

/-- The additional package read is both present in the one submitted intent
and pinned to the same durable old image used for DRC admission. -/
theorem Accepted.intent_package_guard {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {ingress : Ingress}
    (accepted : Accepted deployment profile ambient durable ingress) :
    packageGuard ingress.source accepted.selected.observed.before ∈ accepted.intent.readGuards ∧
      (packageGuard ingress.source accepted.selected.observed.before).expectedRoot =
        durable.snapshot.model.roots
          (packageGuard ingress.source accepted.selected.observed.before).cellId := by
  constructor
  · change packageGuard ingress.source accepted.selected.observed.before ∈
      (accepted.invocation.dataIntent accepted.shape).readGuards ++
        [packageGuard ingress.source accepted.selected.observed.before]
    simp
  · exact accepted.guardCurrent

theorem stale_package_root_has_no_admission {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {ingress : Ingress}
    (stale : ∀ before : PackedCell CanonicalCellRegistry.registry,
      ingress.source.packageRoot = before.payload.root →
      (packageGuard ingress.source before).expectedRoot ≠
        durable.snapshot.model.roots
          (packageGuard ingress.source before).cellId) :
    ¬ Nonempty (Accepted deployment profile ambient durable ingress) := by
  rintro ⟨accepted⟩
  exact stale accepted.selected.observed.before
    accepted.selected.observed.rootExact accepted.guardCurrent

theorem package_write_overlap_has_no_admission {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {ingress : Ingress}
    (overlap : ∀ prepared : DeclaredResourceController.PreparedInvocation deployment
      profile ambient durable
      (command deployment.domain profile.semantics ingress.source),
      ⟨ingress.source.packageManifest⟩ ∈
        (DeclaredResourceController.writes prepared).map DataWrite.cellId) :
    ¬ Nonempty (Accepted deployment profile ambient durable ingress) := by
  rintro ⟨accepted⟩
  exact accepted.guardReadOnly (overlap accepted.prepared)

/-- A replay verifier can call this same admission without writing to the
Store. All selected policy heads, the package observation, the DRC invocation,
and their physical guards come from this one supplied loaded image. -/
def admitLoaded {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (durable : Durable) (ingress : Ingress) :
    IO (Except String (Accepted deployment profile ambient durable ingress)) := do
  let source := ingress.source
  if sourceValid : source.valid = true then
    if profileExact : ingress.domain = deployment.domain ∧ ingress.semantics = profile.semantics then
      let expected := command deployment.domain profile.semantics source
      unless ingress.signed.commandBytes == DeclaredResourceController.commandCodec.encode expected do
        return .error "signed lifecycle begin command differs from source"
      match DeclaredResourceController.prepare deployment profile ambient durable expected with
      | .error _ => return .error "lifecycle begin preparation refused"
      | .ok prepared =>
          if linked : linkedCurrentPolicy deployment profile ambient durable source prepared = true then
            if shape : DeclaredResourceController.PhysicalShape prepared then
              let marker := DeclaredResourceController.operationMarker deployment.domain
                profile.semantics expected
              let wanted := packageRequest deployment profile ambient durable source prepared
              let context := DeclaredResourceController.readContext prepared
              match ResourceObservationAdmission.prepare context profile wanted marker
                  source.packageObserveCapability source.canonicalBytes with
              | .error _ => return .error "current package observation refused"
              | .ok selected =>
                  if content : selected.observed.before.kind = .content then
                    if installed : installedPackageMatches deployment source selected.observed.before = true then
                      match ← ResourceObservationAdmission.check native selected
                          ingress.packageObservationEnvelope with
                      | .error _ => return .error "signed package observation refused"
                      | .ok observed =>
                          have guardCurrent :
                              (packageGuard source selected.observed.before).expectedRoot =
                                durable.snapshot.model.roots
                                  (packageGuard source selected.observed.before).cellId :=
                            PhysicalResourceReadGuard.current context.directory
                              source.packageManifest selected.observed.before
                              selected.observed.present
                          if guardReadOnly :
                              (packageGuard source selected.observed.before).cellId ∉
                                (DeclaredResourceController.writes prepared).map DataWrite.cellId then
                            match ← DeclaredResourceController.admit native prepared ingress.signed with
                            | .error _ => return .error "current lifecycle begin authority refused"
                            | .ok invocation =>
                                return .ok ⟨profileExact, sourceValid, prepared, linked, shape,
                                  selected, content, installed, observed, guardCurrent,
                                  guardReadOnly, invocation⟩
                          else return .error "package observation overlaps lifecycle writes"
                    else return .error "current installed package identity refused"
                  else return .error "package target is not content"
            else return .error "lifecycle begin physical write shape refused"
          else return .error "current app/package policy linkage refused"
    else return .error "lifecycle begin domain or semantics differs from current deployment"
  else return .error "invalid lifecycle begin source"

def receiveLoaded {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (bytes : List UInt8) : IO Result := do
  let some ingress := codec.decode bytes
    | return .rejected "noncanonical lifecycle begin ingress"
  match replay durable ingress with
  | some (.ok original) => return .historical original
  | some (.error detail) => return .rejected detail
  | none => pure ()
  match ← admitLoaded deployment profile ambient native durable ingress with
  | .error detail => return .rejected detail
  | .ok accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable accepted.intent with
      | .confirmed kind _ => return .confirmed kind (receipt ingress)
      | .rejected _ => return .rejected "durable lifecycle begin refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationLifecycleBeginReceiver
