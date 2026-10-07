/-
# Kernel.CapabilityDelegationController — actual source-authorized delegation

The parent is selected from the complete canonical authority snapshot. The
source computes the child edge, its complete historical request, the one
authority-cell post and the policy view before native authorization. Only capability-mode
authorization naming that exact parent can complete the semantic family.

This controller changes authority only. The recipient later invokes through
the ordinary declared-resource controller with their own current signature.
-/
import Kernel.DeclaredResourceController
import Theory.CredentialAuthorityEffects
import Compiler.ResourceTargetAdmission
import Compiler.ResourceAuthorityProjection
import Compiler.ServedBasis

namespace Minidregg.Kernel.CapabilityDelegationController

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.CredentialLineageAdmission
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Store (Store)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Ground := ServedBasis.Ground
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer

def declarationStream (kind : ResourceKind) : StreamCodec (DelegateDeclaration kind) :=
  StreamCodec.xmap
    (StreamCodec.product (capabilityStream kind)
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product (TypedAuthorizationRequestCodec.resourceIdStream kind) StreamCodec.nat)))
    (fun declaration => (declaration.child, declaration.parentId, declaration.target,
      declaration.operationNullifier))
    (fun (child, parentId, target, marker) => ⟨child, parentId, target, marker⟩)
    (by intro declaration; cases declaration; rfl)

def declarationCodec (kind : ResourceKind) : LawfulCodec (DelegateDeclaration kind) :=
  ResourceBirthCodec.strictCodec (declarationStream kind).toLawful

structure Command (kind : ResourceKind) where
  subject : SubjectId
  nonce : Nat
  expectedTargetRoot : Digest
  declaration : DelegateDeclaration kind

def commandStream (kind : ResourceKind) : StreamCodec (Command kind) :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product digestStream (declarationStream kind))))
    (fun command => (command.subject, command.nonce, command.expectedTargetRoot, command.declaration))
    (fun (subject, nonce, targetRoot, declaration) => ⟨subject, nonce, targetRoot, declaration⟩)
    (by intro command; cases command; rfl)

abbrev PackedCommand := Sigma Command

def packedCommandStream : StreamCodec PackedCommand where
  encode command := ResourceBirthCodec.resourceKindStream.encode command.1 ++
    (commandStream command.1).encode command.2
  decodePrefix bytes := do
    let (kind, remainder) ← ResourceBirthCodec.resourceKindStream.decodePrefix bytes
    let (command, suffix) ← (commandStream kind).decodePrefix remainder
    pure (⟨kind, command⟩, suffix)
  decodePrefix_encode := by
    intro command suffix
    cases command with
    | mk kind command =>
      simp [List.append_assoc, StreamCodec.decodePrefix_encode]

def commandFrameName : List UInt8 := "DREGG/CAPABILITY/DELEGATE".toUTF8.toList

/-- Version 2: the declaration no longer carries the authority-cell root
(`expectedPreRoot`). Version 1 commands signed that whole root; they refuse by
name (`retiredCommand`). -/
def commandFrame : List UInt8 := commandFrameName ++ [2]

def rawCommandCodec : LawfulCodec PackedCommand where
  encode command := commandFrame ++ packedCommandStream.encode command
  decode bytes := if bytes.take commandFrame.length = commandFrame then
    packedCommandStream.toLawful.decode (bytes.drop commandFrame.length) else none
  decode_encode := by
    intro command
    have decoded := packedCommandStream.toLawful.decode_encode command
    change packedCommandStream.toLawful.decode (packedCommandStream.encode command) = some command at decoded
    simp [decoded]

def commandCodec : LawfulCodec PackedCommand := ResourceBirthCodec.strictCodec rawCommandCodec

theorem command_decode_canonical {bytes : List UInt8} {command : PackedCommand}
    (decoded : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCommandCodec decoded

/-- The version-1 frame: its declaration carried `expectedPreRoot`, the whole
authority-cell root. -/
def retiredFrameV1 : List UInt8 := commandFrameName ++ [1]

/-- Why bytes that do not decode are refused, naming a retired version. -/
def undecodable (bytes : List UInt8) : String :=
  if bytes.take retiredFrameV1.length = retiredFrameV1 then
    "delegation command v1 is retired: it signed the whole authority-cell root (expectedPreRoot); \
     v2 binds the parent by its signed id"
  else "noncanonical delegation command"

/-- **A version-1 command refuses**, and by name. -/
theorem retired_v1_refused (rest : List UInt8) :
    commandCodec.decode (retiredFrameV1 ++ rest) = none ∧
      undecodable (retiredFrameV1 ++ rest) =
        "delegation command v1 is retired: it signed the whole authority-cell root (expectedPreRoot); \
         v2 binds the parent by its signed id" := by
  constructor
  · cases decoded : commandCodec.decode (retiredFrameV1 ++ rest) with
    | none => rfl
    | some command =>
        have exact := command_decode_canonical decoded
        have framed := congrArg (List.take commandFrame.length) exact
        simp [commandCodec, ResourceBirthCodec.strictCodec, rawCommandCodec] at framed
        simp [commandFrame, retiredFrameV1, commandFrameName, List.take_append] at framed
  · simp [undecodable]

def operationMarker {kind : ResourceKind} (domain semantics : Digest) (command : Command kind) : Nat :=
  (Sp800185Cshake256.hash "DREGG.CAPABILITY.DELEGATE.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product ResourceBirthCodec.resourceKindStream
          (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
            (StreamCodec.product StreamCodec.nat StreamCodec.nat))))).encode
      (domain, semantics, kind, command.subject, command.declaration.target.value, command.nonce))).digest.value

def commandBytes {kind : ResourceKind} (domain semantics : Digest) (command : Command kind)
    (declaration : DelegateDeclaration kind) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
    (domain, semantics, commandCodec.encode ⟨kind, { command with declaration := declaration }⟩)

def effectsDigest {kind : ResourceKind} (domain semantics : Digest) (command : Command kind)
    (declaration : DelegateDeclaration kind) : Digest :=
  (Sp800185Cshake256.hash "DREGG.CAPABILITY.DELEGATE.EFFECT/v1".toUTF8.toList
    (commandBytes domain semantics command declaration)).digest

structure Ambient where
  federation : FederationId
  height : Height

def context {kind : ResourceKind} (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command kind) : DelegationContext where
  domain := snapshot.domain
  semantics := semantics
  federation := ambient.federation
  subject := command.subject
  subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
  height := ambient.height
  cost := (commandCodec.encode ⟨kind, command⟩).length
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.CAPABILITY.DELEGATE.ARGS/v1".toUTF8.toList
      (commandBytes snapshot.domain semantics command command.declaration ++ bytes)).digest

def request {kind : ResourceKind} (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command kind) : Request kind :=
  (context snapshot semantics ambient command).request (declarationCodec kind)
    (effectsDigest snapshot.domain semantics command) snapshot.cell command.declaration

def child {kind : ResourceKind} (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command kind) (parent : StoredCapability kind) : StoredCapability kind :=
  delegatedCapability command.declaration.child parent (request snapshot semantics ambient command)

inductive Reject where
  | malformedCommand | directoryUnavailable | authorityUnavailable | targetUnavailable
  | staleTarget | staleAuthority | identity | parentUnavailable | lineage | descent
  | shape | validation | physicalPreparation
  /-- The operation marker is already spent (the delegation was admitted before). -/
  | replayedMarker
  /-- The request did not declare the operation marker's replay nullifier, so its
  ground has no answer for it (`ServedBasis.Ground.markerSpent`): refused, never
  read as unspent. -/
  | undeclaredMarker
  /-- The request did not declare the delegation's transaction id, so its ground
  has no journal answer for it (`ServedBasis.Ground.replayOf`): refused, never read
  as "not recorded". -/
  | undeclaredTransaction
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias | parentSubstitution
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

def DescentReady {kind : ResourceKind} (snapshot : Snapshot) (command : Command kind)
    (parent : StoredCapability kind) : Prop :=
  readCapability snapshot.cell kind command.declaration.parentId = some parent ∧
    parent.head.id = command.declaration.parentId ∧
    CapabilityIdFresh snapshot.cell command.declaration.child.id ∧
    command.declaration.child.issuerEpoch = issuerEpochAt snapshot.cell command.declaration.child.issuer ∧
    command.declaration.child.policyEpoch = policyEpochAt snapshot.cell command.declaration.child.policyId ∧
    isRegistered snapshot.cell (.capability command.declaration.child.id) = false ∧
    (∀ ancestor ∈ command.declaration.child.ancestors,
      isRegistered snapshot.cell (.capability ancestor) = true) ∧
    (∀ channel ∈ command.declaration.child.channels,
      isRegistered snapshot.cell (.channel channel) = true) ∧
    isRevoked snapshot.cell (.capability command.declaration.child.id) = false ∧
    (∀ ancestor ∈ command.declaration.child.ancestors,
      isRevoked snapshot.cell (.capability ancestor) = false) ∧
    (∀ channel ∈ command.declaration.child.channels,
      isRevoked snapshot.cell (.channel channel) = false)

instance descentReadyDecidable {kind : ResourceKind} (snapshot : Snapshot)
    (command : Command kind) (parent : StoredCapability kind) : Decidable (DescentReady snapshot command parent) := by
  unfold DescentReady
  infer_instance

/-- The parent projection every lineage and delegation check of this controller
is decided at: the one carried by the authority projection it admits against. -/
abbrev parentage {kind : ResourceKind} (snapshot : Snapshot) (command : Command kind) :
    Parentage :=
  (authState snapshot.cell).parent

def descentEvidence {kind : ResourceKind} (snapshot : Snapshot) (command : Command kind)
    (parent : StoredCapability kind) (ready : DescentReady snapshot command parent)
    (valid : LineageValid (parentage snapshot command) parent) (anchored : LineageAnchored snapshot.cell parent) :
    DescentEvidence snapshot.cell command.declaration.parentId command.declaration.child parent := by
  rcases ready with ⟨lookup, parentId, fresh, issuer, generation,
    selfUnregistered, ancestorsRegistered, channelsRegistered, selfLive, ancestorsLive, channelsLive⟩
  exact ⟨lookup, parentId, valid, anchored, fresh, issuer, generation,
    selfUnregistered, ancestorsRegistered, channelsRegistered, selfLive, ancestorsLive, channelsLive⟩

abbrev ObservedTarget (deployment : Deployment) (directory : Directory Nat Registry)
    {kind : ResourceKind} (command : Command kind) :=
  ResourceTargetAdmission.Observed deployment directory kind command.declaration.target.value command.expectedTargetRoot

def observeTarget (deployment : Deployment) (directory : Directory Nat Registry)
    {kind : ResourceKind} (command : Command kind) : Option (ObservedTarget deployment directory command) :=
  ResourceTargetAdmission.observe deployment directory kind command.declaration.target.value command.expectedTargetRoot

/-- A prepared delegation over the directory and authority snapshot it read. -/
structure PreparedOn {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (directory : Directory Nat Registry)
    (authority : Snapshot) {kind : ResourceKind} (command : Command kind) where
  private mk ::
  target : ObservedTarget deployment directory command
  parent : StoredCapability kind
  descent : DescentEvidence authority.cell
    command.declaration.parentId command.declaration.child parent
  shape : CredentialAuthorityFamily.DelegationShape
    (request authority profile.semantics ambient command) command.declaration.child parent.head
    (parentage authority command)
  policyTarget : command.declaration.child.policyId = ⟨command.declaration.target.value⟩
  identity : command.declaration.operationNullifier = operationMarker authority.domain profile.semantics command
  validated : ValidatedPatch AuthorityMaterializer authority.cell authority.cell.root
    (command.declaration.patch parent (request authority profile.semantics ambient command)
      authority.logical)
  source : CanonicalCellRegistry.LoadedPolicySource authority.domain directory
    (authority.authState.policyAddress command.declaration.child.policyId
      (authority.authState.policyRevision command.declaration.child.policyId))

/-- The preparation over what it reads: the directory, the authority snapshot and
the operation marker's spent answer (`none`: not declared by the request, refused
`undeclaredMarker` before anything else is read). The marker's spent bit is read
only through that answer, never from the snapshot. -/
def prepareOn {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (directory : Directory Nat Registry)
    (authority : Snapshot) (markerSpent : Option Bool) {kind : ResourceKind} (command : Command kind) :
    Except Reject (PreparedOn deployment profile ambient directory authority command) := do
  -- An undeclared marker is refused first, before any state is read.
  let some spent := markerSpent | throw .undeclaredMarker
  let target ← requireSome .targetUnavailable (observeTarget deployment directory command)
  let parent ← requireSome .parentUnavailable (readCapability authority.cell kind command.declaration.parentId)
  if ready : DescentReady authority command parent then
    if lineage : storedLineageCheck authority.cell
        (parentage authority command) parent = true then
      if shape : CredentialAuthorityFamily.DelegationShape
          (request authority profile.semantics ambient command) command.declaration.child parent.head
          (parentage authority command) then
        if policyTarget : command.declaration.child.policyId = ⟨command.declaration.target.value⟩ then
          if identity : command.declaration.operationNullifier = operationMarker authority.domain profile.semantics command then
            if spent then .error .replayedMarker else
            match validate AuthorityMaterializer authority.cell authority.cell.root
                (command.declaration.patch parent (request authority profile.semantics ambient command)
                  authority.logical) with
            | .rejected _ => .error .validation
            | .accepted validated =>
                let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                  authority.domain directory
                  (authority.authState.policyAddress command.declaration.child.policyId
                    (authority.authState.policyRevision command.declaration.child.policyId)))
                let facts := (storedLineageCheck_iff authority.cell
                  (parentage authority command) parent).mp lineage
                .ok ⟨target, parent,
                  descentEvidence authority command parent ready facts.1 facts.2,
                  shape, policyTarget, identity, validated, source⟩
          else .error .identity
        else .error .shape
      else .error .shape
    else .error .lineage
  else .error .descent

/-- A prepared delegation over a ground (`ServedBasis.Ground`): the light route's
basis or the full shape. -/
abbrev Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (ground : Ground deployment)
    {kind : ResourceKind} (command : Command kind) :=
  PreparedOn deployment profile ambient ground.directory ground.authority command

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (ground : Ground deployment)
    {kind : ResourceKind} (command : Command kind) :
    Except Reject (Prepared deployment profile ambient ground command) :=
  prepareOn deployment profile ambient ground.directory ground.authority
    (ground.markerSpent (operationMarker ground.authority.domain profile.semantics command)) command

theorem prepareOn_map_congr {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient)
    {directory directory' : Directory Nat Registry} {authority authority' : Snapshot}
    {spent spent' : Option Bool} {kind : ResourceKind} (command : Command kind)
    (directories : directory = directory') (authorities : authority = authority') (answers : spent = spent') :
    (prepareOn deployment profile ambient directory authority spent command).map (fun _ => ()) =
      (prepareOn deployment profile ambient directory' authority' spent' command).map (fun _ => ()) := by
  subst directories authorities answers
  rfl

/-- **The delegation is prepared alike on any two grounds that read alike**: the
same decoded directory, the same authority snapshot (its cell, the clock at the
height) and the same verified answer for the operation marker — the one key the
preparation consults beyond the state — give the same refusal, or both prepare.
On the light route the marker's answer is the spent map's verified answer at the
served height (`Ground.markerSpent_some`, `Basis.view_consumed_declared`); on the
full shape it is the full snapshot's consumed bit (`Ground.markerSpent_full`). -/
theorem prepare_agrees {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (light full : Ground deployment)
    {kind : ResourceKind} (command : Command kind)
    (directories : light.directory = full.directory) (authorities : light.authority = full.authority)
    (markers : light.markerSpent (operationMarker light.authority.domain profile.semantics command) =
      full.markerSpent (operationMarker full.authority.domain profile.semantics command)) :
    (prepare deployment profile ambient light command).map (fun _ => ()) =
      (prepare deployment profile ambient full command).map (fun _ => ()) :=
  prepareOn_map_congr deployment profile ambient command directories authorities markers

/-- With no answer for the marker, the preparation refuses exactly `undeclaredMarker`. -/
theorem prepareOn_unanswered {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (directory : Directory Nat Registry)
    (authority : Snapshot) {kind : ResourceKind} (command : Command kind) :
    prepareOn deployment profile ambient directory authority none command = .error .undeclaredMarker := rfl

/-- **An undeclared marker is refused by name** (the plant's pole): a light basis
that did not declare the marker's replay nullifier refuses the delegation exactly
`undeclaredMarker`, whatever the state. -/
theorem prepare_undeclared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) {store : DurableHistory.StoreIdentity}
    (basis : ServedBasis.Basis deployment store) {kind : ResourceKind} (command : Command kind)
    (undeclared : CredentialAuthorityReplay.nullifier deployment.domain
        (operationMarker (ServedBasis.Ground.ofBasis basis).authority.domain profile.semantics command) ∉
          basis.keys.nullifiers) :
    prepare deployment profile ambient (ServedBasis.Ground.ofBasis basis) command = .error .undeclaredMarker := by
  unfold prepare
  rw [ServedBasis.Ground.markerSpent_undeclared basis _ undeclared]
  rfl

#assert_axioms prepare_agrees
#assert_axioms prepare_undeclared

/-! ## The same source-derived authority tuple supplies the policy view. -/

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {ground : Ground deployment}
  {kind : ResourceKind} {command : Command kind}

/-- The authority cell after the delegation: the family's own validated patch
applied to the loaded cell. It is the one authority write. -/
def Prepared.authorityPost (prepared : Prepared deployment profile ambient ground command) :
    CredentialAuthorityDomain.Cell :=
  prepared.validated.apply

def layout (prepared : Prepared deployment profile ambient ground command) : CellLayout Unit where
  storeLayout _ := CredentialAuthorityState.layout
  materializer _ := AuthorityMaterializer
  projectAuthority := fun _ _ => authState ground.authority.cell
  cellId _ := cellIdOf deployment

def rawLeg (prepared : Prepared deployment profile ambient ground command) :
    CandidateLegData (layout prepared) () where
  pre := ground.authority.cell
  patch := command.declaration.patch prepared.parent (request ground.authority profile.semantics ambient command)
    ground.authority.logical
  request := ⟨kind, request ground.authority profile.semantics ambient command⟩
  Postcondition := fun logical =>
    (command.declaration.patch prepared.parent
      (request ground.authority profile.semantics ambient command)
        ground.authority.logical).ResultAt
      ground.authority.logical logical ∧
    LineageAnchored (materialize AuthorityMaterializer logical)
      (child ground.authority profile.semantics ambient command prepared.parent)

def plan (prepared : Prepared deployment profile ambient ground command) : PreparationPlan (layout prepared) Unit where
  leg _ _ := rawLeg prepared
  jointDigest _ := effectsDigest ground.authority.domain profile.semantics command command.declaration
  legEffectsDigest _ _ := effectsDigest ground.authority.domain profile.semantics command command.declaration
  bindFamily _ portals _ :=
    { Nullifier := Nat
      family := delegateFamily ground.authority.cell
        (portals ()) (context ground.authority profile.semantics ambient command)
        (declarationCodec kind) (storedCapabilityStream kind).toLawful
        (effectsDigest ground.authority.domain profile.semantics command)
      declaration := command.declaration
      outcome := prepared.parent
      preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
      postconditionExact := fun _ => Iff.rfl }

theorem child_anchored (prepared : Prepared deployment profile ambient ground command) :
    LineageAnchored prepared.validated.apply
      (child ground.authority profile.semantics ambient command prepared.parent) := by
  have preserved := capabilityProduction_preserves_present prepared.validated
    (DelegateDeclaration.patch_writeFootprint _ _ _ _) prepared.descent.childSlotFresh
  have parentPresent : readCapability ground.authority.cell kind prepared.parent.head.id = some prepared.parent := by
    rw [prepared.descent.parentIdExact]
    exact prepared.descent.parentExact
  exact ⟨preserved kind prepared.parent.head.id prepared.parent parentPresent,
    prepared.descent.parentLineageAnchored.of_present_reads_preserved preserved⟩

def tuple (prepared : Prepared deployment profile ambient ground command) : PreparedTuple (plan prepared) where
  source := ()
  primary := ()
  validated _ := prepared.validated
  postconditions _ := ⟨prepared.validated.resultAt, child_anchored prepared⟩
  cellIdsDistinct := fun _ _ _ => Subsingleton.elim _ _
  requestEffects _ := rfl

def project (prepared : Prepared deployment profile ambient ground command) (_ : Unit)
    (logical : (incidence : Unit) → Store ((layout prepared).storeLayout incidence)) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots ground.directory command.declaration.target.value ++
    CanonicalRuntimeProfile.requestSlots (request ground.authority profile.semantics ambient command) ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode ⟨kind, command⟩) ++
    DeclaredResourceController.bytesSlots "resource/bytes" 0 (PackedCell.bytes Registry prepared.target.before) ++
    ResourceAuthorityProjection.grantSlots "authority/parent" kind command.declaration.parentId (logical ()) ++
    ResourceAuthorityProjection.grantSlots "authority/child" kind command.declaration.child.id (logical ())⟩

/-- A delegation law can inspect the selected parent and proposed child;
unrelated authority records cannot affect its source-owned predicate view. -/
theorem project_noninterference (prepared : Prepared deployment profile ambient ground command)
    (left right : (incidence : Unit) → Store ((layout prepared).storeLayout incidence))
    (parent : (left ()) ⟨.capability kind, command.declaration.parentId⟩ =
      (right ()) ⟨.capability kind, command.declaration.parentId⟩)
    (parentRevoked : (left ()) ⟨.revoked, .capability command.declaration.parentId⟩ =
      (right ()) ⟨.revoked, .capability command.declaration.parentId⟩)
    (child : (left ()) ⟨.capability kind, command.declaration.child.id⟩ =
      (right ()) ⟨.capability kind, command.declaration.child.id⟩)
    (childRevoked : (left ()) ⟨.revoked, .capability command.declaration.child.id⟩ =
      (right ()) ⟨.revoked, .capability command.declaration.child.id⟩) :
    project prepared () left = project prepared () right := by
  unfold project
  rw [ResourceAuthorityProjection.grantSlots_noninterference _ _ _ (left ()) (right ()) parent parentRevoked,
    ResourceAuthorityProjection.grantSlots_noninterference _ _ _ (left ()) (right ()) child childRevoked]

def step (prepared : Prepared deployment profile ambient ground command) : PolicyStepContext :=
  PolicyStepContext.ofPreparedTuple (project prepared) profile.semantics (tuple prepared)

def sourceStore (prepared : Prepared deployment profile ambient ground command) : CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource ground.authority.domain ground.directory⟩

/-- Management uses the same current structural roots as edits and reads. -/
def kindDependencies (prepared : Prepared deployment profile ambient ground command) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment ground.directory command.declaration.target.value

def policyConfig [DecidableEq F] (prepared : Prepared deployment profile ambient ground command) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile ground.authority
    ground.directory
    (sourceCapabilityPortal ground.authority command.declaration.operationNullifier)
    (step prepared) command.declaration.target.value
    ((kindDependencies prepared).map (·.additional) |>.getD [])

/-- Missing kind/history dependencies refuse at both semantic and CAS boundaries. -/
def lawReadGuards (prepared : Prepared deployment profile ambient ground command) :
    Option (List (Nat × Digest)) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards ground.authority
    ground.directory profile.semantics command.declaration.target.value structural.additional
  pure (sources ++ structural.readGuards)

def portal [DecidableEq F] (prepared : Prepared deployment profile ambient ground command) : Portal :=
  (policyConfig prepared).portal

/-- The snapshot carries its authorization projection memoised
(`Snapshot.authStateExact`); the family is indexed by the cell's own
projection.  They are equal, so an authorization moves across unchanged. -/
def reindexAuthorization {source target : AuthState} {portal : Portal}
    {kind : ResourceKind} {request : Request kind} (same : source = target)
    (authorization : Authorized portal target request) : Authorized portal source request :=
  same.symm ▸ authorization

theorem reindexAuthorization_capabilityValue {source target : AuthState} {portal : Portal}
    {kind : ResourceKind} {request : Request kind} (same : source = target)
    (authorization : Authorized portal target request) :
    (reindexAuthorization same authorization).evidence.capabilityValue =
      authorization.evidence.capabilityValue := by
  cases same
  rfl

def mode [DecidableEq F] (prepared : Prepared deployment profile ambient ground command)
    (authorization : Authorized (portal prepared) ground.authority.authState
      (request ground.authority profile.semantics ambient command))
    (named : authorization.evidence.capabilityValue =
      some (prepared.parent.head, storedCapabilityDigest ground.authority prepared.parent)) :
    DelegationEvidence ground.authority.cell
      (portal prepared) (context ground.authority profile.semantics ambient command)
      (declarationCodec kind) (effectsDigest ground.authority.domain profile.semantics command)
      command.declaration prepared.parent where
  toDescentEvidence := prepared.descent
  parentCommitment := storedCapabilityDigest ground.authority prepared.parent
  parentAuthorization := reindexAuthorization ground.authority.authStateExact.symm authorization
  parentNamed := (reindexAuthorization_capabilityValue
    ground.authority.authStateExact.symm authorization).trans named
  shape := prepared.shape

attribute [irreducible] portal

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient ground command) (envelope : List UInt8) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature ground.authority
  envelopeExact : receipt.envelopeBytes = envelope
  authorization : Authorized (portal prepared) ground.authority.authState
    (request ground.authority profile.semantics ambient command)
  parentNamed : authorization.evidence.capabilityValue =
    some (prepared.parent.head, storedCapabilityDigest ground.authority prepared.parent)

def authorize [DecidableEq F] (prepared : Prepared deployment profile ambient ground command)
    (receipt : CredentialSignatureAdmission.CheckedSignature ground.authority) :
    Except Reject { authorization : Authorized (portal prepared) ground.authority.authState
        (request ground.authority profile.semantics ambient command) //
      authorization.evidence.capabilityValue =
        some (prepared.parent.head, storedCapabilityDigest ground.authority prepared.parent) } := by
  unfold portal
  exact do
    let wanted := request ground.authority profile.semantics ambient command
    let config := policyConfig prepared
    let _ ← requireSome .policyUnavailable (kindDependencies prepared)
    match supplied : config.capabilityEvidenceChecked wanted command.declaration.parentId
        () receipt () (fun _ => ()) with
    | .error _ => .error .capabilityRejected
    | .ok evidence =>
      let law ← requireSome .policyUnavailable config.resolve?
      let witness := law.witness
      if inputsInRange profile.compilerProfile.compiler law.predicate
          (step prepared).oldState (step prepared).newState != true then
        throw .policyInputRange
      if !decide (castInjOn F (intsOf law.predicate (step prepared).oldState (step prepared).newState)) then
        throw .policyCastAlias
      let epochExact : wanted.policyEpoch = ground.authority.authState.policyEpoch wanted.policyId := by
        rw [CredentialAuthorityDomain.Snapshot.authState_policyEpoch]
        exact prepared.descent.policyCurrent
      let revisionExact : wanted.policyRevision = ground.authority.authState.policyRevision wanted.policyId := by
        rw [CredentialAuthorityDomain.Snapshot.authState_policyRevision]
        rfl
      match admitted : ComposedPolicyAdmission.admit config wanted evidence witness
          (.policy wanted.policyId wanted.policyRevision) epochExact revisionExact with
      | none => .error .policyRejected
      | some authorization =>
        .ok ⟨authorization, by
          have unchanged := ComposedPolicyAdmission.admit_preserves_evidence config
            wanted evidence witness (.policy wanted.policyId wanted.policyRevision) epochExact revisionExact admitted
          have named := config.capabilityEvidence_names_stored wanted command.declaration.parentId
            () receipt () (fun _ => ()) supplied
          obtain ⟨parent, parentExact, evidenceExact⟩ := named
          have parentSame : parent = prepared.parent := Option.some.inj (parentExact.symm.trans prepared.descent.parentExact)
          subst parent
          rw [unchanged]
          exact evidenceExact⟩

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient ground command) (envelope : List UInt8) :
    IO (Except Reject (Accepted prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native ground.authority
      command.declaration.operationNullifier (request ground.authority profile.semantics ambient command) envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
    if same : receipt.envelopeBytes = envelope then
      match authorize prepared receipt with
      | .error reason => return .error reason
      | .ok authorization => return .ok ⟨receipt, same, authorization.val, authorization.property⟩
    else return .error .parentSubstitution

def Accepted.evidence [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    (tuple prepared).AdmissionEvidence (fun _ => portal prepared) where
  modes _ := mode prepared accepted.authorization accepted.parentNamed
  authorizations _ := reindexAuthorization ground.authority.authStateExact.symm
    accepted.authorization
  disclosure _ := .sealed
  disclosureAllowed _ := trivial

def Accepted.declaration [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (_accepted : Accepted prepared envelope) :=
  (tuple prepared).toDeclaration (fun _ => portal prepared)
    (effectsDigest ground.authority.domain profile.semantics command command.declaration)

def Accepted.legs [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) : accepted.declaration.AcceptedLegs :=
  (tuple prepared).accept (fun _ => portal prepared)
    (effectsDigest ground.authority.domain profile.semantics command command.declaration) accepted.evidence

theorem Accepted.post_exact [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    (accepted.declaration.post accepted.legs ()).logical = prepared.authorityPost.logical :=
  congrArg Materialized.logical
    ((tuple prepared).accepted_posts_exact (fun _ => portal prepared)
      (effectsDigest ground.authority.domain profile.semantics command command.declaration) accepted.evidence ())

theorem Accepted.child_lineage [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    LineageValid (parentage ground.authority command)
      (child ground.authority profile.semantics ambient command prepared.parent) :=
  (mode prepared accepted.authorization accepted.parentNamed).childLineageValid

theorem Accepted.parent_authorized [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    accepted.authorization.evidence.capabilityValue =
      some (prepared.parent.head, storedCapabilityDigest ground.authority prepared.parent) :=
  accepted.parentNamed

/-- The selected current policy evaluated the scoped view of the actual old
and source-computed authority states. The physical receiver proves this same post image
is installed; no caller-selected predicate state appears in either statement. -/
theorem Accepted.policy_evaluated_actual_post [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    ∃ graph : PolicyComponentResolution.LoadedGraph
        (policyConfig prepared).snapshot (policyConfig prepared).store
        (policyConfig prepared).profile.semantics (policyConfig prepared).target
        (policyConfig prepared).additional,
      PolicyComponentResolution.loadTarget (policyConfig prepared).snapshot
        (policyConfig prepared).store (policyConfig prepared).profile.semantics
        (policyConfig prepared).target (policyConfig prepared).resolutionBudget
        (policyConfig prepared).additional = .ok graph ∧
      Minidregg.Pred.eval (ResolvedLawCompilation.predicate graph.resolved)
        (step prepared).oldState (step prepared).newState = true := by
  apply ComposedPolicyAdmission.authorized_effective_law (policyConfig prepared)
    (request ground.authority profile.semantics ambient command)
  simpa only [portal] using accepted.authorization

/-- info: 'Minidregg.Kernel.CapabilityDelegationController.project_noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms project_noninterference

end Minidregg.Kernel.CapabilityDelegationController
