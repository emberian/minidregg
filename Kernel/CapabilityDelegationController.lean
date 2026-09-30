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
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer

def declarationStream (kind : ResourceKind) : StreamCodec (DelegateDeclaration kind) :=
  StreamCodec.xmap
    (StreamCodec.product (capabilityStream kind)
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product (TypedAuthorizationRequestCodec.resourceIdStream kind)
          (StreamCodec.product digestStream StreamCodec.nat))))
    (fun declaration => (declaration.child, declaration.parentId, declaration.target,
      declaration.expectedPreRoot, declaration.operationNullifier))
    (fun (child, parentId, target, root, marker) => ⟨child, parentId, target, root, marker⟩)
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

def commandFrame : List UInt8 := "DREGG/CAPABILITY/DELEGATE".toUTF8.toList ++ [1]

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
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias | parentSubstitution
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

def DescentReady {kind : ResourceKind} (snapshot : Snapshot) (command : Command kind)
    (parent : StoredCapability kind) : Prop :=
  command.declaration.expectedPreRoot = snapshot.cell.root ∧
    readCapability snapshot.cell kind command.declaration.parentId = some parent ∧
    parent.head.id = command.declaration.parentId ∧
    CapabilityIdFresh snapshot.cell command.declaration.child.id ∧
    snapshot.spent command.declaration.operationNullifier = false ∧
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
    DescentEvidence snapshot.cell command.declaration.expectedPreRoot
      command.declaration.parentId command.declaration.child parent := by
  rcases ready with ⟨root, lookup, parentId, fresh, _unspent, issuer, generation,
    selfUnregistered, ancestorsRegistered, channelsRegistered, selfLive, ancestorsLive, channelsLive⟩
  exact ⟨root, lookup, parentId, valid, anchored, fresh, issuer, generation,
    selfUnregistered, ancestorsRegistered, channelsRegistered, selfLive, ancestorsLive, channelsLive⟩

abbrev ObservedTarget (deployment : Deployment) (directory : Directory Nat Registry)
    {kind : ResourceKind} (command : Command kind) :=
  ResourceTargetAdmission.Observed deployment directory kind command.declaration.target.value command.expectedTargetRoot

def observeTarget (deployment : Deployment) (directory : Directory Nat Registry)
    {kind : ResourceKind} (command : Command kind) : Option (ObservedTarget deployment directory command) :=
  ResourceTargetAdmission.observe deployment directory kind command.declaration.target.value command.expectedTargetRoot

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    {kind : ResourceKind} (command : Command kind) where
  private mk ::
  directory : LoadedDirectory durable
  authority : Loaded deployment durable.snapshot
  target : ObservedTarget deployment directory.directory command
  parent : StoredCapability kind
  descent : DescentEvidence authority.snapshot.cell
    command.declaration.expectedPreRoot command.declaration.parentId command.declaration.child parent
  shape : CredentialAuthorityFamily.DelegationShape
    (request authority.snapshot profile.semantics ambient command) command.declaration.child parent.head
    (parentage authority.snapshot command)
  policyTarget : command.declaration.child.policyId = ⟨command.declaration.target.value⟩
  identity : command.declaration.operationNullifier = operationMarker authority.snapshot.domain profile.semantics command
  validated : ValidatedPatch AuthorityMaterializer authority.snapshot.cell authority.snapshot.cell.root
    (command.declaration.patch parent (request authority.snapshot profile.semantics ambient command)
      authority.snapshot.logical)
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress command.declaration.child.policyId
      (authority.snapshot.authState.policyRevision command.declaration.child.policyId))

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    {kind : ResourceKind} (command : Command kind) :
    Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let target ← requireSome .targetUnavailable (observeTarget deployment directory.directory command)
  let parent ← requireSome .parentUnavailable (readCapability authority.snapshot.cell kind command.declaration.parentId)
  if ready : DescentReady authority.snapshot command parent then
    if lineage : storedLineageCheck authority.snapshot.cell
        (parentage authority.snapshot command) parent = true then
      if shape : CredentialAuthorityFamily.DelegationShape
          (request authority.snapshot profile.semantics ambient command) command.declaration.child parent.head
          (parentage authority.snapshot command) then
        if policyTarget : command.declaration.child.policyId = ⟨command.declaration.target.value⟩ then
          if identity : command.declaration.operationNullifier = operationMarker authority.snapshot.domain profile.semantics command then
            match validate AuthorityMaterializer authority.snapshot.cell authority.snapshot.cell.root
                (command.declaration.patch parent (request authority.snapshot profile.semantics ambient command)
                  authority.snapshot.logical) with
            | .rejected _ => .error .validation
            | .accepted validated =>
                let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                  authority.snapshot.domain directory.directory
                  (authority.snapshot.authState.policyAddress command.declaration.child.policyId
                    (authority.snapshot.authState.policyRevision command.declaration.child.policyId)))
                let facts := (storedLineageCheck_iff authority.snapshot.cell
                  (parentage authority.snapshot command) parent).mp lineage
                .ok ⟨directory, authority, target, parent,
                  descentEvidence authority.snapshot command parent ready facts.1 facts.2,
                  shape, policyTarget, identity, validated, source⟩
          else .error .identity
        else .error .shape
      else .error .shape
    else .error .lineage
  else .error .descent

/-! ## The same source-derived authority tuple supplies the policy view. -/

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {kind : ResourceKind} {command : Command kind}

/-- The authority cell after the delegation: the family's own validated patch
applied to the loaded cell. It is the one authority write. -/
def Prepared.authorityPost (prepared : Prepared deployment profile ambient durable command) :
    CredentialAuthorityDomain.Cell :=
  prepared.validated.apply

def layout (prepared : Prepared deployment profile ambient durable command) : CellLayout Unit where
  storeLayout _ := CredentialAuthorityState.layout
  materializer _ := AuthorityMaterializer
  projectAuthority := fun _ _ => authState prepared.authority.snapshot.cell
  cellId _ := cellIdOf deployment

def rawLeg (prepared : Prepared deployment profile ambient durable command) :
    CandidateLegData (layout prepared) () where
  pre := prepared.authority.snapshot.cell
  patch := command.declaration.patch prepared.parent (request prepared.authority.snapshot profile.semantics ambient command)
    prepared.authority.snapshot.logical
  request := ⟨kind, request prepared.authority.snapshot profile.semantics ambient command⟩
  Postcondition := fun logical =>
    (command.declaration.patch prepared.parent
      (request prepared.authority.snapshot profile.semantics ambient command)
        prepared.authority.snapshot.logical).ResultAt
      prepared.authority.snapshot.logical logical ∧
    LineageAnchored (materialize AuthorityMaterializer logical)
      (child prepared.authority.snapshot profile.semantics ambient command prepared.parent)

def plan (prepared : Prepared deployment profile ambient durable command) : PreparationPlan (layout prepared) Unit where
  leg _ _ := rawLeg prepared
  jointDigest _ := effectsDigest prepared.authority.snapshot.domain profile.semantics command command.declaration
  legEffectsDigest _ _ := effectsDigest prepared.authority.snapshot.domain profile.semantics command command.declaration
  bindFamily _ portals _ :=
    { Nullifier := Nat
      family := delegateFamily prepared.authority.snapshot.cell
        (portals ()) (context prepared.authority.snapshot profile.semantics ambient command)
        (declarationCodec kind) (storedCapabilityStream kind).toLawful
        (effectsDigest prepared.authority.snapshot.domain profile.semantics command)
      declaration := command.declaration
      outcome := prepared.parent
      preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
      postconditionExact := fun _ => Iff.rfl }

theorem child_anchored (prepared : Prepared deployment profile ambient durable command) :
    LineageAnchored prepared.validated.apply
      (child prepared.authority.snapshot profile.semantics ambient command prepared.parent) := by
  have preserved := capabilityProduction_preserves_present prepared.validated
    (DelegateDeclaration.patch_writeFootprint _ _ _ _) prepared.descent.childSlotFresh
  have parentPresent : readCapability prepared.authority.snapshot.cell kind prepared.parent.head.id = some prepared.parent := by
    rw [prepared.descent.parentIdExact]
    exact prepared.descent.parentExact
  exact ⟨preserved kind prepared.parent.head.id prepared.parent parentPresent,
    prepared.descent.parentLineageAnchored.of_present_reads_preserved preserved⟩

def tuple (prepared : Prepared deployment profile ambient durable command) : PreparedTuple (plan prepared) where
  source := ()
  primary := ()
  validated _ := prepared.validated
  postconditions _ := ⟨prepared.validated.resultAt, child_anchored prepared⟩
  cellIdsDistinct := fun _ _ _ => Subsingleton.elim _ _
  requestEffects _ := rfl

def project (prepared : Prepared deployment profile ambient durable command) (_ : Unit)
    (logical : (incidence : Unit) → Store ((layout prepared).storeLayout incidence)) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots (request prepared.authority.snapshot profile.semantics ambient command) ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode ⟨kind, command⟩) ++
    DeclaredResourceController.bytesSlots "resource/bytes" 0 (PackedCell.bytes Registry prepared.target.before) ++
    ResourceAuthorityProjection.grantSlots "authority/parent" kind command.declaration.parentId (logical ()) ++
    ResourceAuthorityProjection.grantSlots "authority/child" kind command.declaration.child.id (logical ())⟩

/-- A delegation law can inspect the selected parent and proposed child;
unrelated authority records cannot affect its source-owned predicate view. -/
theorem project_noninterference (prepared : Prepared deployment profile ambient durable command)
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

def step (prepared : Prepared deployment profile ambient durable command) : PolicyStepContext :=
  PolicyStepContext.ofPreparedTuple (project prepared) profile.semantics (tuple prepared)

def sourceStore (prepared : Prepared deployment profile ambient durable command) : CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource prepared.authority.snapshot.domain prepared.directory.directory⟩

def policyConfig [DecidableEq F] (prepared : Prepared deployment profile ambient durable command) : CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile prepared.authority.snapshot (sourceStore prepared)
    (sourceCapabilityPortal prepared.authority.snapshot command.declaration.operationNullifier) (step prepared)

def portal [DecidableEq F] (prepared : Prepared deployment profile ambient durable command) : Portal :=
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

def mode [DecidableEq F] (prepared : Prepared deployment profile ambient durable command)
    (authorization : Authorized (portal prepared) prepared.authority.snapshot.authState
      (request prepared.authority.snapshot profile.semantics ambient command))
    (named : authorization.evidence.capabilityValue =
      some (prepared.parent.head, storedCapabilityDigest prepared.authority.snapshot prepared.parent)) :
    DelegationEvidence prepared.authority.snapshot.cell
      (portal prepared) (context prepared.authority.snapshot profile.semantics ambient command)
      (declarationCodec kind) (effectsDigest prepared.authority.snapshot.domain profile.semantics command)
      command.declaration prepared.parent where
  toDescentEvidence := prepared.descent
  parentCommitment := storedCapabilityDigest prepared.authority.snapshot prepared.parent
  parentAuthorization := reindexAuthorization prepared.authority.snapshot.authStateExact.symm authorization
  parentNamed := (reindexAuthorization_capabilityValue
    prepared.authority.snapshot.authStateExact.symm authorization).trans named
  shape := prepared.shape

attribute [irreducible] portal

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) (envelope : List UInt8) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = envelope
  authorization : Authorized (portal prepared) prepared.authority.snapshot.authState
    (request prepared.authority.snapshot profile.semantics ambient command)
  parentNamed : authorization.evidence.capabilityValue =
    some (prepared.parent.head, storedCapabilityDigest prepared.authority.snapshot prepared.parent)

def authorize [DecidableEq F] (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject { authorization : Authorized (portal prepared) prepared.authority.snapshot.authState
        (request prepared.authority.snapshot profile.semantics ambient command) //
      authorization.evidence.capabilityValue =
        some (prepared.parent.head, storedCapabilityDigest prepared.authority.snapshot prepared.parent) } := by
  unfold portal
  exact do
    let wanted := request prepared.authority.snapshot profile.semantics ambient command
    let config := policyConfig prepared
    match supplied : sourceCapabilityOnlyEvidence profile.compilerProfile prepared.authority.snapshot
        (sourceStore prepared) command.declaration.operationNullifier (step prepared)
        wanted command.declaration.parentId receipt with
    | none => .error .capabilityRejected
    | some evidence =>
      let committed ← requireSome .policyUnavailable (config.registry.resolve wanted.policyId wanted.policyRevision)
      let witness := canonicalWitness profile.compilerProfile.compiler committed (step prepared).oldState (step prepared).newState
      if inputsInRange profile.compilerProfile.compiler committed.record.predicate witness.oldState witness.newState != true then
        throw .policyInputRange
      if !decide (castInjOn F (intsOf committed.record.predicate witness.oldState witness.newState)) then
        throw .policyCastAlias
      let epochExact : wanted.policyEpoch = prepared.authority.snapshot.authState.policyEpoch wanted.policyId := by
        rw [CredentialAuthorityDomain.Snapshot.authState_policyEpoch]
        exact prepared.descent.policyCurrent
      let revisionExact : wanted.policyRevision = prepared.authority.snapshot.authState.policyRevision wanted.policyId := by
        rw [CredentialAuthorityDomain.Snapshot.authState_policyRevision]
        rfl
      match admitted : CanonicalPolicyAdmission.admit config prepared.authority.snapshot.authState wanted evidence witness
          (.policy wanted.policyId wanted.policyRevision) epochExact revisionExact with
      | none => .error .policyRejected
      | some authorization =>
        .ok ⟨authorization, by
          have unchanged := CanonicalPolicyAdmission.admit_preserves_evidence config prepared.authority.snapshot.authState
            wanted evidence witness (.policy wanted.policyId wanted.policyRevision) epochExact revisionExact admitted
          have named := sourceCapabilityOnlyEvidence_names_parent profile.compilerProfile prepared.authority.snapshot
            (sourceStore prepared) command.declaration.operationNullifier (step prepared)
            wanted command.declaration.parentId receipt supplied
          obtain ⟨parent, parentExact, evidenceExact⟩ := named
          have parentSame : parent = prepared.parent := Option.some.inj (parentExact.symm.trans prepared.descent.parentExact)
          subst parent
          rw [unchanged]
          exact evidenceExact⟩

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command) (envelope : List UInt8) :
    IO (Except Reject (Accepted prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      command.declaration.operationNullifier (request prepared.authority.snapshot profile.semantics ambient command) envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
    if same : receipt.envelopeBytes = envelope then
      match authorize prepared receipt with
      | .error reason => return .error reason
      | .ok authorization => return .ok ⟨receipt, same, authorization.val, authorization.property⟩
    else return .error .parentSubstitution

def Accepted.evidence [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    (tuple prepared).AdmissionEvidence (fun _ => portal prepared) where
  modes _ := mode prepared accepted.authorization accepted.parentNamed
  authorizations _ := reindexAuthorization prepared.authority.snapshot.authStateExact.symm
    accepted.authorization
  disclosure _ := .sealed
  disclosureAllowed _ := trivial

def Accepted.declaration [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (_accepted : Accepted prepared envelope) :=
  (tuple prepared).toDeclaration (fun _ => portal prepared)
    (effectsDigest prepared.authority.snapshot.domain profile.semantics command command.declaration)

def Accepted.legs [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) : accepted.declaration.AcceptedLegs :=
  (tuple prepared).accept (fun _ => portal prepared)
    (effectsDigest prepared.authority.snapshot.domain profile.semantics command command.declaration) accepted.evidence

theorem Accepted.post_exact [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    (accepted.declaration.post accepted.legs ()).logical = prepared.authorityPost.logical :=
  congrArg Materialized.logical
    ((tuple prepared).accepted_posts_exact (fun _ => portal prepared)
      (effectsDigest prepared.authority.snapshot.domain profile.semantics command command.declaration) accepted.evidence ())

theorem Accepted.child_lineage [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    LineageValid (parentage prepared.authority.snapshot command)
      (child prepared.authority.snapshot profile.semantics ambient command prepared.parent) :=
  (mode prepared accepted.authorization accepted.parentNamed).childLineageValid

theorem Accepted.parent_authorized [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    accepted.authorization.evidence.capabilityValue =
      some (prepared.parent.head, storedCapabilityDigest prepared.authority.snapshot prepared.parent) :=
  accepted.parentNamed

/-- The selected current policy evaluated the scoped view of the actual old
and source-computed authority states. The physical receiver proves this same post image
is installed; no caller-selected predicate state appears in either statement. -/
theorem Accepted.policy_evaluated_actual_post [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    ∃ committed,
      (policyConfig prepared).registry.resolve command.declaration.child.policyId
        (prepared.authority.snapshot.authState.policyRevision command.declaration.child.policyId) = some committed ∧
      Minidregg.Pred.eval committed.record.predicate
        (project prepared () (fun _ => prepared.authority.snapshot.logical))
        (project prepared () (fun _ => prepared.authorityPost.logical)) = true := by
  let authorization : CanonicalAuthorized (policyConfig prepared) prepared.authority.snapshot.authState
      (request prepared.authority.snapshot profile.semantics ambient command) := by
    simpa only [portal] using accepted.authorization
  have verified := authorization.policyVerified
  change (decide (_ = authorization.policyWitness.address) &&
    (policyConfig prepared).verifies
      (request prepared.authority.snapshot profile.semantics ambient command)
      authorization.policyWitness) = true at verified
  have sound := canonical_context_verifies_sound (config := policyConfig prepared)
    (step prepared) rfl (Bool.and_eq_true_iff.mp verified).2
  obtain ⟨committed, resolved, evaluated⟩ := sound.2.2.2
  refine ⟨committed, ?_, evaluated⟩
  rw [CredentialAuthorityDomain.Snapshot.authState_policyRevision]
  exact resolved

/-- info: 'Minidregg.Kernel.CapabilityDelegationController.project_noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms project_noninterference

end Minidregg.Kernel.CapabilityDelegationController
