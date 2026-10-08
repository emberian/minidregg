/-
# Source-authorized revocation in the canonical resource world

Revocation uses the resource's existing policy-control grant, checked against
its CURRENT policy. The victim must be a stored grant for that same resource.
The source derives a single revocation/nullifier patch from one complete old
authority snapshot; neither a signature alone nor resource ownership bypasses
the policy. Descendant admission consults this same canonical revocation plane.
-/
import Kernel.DeclaredResourceController
import Theory.CredentialAuthorityEffects
import Compiler.ResourceTargetAdmission
import Compiler.ResourceAuthorityProjection
import Compiler.ServedBasis

namespace Minidregg.Kernel.CapabilityRevocationController

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.Store (Store)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Ground := ServedBasis.Ground
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer

structure Command (kind : ResourceKind) where
  subject : SubjectId
  nonce : Nat
  target : ResourceId kind
  victimKind : ResourceKind
  capability : CapabilityId
  controlCapability : CapabilityId
  expectedTargetRoot : Digest
  expectedAuthorityRoot : Digest
  deriving DecidableEq, Repr

abbrev CommandWire (kind : ResourceKind) := SubjectId × Nat × ResourceId kind ×
  ResourceKind × CapabilityId × CapabilityId × Digest × Digest

def commandWireStream (kind : ResourceKind) : StreamCodec (CommandWire kind) :=
  StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (TypedAuthorizationRequestCodec.resourceIdStream kind)
        (StreamCodec.product ResourceBirthCodec.resourceKindStream
          (StreamCodec.product capabilityIdStream
            (StreamCodec.product capabilityIdStream
              (StreamCodec.product digestStream digestStream))))))

def commandStream (kind : ResourceKind) : StreamCodec (Command kind) :=
  StreamCodec.xmap (commandWireStream kind)
    (fun command => (command.subject, command.nonce, command.target, command.victimKind, command.capability,
      command.controlCapability, command.expectedTargetRoot, command.expectedAuthorityRoot))
    (fun (subject, nonce, target, victimKind, capability, control, targetRoot, authorityRoot) =>
      ⟨subject, nonce, target, victimKind, capability, control, targetRoot, authorityRoot⟩)
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
    | mk kind command => simp [List.append_assoc, StreamCodec.decodePrefix_encode]

def commandFrame : List UInt8 := "DREGG/CAPABILITY/REVOKE".toUTF8.toList ++ [1]

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

/-- Same caller/resource/nonce is one operation even if its victim, authority,
root or signature changes. The retained exact ingress rejects such substitution. -/
def operationMarker {kind : ResourceKind} (domain semantics : Digest) (command : Command kind) : Nat :=
  (Sp800185Cshake256.hash "DREGG.CAPABILITY.REVOKE.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product ResourceBirthCodec.resourceKindStream
          (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
            (StreamCodec.product StreamCodec.nat StreamCodec.nat))))).encode
      (domain, semantics, kind, command.subject, command.target.value, command.nonce))).digest.value

def declaration {kind : ResourceKind} (domain semantics : Digest) (command : Command kind) : RevokeDeclaration :=
  ⟨.capability command.capability, command.expectedAuthorityRoot, operationMarker domain semantics command⟩

def declarationStream : StreamCodec RevokeDeclaration :=
  StreamCodec.xmap
    (StreamCodec.product CredentialAuthorityCell.revocationKeyStream
      (StreamCodec.product digestStream StreamCodec.nat))
    (fun declaration => (declaration.key, declaration.expectedPreRoot, declaration.operationNullifier))
    (fun (key, root, marker) => ⟨key, root, marker⟩)
    (by intro declaration; cases declaration; rfl)

def declarationCodec : LawfulCodec RevokeDeclaration :=
  ResourceBirthCodec.strictCodec declarationStream.toLawful

def commandBytes {kind : ResourceKind} (domain semantics : Digest) (command : Command kind) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
    (domain, semantics, commandCodec.encode ⟨kind, command⟩)

def effectsDigest {kind : ResourceKind} (domain semantics : Digest) (command : Command kind)
    (declaration : RevokeDeclaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.CAPABILITY.REVOKE.EFFECT/v1".toUTF8.toList
    (commandBytes domain semantics command ++ declarationCodec.encode declaration)).digest

structure Ambient where
  federation : FederationId
  height : Height

/-- Policy-control authority is deliberately governed by the resource's own
current policy. `authority/operation/revoke` additionally distinguishes the
operation in the source-derived predicate view. -/
def context {kind : ResourceKind} (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command kind) : RequestContext where
  authority :=
    { kind := .program
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.subject
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
      target := ⟨command.target.value⟩
      verb := .revokeCapability
      nonce := operationMarker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨command.target.value⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨command.target.value⟩
      policyRevision := snapshot.authState.policyRevision ⟨command.target.value⟩
      cost := (commandCodec.encode ⟨kind, command⟩).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.CAPABILITY.REVOKE.ARGS/v1".toUTF8.toList
      (commandBytes snapshot.domain semantics command ++ bytes)).digest

def request {kind : ResourceKind} (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command kind) : Request .program :=
  ((context snapshot semantics ambient command).request declarationCodec
    (effectsDigest snapshot.domain semantics command) snapshot.cell.root
    (operationMarker snapshot.domain semantics command)
    (declaration snapshot.domain semantics command)).2

inductive Reject where
  | malformedCommand | directoryUnavailable | authorityUnavailable | targetUnavailable
  | staleAuthority | victimUnavailable | unregisteredVictim | victimPolicy | alreadyRevoked | replayedMarker
  | validation | physicalPreparation
  /-- The request did not declare the operation marker's replay nullifier, so its
  ground has no answer for it (`ServedBasis.Ground.markerSpent`): refused, never
  read as unspent. -/
  | undeclaredMarker
  /-- The request did not declare the revocation's transaction id, so its ground
  has no journal answer for it (`ServedBasis.Ground.replayOf`): refused, never read
  as "not recorded". -/
  | undeclaredTransaction
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

abbrev ObservedTarget (deployment : Deployment) (directory : Directory Nat Registry)
    {kind : ResourceKind} (command : Command kind) :=
  ResourceTargetAdmission.Observed deployment directory kind command.target.value command.expectedTargetRoot

def observeTarget (deployment : Deployment) (directory : Directory Nat Registry)
    {kind : ResourceKind} (command : Command kind) : Option (ObservedTarget deployment directory command) :=
  ResourceTargetAdmission.observe deployment directory kind command.target.value command.expectedTargetRoot

def family {kind : ResourceKind} (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command kind) :=
  revokeFamily snapshot.cell declarationCodec
    (effectsDigest snapshot.domain semantics command) (context snapshot semantics ambient command)

/-- A prepared revocation over the directory and authority snapshot it read. -/
structure PreparedOn {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (directory : Directory Nat Registry)
    (authority : Snapshot) {kind : ResourceKind} (command : Command kind) where
  private mk ::
  target : ObservedTarget deployment directory command
  victim : StoredCapability command.victimKind
  victimExact : readCapability authority.cell command.victimKind command.capability = some victim
  victimIdentity : victim.head.id = command.capability
  victimPolicy : victim.head.policyId = ⟨command.target.value⟩
  candidate : Candidate (family authority profile.semantics ambient command)
    authority.cell (declaration authority.domain profile.semantics command) ()
  source : CanonicalCellRegistry.LoadedPolicySource authority.domain directory
    (authority.authState.policyAddress ⟨command.target.value⟩
      (authority.authState.policyRevision ⟨command.target.value⟩))

/-- The preparation over what it reads: the directory, the authority snapshot and
the operation marker's spent answer (`none`: not declared by the request). -/
def prepareOn {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (directory : Directory Nat Registry)
    (authority : Snapshot) (markerSpent : Option Bool) {kind : ResourceKind} (command : Command kind) :
    Except Reject (PreparedOn deployment profile ambient directory authority command) := do
  let target ← requireSome .targetUnavailable (observeTarget deployment directory command)
  match victimExact : readCapability authority.cell command.victimKind command.capability with
  | none => .error .victimUnavailable
  | some victim =>
    if victimIdentity : victim.head.id = command.capability then
     if victimPolicy : victim.head.policyId = ⟨command.target.value⟩ then
      if rootExact : command.expectedAuthorityRoot = authority.cell.root then
        if registered : isRegistered authority.cell (.capability command.capability) = true then
          if live : isRevoked authority.cell (.capability command.capability) = false then
            match markerSpent with
            | none => .error .undeclaredMarker
            | some true => .error .replayedMarker
            | some false =>
              match validate AuthorityMaterializer authority.cell authority.cell.root
                  ((declaration authority.domain profile.semantics command).patch
                    authority.logical) with
              | .rejected _ => .error .validation
              | .accepted validated =>
                  let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                    authority.domain directory
                    (authority.authState.policyAddress ⟨command.target.value⟩
                      (authority.authState.policyRevision ⟨command.target.value⟩)))
                  .ok ⟨target, victim, victimExact, victimIdentity, victimPolicy,
                    { preStateBound := rfl
                      modeEvidence := ⟨rootExact, registered, live⟩
                      validated := validated
                      postcondition := validated.resultAt },
                    source⟩
          else .error .alreadyRevoked
        else .error .unregisteredVictim
      else .error .staleAuthority
     else .error .victimPolicy
    else .error .victimUnavailable

/-- A prepared revocation over a ground (`ServedBasis.Ground`): the light route's
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

/-- **The revocation is prepared alike on any two grounds that read alike**: the
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

/-- With no answer for the marker, the preparation never succeeds. -/
theorem prepareOn_unanswered {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (directory : Directory Nat Registry)
    (authority : Snapshot) {kind : ResourceKind} (command : Command kind) :
    ∀ prepared, prepareOn deployment profile ambient directory authority none command ≠ .ok prepared := by
  intro prepared accepted
  unfold prepareOn at accepted
  cases target : observeTarget deployment directory command with
  | none => simp [requireSome, target, bind, Except.bind] at accepted
  | some observed =>
      simp only [requireSome, target, bind, Except.bind] at accepted
      split at accepted
      · cases accepted
      · repeat' split at accepted
        all_goals cases accepted

/-- **An undeclared marker is refused by name** (the plant's pole): a light basis
that did not declare the marker's replay nullifier never prepares the revocation
as unspent; its refusal is `undeclaredMarker` where every earlier check passed. -/
theorem prepare_undeclared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) {store : DurableHistory.StoreIdentity}
    (basis : ServedBasis.Basis deployment store) {kind : ResourceKind} (command : Command kind)
    (undeclared : CredentialAuthorityReplay.nullifier deployment.domain
        (operationMarker (ServedBasis.Ground.ofBasis basis).authority.domain profile.semantics command) ∉
          basis.keys.nullifiers) :
    ∀ prepared, prepare deployment profile ambient (ServedBasis.Ground.ofBasis basis) command ≠ .ok prepared := by
  unfold prepare
  rw [ServedBasis.Ground.markerSpent_undeclared basis _ undeclared]
  exact prepareOn_unanswered deployment profile ambient _ _ command

#assert_axioms prepare_agrees
#assert_axioms prepare_undeclared

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {ground : Ground deployment}
  {kind : ResourceKind} {command : Command kind}

/-- The authority cell after the revocation: the family's own validated patch
applied to the loaded cell. It is the one authority write. -/
def Prepared.authorityPost (prepared : Prepared deployment profile ambient ground command) :
    CredentialAuthorityDomain.Cell :=
  prepared.candidate.validated.apply

def project (prepared : Prepared deployment profile ambient ground command)
    (logical : Store CredentialAuthorityState.layout) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots ground.directory command.target.value ++
    CanonicalRuntimeProfile.requestSlots (request ground.authority profile.semantics ambient command) ++
    [("authority/operation/revoke", 1)] ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode ⟨kind, command⟩) ++
    DeclaredResourceController.bytesSlots "resource/bytes" 0 (PackedCell.bytes Registry prepared.target.before) ++
    ResourceAuthorityProjection.grantSlots "authority/victim" command.victimKind command.capability logical ++
    ResourceAuthorityProjection.grantSlots "authority/control" .program command.controlCapability logical⟩

/-- Unrelated authority fields cannot influence this resource's predicate
view. Request/header and target are fixed; only victim/control slots may vary. -/
theorem project_noninterference (prepared : Prepared deployment profile ambient ground command)
    (left right : ResourceAuthorityProjection.Authority)
    (victim : left ⟨.capability command.victimKind, command.capability⟩ =
      right ⟨.capability command.victimKind, command.capability⟩)
    (victimRevoked : left ⟨.revoked, .capability command.capability⟩ =
      right ⟨.revoked, .capability command.capability⟩)
    (control : left ⟨.capability .program, command.controlCapability⟩ =
      right ⟨.capability .program, command.controlCapability⟩)
    (controlRevoked : left ⟨.revoked, .capability command.controlCapability⟩ =
      right ⟨.revoked, .capability command.controlCapability⟩) :
    project prepared left = project prepared right := by
  unfold project
  rw [ResourceAuthorityProjection.grantSlots_noninterference _ _ _ left right victim victimRevoked,
    ResourceAuthorityProjection.grantSlots_noninterference _ _ _ left right control controlRevoked]

def step (prepared : Prepared deployment profile ambient ground command) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

def sourceStore (prepared : Prepared deployment profile ambient ground command) : CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource ground.authority.domain ground.directory⟩

/-- Management uses the same current structural roots as edits and reads. -/
def kindDependencies (prepared : Prepared deployment profile ambient ground command) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment ground.directory command.target.value

def policyConfig [DecidableEq F] (prepared : Prepared deployment profile ambient ground command) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile ground.authority
    ground.directory
    (sourceCapabilityPortal ground.authority (operationMarker ground.authority.domain profile.semantics command))
    (step prepared) command.target.value
    ((kindDependencies prepared).map (·.additional) |>.getD [])

/-- Missing kind/history dependencies refuse at both semantic and CAS boundaries. -/
def lawReadGuards (prepared : Prepared deployment profile ambient ground command) :
    Option (List (Nat × Digest)) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards ground.authority
    ground.directory profile.semantics command.target.value structural.additional
  pure (sources ++ structural.readGuards)

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient ground command) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := ground.authority.authState)
    (family ground.authority profile.semantics ambient command)
    (request ground.authority profile.semantics ambient command)
    ground.authority.cell (declaration ground.authority.domain profile.semantics command) ()

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient ground command) (envelope : List UInt8) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature ground.authority
  envelopeExact : receipt.envelopeBytes = envelope
  semantic : prepared.SemanticAccepted

def authorize [DecidableEq F] (prepared : Prepared deployment profile ambient ground command)
    (receipt : CredentialSignatureAdmission.CheckedSignature ground.authority) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request ground.authority profile.semantics ambient command
  let config := policyConfig prepared
  let _ ← requireSome .policyUnavailable (kindDependencies prepared)
  let evidence ← requireSome .capabilityRejected
    (config.capabilityEvidenceChecked wanted command.controlCapability () receipt () (fun _ => ())).toOption
  let law ← requireSome .policyUnavailable config.resolve?
  let witness := law.witness
  if inputsInRange profile.compilerProfile.compiler law.predicate
      (step prepared).oldState (step prepared).newState != true then
    throw .policyInputRange
  if !decide (castInjOn F (intsOf law.predicate (step prepared).oldState (step prepared).newState)) then
    throw .policyCastAlias
  match ComposedPolicyAdmission.admit config wanted evidence witness
      (.policy wanted.policyId wanted.policyRevision) rfl rfl with
  | none => .error .policyRejected
  | some authorization => .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient ground command) (envelope : List UInt8) :
    IO (Except Reject (Accepted prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native ground.authority
      (operationMarker ground.authority.domain profile.semantics command)
      (request ground.authority profile.semantics ambient command) envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
    if same : receipt.envelopeBytes = envelope then
      match authorize prepared receipt with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨receipt, same, accepted⟩
    else return .error .capabilityRejected

/-- Revocation is not merely logged: the actual accepted post participates in
all subsequent same-state capability checks. -/
theorem Accepted.revoked [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    RevocationKey.capability command.capability ∈
      (authState accepted.semantic.prepared.post).revoked :=
  by simpa using (revocation_post_is_authorizer_member
    (accepted.semantic.recast ground.authority.authStateExact))

theorem Accepted.rejects_victim [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) (wanted : Request command.victimKind) :
    ¬ prepared.victim.head.Admissible
      (authState accepted.semantic.prepared.post) wanted := by
  intro admitted
  apply admitted.selfNotRevoked
  rw [prepared.victimIdentity]
  exact accepted.revoked

theorem Accepted.rejects_descendant [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) {other : ResourceKind} (descendant : Capability other)
    (wanted : Request other) (ancestor : command.capability ∈ descendant.ancestors) :
    ¬ descendant.Admissible
      (authState accepted.semantic.prepared.post) wanted :=
  ancestor_revocation_rejected descendant _ wanted command.capability ancestor accepted.revoked

/-- Neither a subject signature nor a proof-only portal can replace the
actually stored management capability; its distinct revoke verb is mandatory. -/
theorem Accepted.control_capability_required [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    ∃ capability commitment,
      accepted.semantic.authorization.evidence.capabilityValue = some (capability, commitment) ∧
      Verb.revokeCapability ∈ capability.scope.verbs := by
  cases evidence : accepted.semantic.authorization.evidence with
  | signature witness epoch verified => exact witness.elim
  | proof witness verified => exact witness.elim
  | capability cap commitment commitmentWitness membershipWitness issuerWitness
      selfRevocationWitness useWitness semantic useVerified commitmentVerified
      membershipVerified issuerVerified selfVerified ancestorVerified channelVerified =>
      exact ⟨cap, commitment, rfl, (Verb.allowedBy_iff_mem rfl).mp semantic.scope.verb⟩

/-- Revocation preserves ALL grant payloads and their generation/revision
coordinates. Only the named revocation fact changes. -/
theorem Accepted.grants_preserved [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) (other : ResourceKind) (identifier : CapabilityId) :
    readCapability accepted.semantic.prepared.post other identifier =
      readCapability ground.authority.cell other identifier := by
  have frame := revoke_frame (accepted.semantic.recast ground.authority.authStateExact)
    ⟨.capability other, identifier⟩
  simp only [AcceptedCellEffect.recast_prepared] at frame
  exact frame
    (by
      intro member
      have impossible := Finset.mem_singleton.mp member
      cases impossible)

theorem Accepted.policy_generation_preserved [DecidableEq F]
    {prepared : Prepared deployment profile ambient ground command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) (policy : PolicyId) :
    policyEpochAt accepted.semantic.prepared.post policy =
      policyEpochAt ground.authority.cell policy := by
  have frame := revoke_frame (accepted.semantic.recast ground.authority.authStateExact)
    ⟨.policyEpoch, policy⟩
      (by
      intro member
      have impossible := Finset.mem_singleton.mp member
      cases impossible)
  rw [AcceptedCellEffect.recast_prepared] at frame
  exact congrArg (fun value : Option Nat => value.getD 0) frame

/-- The CURRENT resource law evaluates the scoped source-derived old/post
authority view. It may refuse its own management, including owner revocation. -/
theorem Accepted.current_policy_evaluated [DecidableEq F]
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
        (step prepared).oldState (step prepared).newState = true :=
  ComposedPolicyAdmission.authorized_effective_law (policyConfig prepared)
    (request ground.authority profile.semantics ambient command)
    accepted.semantic.authorization

/-- info: 'Minidregg.Kernel.CapabilityRevocationController.Accepted.revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.revoked

/-- info: 'Minidregg.Kernel.CapabilityRevocationController.Accepted.rejects_victim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.rejects_victim

/-- info: 'Minidregg.Kernel.CapabilityRevocationController.Accepted.rejects_descendant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.rejects_descendant

/-- info: 'Minidregg.Kernel.CapabilityRevocationController.Accepted.control_capability_required' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.control_capability_required

/-- info: 'Minidregg.Kernel.CapabilityRevocationController.Accepted.grants_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.grants_preserved

/-- info: 'Minidregg.Kernel.CapabilityRevocationController.Accepted.policy_generation_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.policy_generation_preserved

/-- info: 'Minidregg.Kernel.CapabilityRevocationController.Accepted.current_policy_evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.current_policy_evaluated

/-- info: 'Minidregg.Kernel.CapabilityRevocationController.project_noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms project_noninterference

end Minidregg.Kernel.CapabilityRevocationController
