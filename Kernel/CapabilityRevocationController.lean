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
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityStateCodec.materializer

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
    (StreamCodec.product (StreamCodec.sum capabilityIdStream channelIdStream)
      (StreamCodec.product digestStream StreamCodec.nat))
    (fun declaration => ((match declaration.key with
      | .capability key => .inl key | .channel key => .inr key),
      declaration.expectedPreRoot, declaration.operationNullifier))
    (fun (key, root, marker) => ⟨(match key with
      | .inl key => .capability key | .inr key => .channel key), root, marker⟩)
    (by intro declaration; cases declaration with | mk key root marker => cases key <;> rfl)

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

def edits {kind : ResourceKind} (snapshot : Snapshot) (semantics : Digest)
    (command : Command kind) : List CredentialAuthorityDomain.Edit :=
  [⟨snapshot.entries.find? (fun entry => match entry with
      | .revocation key _ => decide (key = .capability command.capability)
      | _ => false), .revocation (.capability command.capability) true⟩,
    CredentialAuthorityDomain.nullifierEdit snapshot (operationMarker snapshot.domain semantics command)]

inductive Reject where
  | malformedCommand | directoryUnavailable | authorityUnavailable | targetUnavailable
  | staleAuthority | victimUnavailable | victimPolicy | alreadyRevoked | replayedMarker
  | authorityPreparation | validation | refinement | physicalPreparation
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
  revokeFamily snapshot.revocationUniverse snapshot.cell declarationCodec
    (effectsDigest snapshot.domain semantics command) (context snapshot semantics ambient command)

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    {kind : ResourceKind} (command : Command kind) where
  private mk ::
  directory : LoadedDirectory durable
  authority : Loaded deployment.authorityAnchor durable.snapshot
  target : ObservedTarget deployment directory.directory command
  victim : StoredCapability command.victimKind
  victimExact : readCapability authority.snapshot.cell command.victimKind command.capability = some victim
  victimIdentity : victim.head.id = command.capability
  victimPolicy : victim.head.policyId = ⟨command.target.value⟩
  candidate : Candidate (family authority.snapshot profile.semantics ambient command)
    authority.snapshot.cell (declaration authority.snapshot.domain profile.semantics command) ()
  update : CredentialAuthorityDomain.Prepared authority.snapshot (edits authority.snapshot profile.semantics command)
  postExact : update.postLogical = candidate.validated.apply.logical
  physical : Lowered directory authority (edits authority.snapshot profile.semantics command) update []
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨command.target.value⟩
      (authority.snapshot.authState.policyRevision ⟨command.target.value⟩))

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    {kind : ResourceKind} (command : Command kind) :
    Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let target ← requireSome .targetUnavailable (observeTarget deployment directory.directory command)
  match victimExact : readCapability authority.snapshot.cell command.victimKind command.capability with
  | none => .error .victimUnavailable
  | some victim =>
    if victimIdentity : victim.head.id = command.capability then
     if victimPolicy : victim.head.policyId = ⟨command.target.value⟩ then
      if rootExact : command.expectedAuthorityRoot = authority.snapshot.cell.root then
        if registered : RevocationKey.capability command.capability ∈ authority.snapshot.revocationUniverse.revocationKeys then
          if live : isRevoked authority.snapshot.cell (.capability command.capability) = false then
            if fresh : isNullified authority.snapshot.cell (operationMarker authority.snapshot.domain profile.semantics command) = false then
              let update ← requireSome .authorityPreparation
                (CredentialAuthorityDomain.prepare authority.snapshot (edits authority.snapshot profile.semantics command))
              match validate AuthorityMaterializer authority.snapshot.cell
                  (declaration authority.snapshot.domain profile.semantics command).patch with
              | .rejected _ => .error .validation
              | .accepted validated =>
                if same : CredentialAuthorityStateCodec.encode update.postLogical =
                    CredentialAuthorityStateCodec.encode validated.apply.logical then
                  let physical ← requireSome .physicalPreparation (lower directory authority update [])
                  let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                    authority.snapshot.domain directory.directory
                    (authority.snapshot.authState.policyAddress ⟨command.target.value⟩
                      (authority.snapshot.authState.policyRevision ⟨command.target.value⟩)))
                  .ok ⟨directory, authority, target, victim, victimExact, victimIdentity, victimPolicy,
                    { preStateBound := rfl
                      modeEvidence := ⟨rootExact, registered, live, fresh⟩
                      validated := validated
                      postcondition := validated.resultAt },
                    update, CredentialAuthorityStateCodec.encode_injective same, physical, source⟩
                else .error .refinement
            else .error .replayedMarker
          else .error .alreadyRevoked
        else .error .victimUnavailable
      else .error .staleAuthority
     else .error .victimPolicy
    else .error .victimUnavailable

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {kind : ResourceKind} {command : Command kind}

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : LogicalState CredentialAuthorityState.schema.{0, 0}) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots (request prepared.authority.snapshot profile.semantics ambient command) ++
    [("authority/operation/revoke", 1)] ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode ⟨kind, command⟩) ++
    DeclaredResourceController.bytesSlots "resource/bytes" 0 (PackedCell.bytes Registry prepared.target.before) ++
    ResourceAuthorityProjection.grantSlots "authority/victim" command.victimKind command.capability logical ++
    ResourceAuthorityProjection.grantSlots "authority/control" .program command.controlCapability logical⟩

/-- Unrelated authority fields cannot influence this resource's predicate
view. Request/header and target are fixed; only victim/control slots may vary. -/
theorem project_noninterference (prepared : Prepared deployment profile ambient durable command)
    (left right : ResourceAuthorityProjection.Authority)
    (victim : left.fields (.capability command.victimKind command.capability) =
      right.fields (.capability command.victimKind command.capability))
    (victimRevoked : left.fields (.revoked (.capability command.capability)) =
      right.fields (.revoked (.capability command.capability)))
    (control : left.fields (.capability .program command.controlCapability) =
      right.fields (.capability .program command.controlCapability))
    (controlRevoked : left.fields (.revoked (.capability command.controlCapability)) =
      right.fields (.revoked (.capability command.controlCapability))) :
    project prepared left = project prepared right := by
  unfold project
  rw [ResourceAuthorityProjection.grantSlots_noninterference _ _ _ left right victim victimRevoked,
    ResourceAuthorityProjection.grantSlots_noninterference _ _ _ left right control controlRevoked]

def step (prepared : Prepared deployment profile ambient durable command) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

def sourceStore (prepared : Prepared deployment profile ambient durable command) : CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource prepared.authority.snapshot.domain prepared.directory.directory⟩

def policyConfig [DecidableEq F] (prepared : Prepared deployment profile ambient durable command) : CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile prepared.authority.snapshot (sourceStore prepared)
    (sourceCapabilityPortal prepared.authority.snapshot (operationMarker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared)

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family prepared.authority.snapshot profile.semantics ambient command)
    (request prepared.authority.snapshot profile.semantics ambient command)
    prepared.authority.snapshot.cell (declaration prepared.authority.snapshot.domain profile.semantics command) ()

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) (envelope : List UInt8) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = envelope
  semantic : prepared.SemanticAccepted

def authorize [DecidableEq F] (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request prepared.authority.snapshot profile.semantics ambient command
  let config := policyConfig prepared
  let evidence ← requireSome .capabilityRejected
    (sourceCapabilityOnlyEvidence profile.compilerProfile prepared.authority.snapshot (sourceStore prepared)
      (operationMarker prepared.authority.snapshot.domain profile.semantics command) (step prepared)
      wanted command.controlCapability receipt)
  let committed ← requireSome .policyUnavailable (config.registry.resolve wanted.policyId wanted.policyRevision)
  let witness := canonicalWitness profile.compilerProfile.compiler committed (step prepared).oldState (step prepared).newState
  if inputsInRange profile.compilerProfile.compiler committed.record.predicate witness.oldState witness.newState != true then
    throw .policyInputRange
  if !decide (castInjOn F (intsOf committed.record.predicate witness.oldState witness.newState)) then
    throw .policyCastAlias
  match CanonicalPolicyAdmission.admit config prepared.authority.snapshot.authState wanted evidence witness
      (.policy wanted.policyId wanted.policyRevision) rfl rfl with
  | none => .error .policyRejected
  | some authorization => .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command) (envelope : List UInt8) :
    IO (Except Reject (Accepted prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (operationMarker prepared.authority.snapshot.domain profile.semantics command)
      (request prepared.authority.snapshot profile.semantics ambient command) envelope with
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
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    RevocationKey.capability command.capability ∈
      (authState prepared.authority.snapshot.revocationUniverse accepted.semantic.prepared.post).revoked :=
  revocation_post_is_authorizer_member accepted.semantic

theorem Accepted.rejects_victim [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) (wanted : Request command.victimKind) :
    ¬ prepared.victim.head.Admissible
      (authState prepared.authority.snapshot.revocationUniverse accepted.semantic.prepared.post) wanted := by
  intro admitted
  apply admitted.selfNotRevoked
  rw [prepared.victimIdentity]
  exact accepted.revoked

theorem Accepted.rejects_descendant [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) {other : ResourceKind} (descendant : Capability other)
    (wanted : Request other) (ancestor : command.capability ∈ descendant.ancestors) :
    ¬ descendant.Admissible
      (authState prepared.authority.snapshot.revocationUniverse accepted.semantic.prepared.post) wanted :=
  ancestor_revocation_rejected descendant _ wanted command.capability ancestor accepted.revoked

/-- Neither a subject signature nor a proof-only portal can replace the
actually stored management capability; its distinct revoke verb is mandatory. -/
theorem Accepted.control_capability_required [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
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
      exact ⟨cap, commitment, rfl, semantic.scope.verb⟩

/-- Revocation preserves ALL grant payloads and their generation/revision
coordinates. Only the named revocation fact and the operation nullifier change. -/
theorem Accepted.grants_preserved [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) (other : ResourceKind) (identifier : CapabilityId) :
    readCapability accepted.semantic.prepared.post other identifier =
      readCapability prepared.authority.snapshot.cell other identifier := by
  exact revoke_frame.{0, 0, 0, 0} accepted.semantic (.capability other identifier)
    (by
      intro member
      rcases Finset.mem_insert.mp member with impossible | member
      · cases impossible
      · have impossible := Finset.mem_singleton.mp member
        cases impossible)

theorem Accepted.policy_generation_preserved [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) (policy : PolicyId) :
    policyEpochAt accepted.semantic.prepared.post policy =
      policyEpochAt prepared.authority.snapshot.cell policy := by
  exact congrArg (fun value : Option Nat => value.getD 0)
    (revoke_frame.{0, 0, 0, 0} accepted.semantic (.policyEpoch policy)
      (by
      intro member
      rcases Finset.mem_insert.mp member with impossible | member
      · cases impossible
      · have impossible := Finset.mem_singleton.mp member
        cases impossible))

/-- The CURRENT resource law evaluates the scoped source-derived old/post
authority view. It may refuse its own management, including owner revocation. -/
theorem Accepted.current_policy_evaluated [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {envelope : List UInt8}
    (accepted : Accepted prepared envelope) :
    ∃ committed,
      (policyConfig prepared).registry.resolve ⟨command.target.value⟩
        (prepared.authority.snapshot.authState.policyRevision ⟨command.target.value⟩) = some committed ∧
      Minidregg.Pred.eval committed.record.predicate
        (project prepared prepared.authority.snapshot.logical)
        (project prepared prepared.update.postLogical) = true := by
  have verified : (policyConfig prepared).verifies
      (request prepared.authority.snapshot profile.semantics ambient command)
      accepted.semantic.authorization.policyWitness = true :=
    (Bool.and_eq_true_iff.mp accepted.semantic.authorization.policyVerified).2
  obtain ⟨committed, resolved, evaluated⟩ :=
    (canonical_context_verifies_sound (step prepared) rfl verified).2.2.2
  refine ⟨committed, resolved, ?_⟩
  change Minidregg.Pred.eval committed.record.predicate
    (project prepared prepared.authority.snapshot.logical)
    (project prepared prepared.candidate.validated.apply.logical) = true at evaluated
  rw [← prepared.postExact] at evaluated
  exact evaluated

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
