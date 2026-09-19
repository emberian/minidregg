/- Source-owned finite resource transaction preparation. Scalar and typed content
operations share one command, exact old directory and authority snapshot, one
nullifier, one candidate tuple and one durable publication. No wire variant
contains a proposed post, raw patch, policy decision, or authority snapshot. -/
import Kernel.DeclaredResourceScalar
import Kernel.ContentResource

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev PageCell := DeclaredResourceScalar.PageCell
abbrev AuthoritySnapshot := CredentialAuthorityDomain.Snapshot
abbrev Ambient := DeclaredResourceScalar.Ambient

inductive Payload where
  | scalar (actions : List DeclaredActionLowering.Action)
  | content (command : ContentResource.Command)
  deriving DecidableEq, Repr

structure Target where
  kind : ResourceKind
  target : Nat
  capability : CapabilityId
  /-- Action declaration version, independent of the physical page schema epoch. -/
  schemaVersion : Nat
  expectedTargetRoot : Digest
  payload : Payload
  /-- Current observation authority for any value exposed to another resource law. -/
  observeCapability : Option CapabilityId := none
  deriving DecidableEq, Repr

structure Command where
  subject : SubjectId
  expectedAuthorityRoot : Digest
  nonce : Nat
  targets : List Target
  deriving DecidableEq, Repr

def Command.TargetsValid (command : Command) : Prop :=
  command.targets ≠ [] ∧ (command.targets.map Target.target).Nodup

instance targetsValidDecidable (command : Command) : Decidable command.TargetsValid := by
  unfold Command.TargetsValid
  infer_instance

def Command.targetsWellFormed (command : Command) : Bool := decide command.TargetsValid

/-- Foreign resource laws receive a participant's state only after actual
observation admission; single-target blind mutation has no foreign observer. -/
def Command.requiresObservation (command : Command) : Bool := decide (1 < command.targets.length)

@[simp] theorem Command.targetsWellFormed_iff (command : Command) :
    command.targetsWellFormed = true ↔ command.TargetsValid := by
  simp [targetsWellFormed]

def payloadStream : StreamCodec Payload :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.list DeclaredResourceScalar.actionStream) ContentResource.commandStream)
    (fun payload => match payload with | .scalar actions => .inl actions | .content command => .inr command)
    (fun payload => match payload with | .inl actions => .scalar actions | .inr command => .content command)
    (by intro payload; cases payload <;> rfl)

def targetStream : StreamCodec Target :=
  StreamCodec.xmap
    (StreamCodec.product ResourceBirthCodec.resourceKindStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
          (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream
            (StreamCodec.product payloadStream (StreamCodec.option CredentialAuthorityEntryCodec.capabilityIdStream)))))))
    (fun target => (target.kind, target.target, target.capability, target.schemaVersion,
      target.expectedTargetRoot, target.payload, target.observeCapability))
    (fun (kind, target, capability, version, root, payload, observe) =>
      ⟨kind, target, capability, version, root, payload, observe⟩)
    (by intro target; cases target; rfl)

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat (StreamCodec.list targetStream))))
    (fun command => (command.subject, command.expectedAuthorityRoot, command.nonce, command.targets))
    (fun (subject, authority, nonce, targets) => ⟨subject, authority, nonce, targets⟩)
    (by intro command; cases command; rfl)

def commandFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [3]

def rawCommandCodec : LawfulCodec Command where
  encode command := commandFrame ++ commandStream.encode command
  decode bytes := if bytes.take commandFrame.length = commandFrame then
    commandStream.toLawful.decode (bytes.drop commandFrame.length) else none
  decode_encode := by
    intro command
    have exact := commandStream.toLawful.decode_encode command
    change commandStream.toLawful.decode (commandStream.encode command) = some command at exact
    simp [exact]

def commandCodec : LawfulCodec Command := ResourceBirthCodec.strictCodec rawCommandCodec

@[simp] theorem command_decode_encode (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command := commandCodec.decode_encode command

theorem command_decode_canonical {bytes : List UInt8} {command : Command}
    (decoded : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCommandCodec decoded

/-- Empty lists never reach preparation; the default merely makes this total. -/
def Command.first (command : Command) : Target :=
  command.targets.headD ⟨.object, 0, ⟨0⟩, 1, ⟨0⟩, .scalar [], none⟩

def commandBytes (domain semantics : Digest) (command : Command) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
    (domain, semantics, commandCodec.encode command)

def argsDigest (domain semantics : Digest) (command : Command) : Digest :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.TRANSACTION.ARGS/v3".toUTF8.toList
    (commandBytes domain semantics command)).digest

def effectsDigest (domain semantics : Digest) (command : Command) : Digest :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.TRANSACTION.EFFECT/v3".toUTF8.toList
    (commandBytes domain semantics command)).digest

/-- Subject+nonce is the operation identity. Different payloads under that
identity conflict; they do not obtain a new marker by changing a target. -/
def operationMarker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.TRANSACTION.IDENTITY/v3".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream StreamCodec.nat))).encode
      (domain, semantics, command.subject, command.nonce))).digest.value

abbrev ordinaryVerb := DeclaredResourceScalar.ordinaryVerb

def requestFor (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) (preRoot : Digest) : Request target.kind where
  domain := snapshot.domain
  semantics := semantics
  federation := ambient.federation
  subject := command.subject
  subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
  target := ⟨target.target⟩
  verb := ordinaryVerb target.kind
  argsDigest := argsDigest snapshot.domain semantics command
  effectsDigest := effectsDigest snapshot.domain semantics command
  nonce := command.nonce
  height := ambient.height
  preStateRoot := preRoot
  policyId := ⟨target.target⟩
  policyEpoch := snapshot.authState.policyEpoch ⟨target.target⟩
  policyRevision := snapshot.authState.policyRevision ⟨target.target⟩
  cost := (commandCodec.encode command).length

def request (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (preRoot : Digest) : Request command.first.kind :=
  requestFor snapshot semantics ambient command command.first preRoot

inductive Reject where
  | malformedCommand | emptyTargets | duplicateTargets | emptyActions | unsupportedVersion
  | missingTarget | wrongRole | invalidPage | staleTarget | staleAuthority
  | scalar (reason : DeclaredResourceScalar.Reject)
  | content (reason : ContentResource.Reject)
  | pageValidation | invalidPost | authorityUnavailable | directoryUnavailable
  | nullifierUsed | authorityPreparation | physicalPreparation | policyUnavailable
  | signature (reason : CredentialSignatureAdmission.Reject)
  | capabilityRejected | policyRejected | policyInputRange | policyCastAlias | conflictingIncidences
  | wrongEnvelopeCount
  | observationRequired | observationRejected
  deriving Repr

def requireSome {α : Type} (reason : Reject) : Option α → Except Reject α
  | none => .error reason | some value => .ok value

def Target.schema (target : Target) : Schema.{0, 0, 0, 0} := match target.payload with
  | .scalar _ => DeclaredEffectPageMaterializer.schema
  | .content _ => HyperdocumentContentPageMaterializer.schema

instance targetFieldEq (target : Target) : DecidableEq target.schema.Field := by
  unfold Target.schema
  split <;> infer_instance
instance targetResourceEq (target : Target) : DecidableEq target.schema.Resource := by
  unfold Target.schema
  split <;> infer_instance

def Target.materializer (target : Target) : Materializer target.schema Digest := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact DeclaredEffectPageMaterializer.materializer
    | content _ => exact HyperdocumentContentPageMaterializer.materializer

abbrev TargetCell (target : Target) := Materialized target.materializer

def Target.Outcome (target : Target) : Type := match target.payload with
  | .scalar _ => DeclaredEffectPageMaterializer.Page
  | .content _ => HyperdocumentContentPageMaterializer.Page

def Target.outcomeCodec (target : Target) : LawfulCodec target.Outcome := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact DeclaredEffectPageMaterializer.pageStream.toLawful
    | content _ => exact HyperdocumentContentPageMaterializer.pageStream.toLawful

def packTarget (target : Target) (cell : TargetCell target) : PackedCell Registry := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact DeclaredResourceScalar.packDeclared kind cell
    | content _ => exact ⟨.content, cell⟩

def selectTarget (deployment : Deployment) (target : Target) (cell : PackedCell Registry) :
    Option (TargetCell target) := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact CanonicalCellRegistry.selectDeclared deployment id kind cell
    | content _ => exact if kind = .object then
        if CanonicalCellRegistry.CellLaw deployment id cell then
          match cell with | ⟨.content, value⟩ => some value | _ => none
        else none
      else none

def scalarCommand (command : Command) (target : Target)
    (actions : List DeclaredActionLowering.Action) : DeclaredResourceScalar.Command :=
  ⟨target.kind, target.target, command.subject, target.capability,
    command.expectedAuthorityRoot, target.schemaVersion, target.expectedTargetRoot, command.nonce, actions⟩

def contentAuthor (command : Command) (target : Target) : Hyperdocument.PrincipalRef :=
  ⟨command.subject, target.kind, target.capability⟩

def contentOperation (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) :
    Hyperdocument.OperationId := ⟨effectsDigest snapshot.domain semantics command⟩

/-- The only target computation. It invokes source-owned typed operations,
never a host supplied post. Every branch returns a real source outcome. -/
def computeTarget (deployment : Deployment) (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (command : Command) (target : Target)
    (pre : TargetCell target) : Except Reject target.Outcome := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar actions =>
      let projected := scalarCommand command ⟨kind, id, capability, version, root, .scalar actions, observe⟩ actions
      exact match DeclaredResourceScalar.preparePage deployment snapshot semantics ambient pre projected with
        | .error reason => .error (.scalar reason)
        | .ok prepared => .ok prepared.post
    | content content => exact do
        if kind != .object then throw .wrongRole
        if version != ContentResource.commandVersion then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        let before ← requireSome .invalidPage (HyperdocumentContentPageMaterializer.pageAt pre.logical)
        match ContentResource.preparePage ⟨command.subject, kind, capability⟩
            (contentOperation snapshot semantics command) before content with
        | .error reason => .error (.content reason)
        | .ok prepared => .ok prepared.post

def targetPatch (target : Target) (pre : TargetCell target) (post : target.Outcome) :
    Patch target.schema Digest := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact DeclaredResourceScalar.pagePatch pre post
    | content _ => exact ContentResource.patch pre post

/-- One declaration is the complete transaction, fixed by the receiving plan.
The family outcome is the actual typed result; mode evidence certifies the
exact command-to-result computation independently of policy authority. -/
def targetFamily (deployment : Deployment) (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (command : Command) (target : Target)
    (pre : TargetCell target) : SemanticEffectFamily target.schema target.materializer Nat where
  Declaration := Unit
  declarationCodec := DeclaredActionLowering.unitCodec
  pre := pre
  request := fun _ => ⟨target.kind, requestFor snapshot semantics ambient command target pre.root⟩
  Outcome := fun _ => target.Outcome
  outcomeCodec := fun _ => target.outcomeCodec
  ModeEvidence := fun _ post => PLift (computeTarget deployment snapshot semantics ambient command target pre = .ok post)
  Postcondition := fun _ post logical =>
    (targetPatch target pre post).ResultAt pre.logical logical
  effectDigest := fun _ => effectsDigest snapshot.domain semantics command
  patch := fun _ post => targetPatch target pre post
  nullifier := fun _ _ => none
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ decision => decision = .sealed

structure PreparedTarget (deployment : Deployment) (directory : Directory Nat Registry)
    (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) where
  private mk ::
  before : PackedCell Registry
  present : directory.slots target.target = .present before
  pre : TargetCell target
  selected : selectTarget deployment target before = some pre
  post : target.Outcome
  candidate : PolicyInstall.Candidate (targetFamily deployment snapshot semantics ambient command target pre)
    pre () post
  postLaw : CanonicalCellRegistry.FinalPostLaw deployment target.target before (packTarget target candidate.post)
  source : CanonicalCellRegistry.LoadedPolicySource snapshot.domain directory
    (snapshot.authState.policyAddress ⟨target.target⟩ (snapshot.authState.policyRevision ⟨target.target⟩))

def prepareTarget (deployment : Deployment) (directory : Directory Nat Registry)
    (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) :
    Except Reject (PreparedTarget deployment directory snapshot semantics ambient command target) := do
  match present : directory.slots target.target with
  | .absent => .error .missingTarget
  | .present before =>
    match selected : selectTarget deployment target before with
    | none => .error .wrongRole
    | some pre =>
      match computed : computeTarget deployment snapshot semantics ambient command target pre with
      | .error reason => .error reason
      | .ok post =>
        match validate target.materializer pre (targetPatch target pre post) with
        | .rejected _ => .error .pageValidation
        | .accepted validated =>
          let candidate : PolicyInstall.Candidate
              (targetFamily deployment snapshot semantics ambient command target pre) pre () post :=
            ⟨rfl, ⟨computed⟩, validated, validated.resultAt⟩
          if postLaw : CanonicalCellRegistry.FinalPostLaw deployment target.target before
              (packTarget target candidate.post) then
            let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
              snapshot.domain directory (snapshot.authState.policyAddress ⟨target.target⟩
                (snapshot.authState.policyRevision ⟨target.target⟩)))
            .ok ⟨before, present, pre, selected, post, candidate, postLaw, source⟩
          else .error .invalidPost

/-- Traverse a finite dependent family without dropping an incidence or
replacing a refused element with an unchecked default. -/
def collect {α : Type} {E : Type} {P : α → Type} :
    (values : List α) → ((value : α) → Except E (P value)) →
      Except E ((i : Fin values.length) → P values[i])
  | [], _ => .ok (fun i => nomatch i)
  | head :: tail, f => do
      let first ← f head
      let rest ← collect tail f
      pure fun i => Fin.cases first (fun j => rest j) i

abbrev TargetIndex (command : Command) := Fin command.targets.length
abbrev Incidence (command : Command) := Option (TargetIndex command)

def incidences (command : Command) : List (Incidence command) :=
  (List.finRange command.targets.length).map some ++ [none]

def markerEdits (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) :
    List CredentialAuthorityDomain.Edit :=
  [CredentialAuthorityDomain.nullifierEdit snapshot (operationMarker snapshot.domain semantics command)]

def markerPatch (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) :
    Patch CredentialAuthorityState.schema.{0, 0} Digest :=
  CredentialAuthorityDomain.editPatch snapshot (markerEdits snapshot semantics command)

structure MarkerMode (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) where
  rootExact : command.expectedAuthorityRoot = snapshot.cell.root
  unused : CredentialAuthorityState.isNullified snapshot.cell
    (operationMarker snapshot.domain semantics command) = false
  prepared : CredentialAuthorityDomain.Prepared snapshot (markerEdits snapshot semantics command)

def markerFamily (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) :
    SemanticEffectFamily CredentialAuthorityState.schema.{0, 0}
      CredentialAuthorityStateCodec.materializer Nat where
  Declaration := Command
  declarationCodec := commandCodec
  pre := snapshot.cell
  request := fun command => ⟨command.first.kind, request snapshot semantics ambient command snapshot.cell.root⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => DeclaredActionLowering.unitCodec
  ModeEvidence := fun command _ => MarkerMode snapshot semantics command
  Postcondition := fun command _ logical =>
    (markerPatch snapshot semantics command).ResultAt snapshot.logical logical
  effectDigest := effectsDigest snapshot.domain semantics
  patch := fun command _ => markerPatch snapshot semantics command
  nullifier := fun command _ => some (operationMarker snapshot.domain semantics command)
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ decision => decision = .sealed

def prepareMarker (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) :
    Except Reject (MarkerMode snapshot semantics command) :=
  if root : command.expectedAuthorityRoot = snapshot.cell.root then
    if unused : CredentialAuthorityState.isNullified snapshot.cell
        (operationMarker snapshot.domain semantics command) = false then
      match CredentialAuthorityDomain.prepare snapshot (markerEdits snapshot semantics command) with
      | none => .error .authorityPreparation
      | some prepared => .ok ⟨root, unused, prepared⟩
    else .error .nullifierUsed
  else .error .staleAuthority

def sourceStore (domain : Digest) (directory : Directory Nat Registry) :
    CanonicalPolicyRegistry.PayloadStore where
  fetch := CanonicalCellRegistry.fetchPolicySource domain directory

structure PreparedInvocation {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) where
  private mk ::
  nonempty : command.targets ≠ []
  distinct : (command.targets.map Target.target).Nodup
  directory : LoadedDirectory durable
  authority : Loaded deployment.authorityAnchor durable.snapshot
  targets : (i : TargetIndex command) → PreparedTarget deployment directory.directory
    authority.snapshot profile.semantics ambient command command.targets[i]
  marker : MarkerMode authority.snapshot profile.semantics command
  physical : Lowered directory authority (markerEdits authority.snapshot profile.semantics command)
    marker.prepared []

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient)
    (durable : Durable) (command : Command) :
    Except Reject (PreparedInvocation deployment profile ambient durable command) := do
  if nonempty : command.targets ≠ [] then
    if distinct : (command.targets.map Target.target).Nodup then
      let directory ← requireSome .directoryUnavailable (loadDirectory durable)
      let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
      let targets ← collect command.targets (prepareTarget deployment directory.directory
        authority.snapshot profile.semantics ambient command)
      let marker ← prepareMarker authority.snapshot profile.semantics command
      let physical ← requireSome .physicalPreparation (lower directory authority marker.prepared [])
      .ok ⟨nonempty, distinct, directory, authority, targets, marker, physical⟩
    else .error .duplicateTargets
  else .error .emptyTargets

end Minidregg.Kernel.DeclaredResourceController
