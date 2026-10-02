/- Source-owned finite resource transaction preparation. Scalar and typed content
operations share one command, exact old directory and authority snapshot, one
nullifier, one candidate tuple and one durable publication. No wire variant
contains a proposed post, raw patch, policy decision, or authority snapshot. -/
import Kernel.DeclaredResourceScalar
import Kernel.ContentResource
import Compiler.StreamCell
import Compiler.ResourceAuthorityProjection
import Kernel.Run
import Kernel.NockDoor
import Kernel.ClockCellDomain

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
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev AuthoritySnapshot := CredentialAuthorityDomain.Snapshot
abbrev Ambient := DeclaredResourceScalar.Ambient

/-- A target's payload: declared scalar actions, a content command, or one
stream append (the entry's bytes; the receiver derives its sequence position
and digest). -/
inductive Payload where
  | scalar (actions : List DeclaredActionLowering.Action)
  | content (command : ContentResource.Command)
  | append (request : StreamCell.Append)
  deriving DecidableEq

/-- A content command shows as its canonical command bytes. -/
instance : Repr Payload where
  reprPrec payload prec := match payload with
    | .scalar actions => Repr.addAppParen ("Payload.scalar " ++ reprArg actions) prec
    | .content command =>
        Repr.addAppParen ("Payload.content " ++ reprArg (ContentResource.commandCodec.encode command)) prec
    | .append request => Repr.addAppParen ("Payload.append " ++ reprArg request) prec

structure Target where
  kind : ResourceKind
  target : Nat
  capability : CapabilityId
  /-- Action declaration version, independent of the cell's wire version. -/
  schemaVersion : Nat
  expectedTargetRoot : Digest
  payload : Payload
  /-- Current observation authority for any value exposed to another resource law. -/
  observeCapability : Option CapabilityId := none
  deriving DecidableEq, Repr

/-- A transaction names what it read per target (`expectedTargetRoot`, a whole
cell it reads) and nothing about the authority cell's root: its authority reads
are the signed header's footprint (`CredentialSignatureAdmission.footprint`,
`Theory.PlanBinding`), and every other authority check runs at admission
against the current cell.  A command bound to the authority root was refused
after any other agent's admission. -/
structure Command where
  subject : SubjectId
  nonce : Nat
  targets : List Target
  /-- A Nock run whose product these writes claim to be (NOCK §2.4). Signed with
  the command: the claim's steps are the fee its signer consents to. When
  present, every write of every target must be a field write the re-executed
  program's product names (`Kernel.Run.checkRun`). -/
  run : Option Run.RunClaim := none
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
    (StreamCodec.sum (StreamCodec.list DeclaredResourceScalar.actionStream)
      (StreamCodec.sum ContentResource.commandStream StreamCell.appendStream))
    (fun payload => match payload with
      | .scalar actions => .inl actions
      | .content command => .inr (.inl command)
      | .append request => .inr (.inr request))
    (fun payload => match payload with
      | .inl actions => .scalar actions
      | .inr (.inl command) => .content command
      | .inr (.inr request) => .append request)
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

/-- `DREGG/NOCK/RUN/v1` inside the command: program id, sample jam, output jam, steps. -/
def runClaimStream : StreamCodec Run.RunClaim :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream StreamCodec.nat)))
    (fun claim => (claim.programId, claim.sampleJam, claim.outputJam, claim.steps))
    (fun (program, sample, output, steps) => ⟨program, sample, output, steps⟩)
    (by intro claim; cases claim; rfl)

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.list targetStream) (StreamCodec.option runClaimStream))))
    (fun command => (command.subject, command.nonce, command.targets, command.run))
    (fun (subject, nonce, targets, run) => ⟨subject, nonce, targets, run⟩)
    (by intro command; cases command; rfl)

/-- Version 6: a target payload may be a stream append (K-STREAM) and a
command may carry a Nock `RunClaim` (K-RAN). Each lane bumped v4 -> v5 for a
different shape; the merged shape is ONE new version. Version-4 and version-5
commands refuse to decode. -/
def commandFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [6]

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

/-- A version-4 command frame refuses to decode. -/
theorem v4_command_refused (payload : List UInt8) :
    rawCommandCodec.decode ("DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ 4 :: payload) = none := by
  let oldFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [4]
  have lengthExact : commandFrame.length = oldFrame.length := by
    simp [commandFrame, oldFrame]
  have different : oldFrame ≠ commandFrame := by decide +kernel
  have refused : rawCommandCodec.decode (oldFrame ++ payload) = none := by
    simp [rawCommandCodec, lengthExact, different]
  simpa only [oldFrame, List.append_assoc, List.singleton_append] using refused

/-- info: 'Minidregg.Kernel.DeclaredResourceController.v4_command_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v4_command_refused

/-- A version-5 command frame (K-STREAM's or K-RAN's, two different shapes)
refuses to decode. -/
theorem v5_command_refused (payload : List UInt8) :
    rawCommandCodec.decode ("DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ 5 :: payload) = none := by
  let oldFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [5]
  have lengthExact : commandFrame.length = oldFrame.length := by
    simp [commandFrame, oldFrame]
  have different : oldFrame ≠ commandFrame := by decide +kernel
  have refused : rawCommandCodec.decode (oldFrame ++ payload) = none := by
    simp [rawCommandCodec, lengthExact, different]
  simpa only [oldFrame, List.append_assoc, List.singleton_append] using refused

/-- info: 'Minidregg.Kernel.DeclaredResourceController.v5_command_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v5_command_refused

@[simp] theorem command_decode_encode (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command := commandCodec.decode_encode command

theorem command_decode_canonical {bytes : List UInt8} {command : Command}
    (decoded : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCommandCodec decoded

/-- Empty lists never reach preparation; the default merely makes this total. -/
def Command.first (command : Command) : Target :=
  command.targets.headD ⟨.object, 0, ⟨0⟩, 1, ⟨0⟩, .scalar [], none⟩

def framedCommandBytes (domain semantics : Digest) (encodedCommand : List UInt8) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
    (domain, semantics, encodedCommand)

def commandBytes (domain semantics : Digest) (command : Command) : List UInt8 :=
  framedCommandBytes domain semantics (commandCodec.encode command)

theorem framedCommandBytes_exact (domain semantics : Digest) (command : Command) :
    framedCommandBytes domain semantics (commandCodec.encode command) =
      commandBytes domain semantics command := rfl

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

/-- The verb a target requests: `appendObject` for a stream append on an
object, the ordinary mutation verb otherwise. -/
def payloadVerb : (kind : ResourceKind) → Payload → Verb kind
  | .object, .append _ => .appendObject
  | kind, _ => ordinaryVerb kind

def Target.verb (target : Target) : Verb target.kind := payloadVerb target.kind target.payload

/-- The original expression is retained as a specification for the optimized
request construction. It is not called by the production request path. -/
def requestForReference (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) (preRoot : Digest) : Request target.kind where
  domain := snapshot.domain
  semantics := semantics
  federation := ambient.federation
  subject := command.subject
  subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
  target := ⟨target.target⟩
  verb := target.verb
  argsDigest := argsDigest snapshot.domain semantics command
  effectsDigest := effectsDigest snapshot.domain semantics command
  nonce := command.nonce
  height := ambient.height
  preStateRoot := preRoot
  policyId := ⟨target.target⟩
  policyEpoch := snapshot.authState.policyEpoch ⟨target.target⟩
  policyRevision := snapshot.authState.policyRevision ⟨target.target⟩
  cost := (commandCodec.encode command).length

/-- Encode the canonical command and its domain/profile frame once per
request. The same exact framed bytes feed both digest domains; the raw
canonical command length remains the declared request cost. -/
def requestFor (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) (preRoot : Digest) : Request target.kind :=
  let encodedCommand := commandCodec.encode command
  let framedBytes := framedCommandBytes snapshot.domain semantics encodedCommand
  { domain := snapshot.domain
    semantics := semantics
    federation := ambient.federation
    subject := command.subject
    subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
    target := ⟨target.target⟩
    verb := target.verb
    argsDigest := (Sp800185Cshake256.hash
      "DREGG.RESOURCE.TRANSACTION.ARGS/v3".toUTF8.toList framedBytes).digest
    effectsDigest := (Sp800185Cshake256.hash
      "DREGG.RESOURCE.TRANSACTION.EFFECT/v3".toUTF8.toList framedBytes).digest
    nonce := command.nonce
    height := ambient.height
    preStateRoot := preRoot
    policyId := ⟨target.target⟩
    policyEpoch := snapshot.authState.policyEpoch ⟨target.target⟩
    policyRevision := snapshot.authState.policyRevision ⟨target.target⟩
    cost := encodedCommand.length }

/-- For every old authority snapshot and transaction input, caching only the
two canonical byte strings changes no request field, digest, or cost. -/
theorem requestFor_eq_reference (snapshot : AuthoritySnapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) (target : Target) (preRoot : Digest) :
    requestFor snapshot semantics ambient command target preRoot =
      requestForReference snapshot semantics ambient command target preRoot := by
  rfl

/-- info: 'Minidregg.Kernel.DeclaredResourceController.requestFor_eq_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms requestFor_eq_reference

def request (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (preRoot : Digest) : Request command.first.kind :=
  requestFor snapshot semantics ambient command command.first preRoot

inductive Reject where
  | malformedCommand | emptyTargets | duplicateTargets | emptyActions | unsupportedVersion
  | missingTarget | wrongRole | staleTarget
  | scalar (reason : DeclaredResourceScalar.Reject)
  | content (reason : ContentResource.Reject)
  | patchValidation | invalidPost | authorityUnavailable | directoryUnavailable
  | nullifierUsed | authorityPreparation | physicalPreparation | policyUnavailable
  | signature (reason : CredentialSignatureAdmission.Reject)
  | capabilityRejected | policyRejected | policyInputRange | policyCastAlias | conflictingIncidences
  | wrongEnvelopeCount
  | observationRequired | observationRejected | clockUnavailable
  | streamTopic | streamPayload
  /-- CH-EPOCH: a channel record's append refused by the channel law, the clause named. -/
  | channel (reason : DomainEpoch.Refusal)
  /-- K-FIELDS: the leg changed a field its capability's scope does not name. -/
  | fieldNotNamed
  /-- K-FIELDS: a named field moved past a per-field bound (`maxDelta`). -/
  | maxDeltaExceeded
  | run (reason : Run.Refusal)
  deriving Repr

def requireSome {α : Type} (reason : Reject) : Option α → Except Reject α
  | none => .error reason | some value => .ok value

/-- The store layout of the target's role: a declared-effect cell for scalar
actions, a hyperdocument content cell for content commands. -/
def Target.layout (target : Target) : Layout.{0, 0, 0} := match target.payload with
  | .scalar _ => EffectDeclaration.effectLayout
  | .content _ => Hyperdocument.layout
  | .append _ => StreamCell.headLayout

def Target.materializer (target : Target) : Materializer target.layout Digest := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact DeclaredEffectCell.materializer
    | content _ => exact HyperdocumentCell.contentMaterializer
    | append _ => exact StreamCell.headMaterializer

abbrev TargetCell (target : Target) := Materialized target.materializer

/-- A target's outcome is its computed post store. -/
abbrev Target.Outcome (target : Target) : Type := Store target.layout

def Target.outcomeCodec (target : Target) : LawfulCodec target.Outcome :=
  target.materializer.codec

def packTarget (target : Target) (cell : TargetCell target) : PackedCell Registry := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact DeclaredResourceScalar.packDeclared kind cell
    | content _ => exact ⟨.content, cell⟩
    | append _ => exact ⟨.stream, cell⟩

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
    | append _ => exact if kind = .object then
        if CanonicalCellRegistry.CellLaw deployment id cell then
          match cell with | ⟨.stream, value⟩ => some value | _ => none
        else none
      else none

def scalarCommand (command : Command) (target : Target)
    (actions : List DeclaredActionLowering.Action) : DeclaredResourceScalar.Command :=
  ⟨target.kind, target.target, command.subject, target.capability,
    target.schemaVersion, target.expectedTargetRoot, command.nonce, actions⟩

def contentAuthor (command : Command) (target : Target) : Hyperdocument.PrincipalRef :=
  ⟨command.subject, target.kind, target.capability⟩

def contentOperation (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) :
    Hyperdocument.OperationId := ⟨effectsDigest snapshot.domain semantics command⟩

/-- The record an append stores: the request's entry plus the signing
subject, the admission height and the exact transaction id. -/
def streamRecord (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (request : StreamCell.Append) : StreamCell.StreamRecord :=
  ⟨command.subject, ambient.height, ⟨operationMarker snapshot.domain semantics command⟩, request.entry⟩

/-- The only target computation. It invokes source-owned typed operations,
never a host supplied post. Every branch returns the post store the source
operation computed at the loaded cell. -/
def computeTarget (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (command : Command) (target : Target)
    (pre : TargetCell target) : Except Reject target.Outcome := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar actions =>
      let projected := scalarCommand command ⟨kind, id, capability, version, root, .scalar actions, observe⟩ actions
      exact match DeclaredResourceScalar.prepareCell snapshot semantics ambient pre projected with
        | .error reason => .error (.scalar reason)
        | .ok prepared => .ok prepared.post
    | content content => exact do
        if kind != .object then throw .wrongRole
        if version != ContentResource.commandVersion then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        match ContentResource.prepareCell ⟨command.subject, kind, capability⟩
            (contentOperation snapshot semantics command) (ContentResource.documentOf id) pre content with
        | .error reason => .error (.content reason)
        | .ok prepared => .ok prepared.post.logical
    | append request => exact do
        if kind != .object then throw .wrongRole
        if version != StreamCell.commandVersion then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        if !decide (request.topic.length ≤ StreamCell.maxTopicBytes) then throw .streamTopic
        if !decide (request.payload.length ≤ StreamCell.maxPayloadBytes) then throw .streamPayload
        match DomainEpoch.admitAppend pre.logical command.subject request with
        | .error reason => throw (.channel reason)
        | .ok () => pure ()
        let some head := StreamCell.headOf pre.logical | throw .wrongRole
        -- A fleet topic's head is appended only by the fleet receiver.
        if head.binding != .room then throw .wrongRole
        pure ((StreamCell.headWriteOp head (StreamCell.appendEntry id head
          (streamRecord snapshot semantics ambient command request))).apply pre.logical)

/-- The target's one guarded patch, generated by its source operation from the
loaded store: the scalar declaration's own lowering, or the content run's patch. -/
def targetPatch (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) (pre : TargetCell target) : Patch target.layout := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar actions =>
        exact DeclaredResourceScalar.cellPatch (scalarCommand command ⟨kind, id, capability, version, root, .scalar actions, observe⟩ actions)
    | content content =>
        let computed := ContentResource.run ⟨command.subject, kind, capability⟩
          (contentOperation snapshot semantics command) (ContentResource.documentOf id)
          pre.logical content
        exact match computed with
          | .ok progress => progress.2
          | .error _ => []
    | append request =>
        exact match StreamCell.headOf pre.logical with
          | some head => [StreamCell.headWriteOp head (StreamCell.appendEntry id head
              (streamRecord snapshot semantics ambient command request))]
          | none => []

/-- The entry an append target records, at the cell `entryCellId target n`:
the loaded head's next position and tail. Scalar and content targets record none.
The head write is the target's own patch; this entry is its one fresh cell. -/
def appendedEntry (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) (pre : TargetCell target) : Option StreamCell.Entry := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact none
    | content _ => exact none
    | append request =>
        exact (StreamCell.headOf pre.logical).map fun head =>
          StreamCell.appendEntry id head (streamRecord snapshot semantics ambient command request)

/-- One declaration is the complete transaction, fixed by the receiving plan.
The family outcome is the actual typed result; mode evidence certifies the
exact command-to-result computation independently of policy authority. -/
def targetFamily (_deployment : Deployment) (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (command : Command) (target : Target)
    (pre : TargetCell target) : SemanticEffectFamily target.layout target.materializer Nat where
  Declaration := Unit
  declarationCodec := DeclaredActionLowering.unitCodec
  pre := pre
  request := fun _ => ⟨target.kind, requestFor snapshot semantics ambient command target pre.root⟩
  Outcome := fun _ => target.Outcome
  outcomeCodec := fun _ => target.outcomeCodec
  ModeEvidence := fun _ post => PLift (computeTarget snapshot semantics ambient command target pre = .ok post)
  Postcondition := fun _ _ logical =>
    (targetPatch snapshot semantics ambient command target pre).ResultAt pre.logical logical
  effectDigest := fun _ => effectsDigest snapshot.domain semantics command
  patch := fun _ _ => targetPatch snapshot semantics ambient command target pre
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
  /-- The computed outcome is exactly the validated post. -/
  postExact : candidate.post.logical = post
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
      match computed : computeTarget snapshot semantics ambient command target pre with
      | .error reason => .error reason
      | .ok post =>
        match validate target.materializer pre pre.root
            (targetPatch snapshot semantics ambient command target pre) with
        | .rejected _ => .error .patchValidation
        | .accepted validated =>
          let candidate : PolicyInstall.Candidate
              (targetFamily deployment snapshot semantics ambient command target pre) pre () post :=
            ⟨rfl, ⟨computed⟩, validated, validated.resultAt⟩
          if postExact : candidate.post.logical = post then
            if postLaw : CanonicalCellRegistry.FinalPostLaw deployment target.target before
                (packTarget target candidate.post) then
              let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                snapshot.domain directory (snapshot.authState.policyAddress ⟨target.target⟩
                  (snapshot.authState.policyRevision ⟨target.target⟩)))
              .ok ⟨before, present, pre, selected, post, candidate, postExact, postLaw, source⟩
            else .error .invalidPost
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

/-- The authority incidence reads the authority cell and writes nothing: it
carries the transaction's authorization at the authority root.  The
operation marker is consumed in the durable nullifier set by the intent
(`DeclaredResourceController.AcceptedInvocation.dataIntent`), so a field
write leaves the authority cell, its root and its bytes unchanged. -/
def authorityReadPatch : Patch CredentialAuthorityState.layout := []

structure MarkerMode (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) where
  unused : snapshot.spent (operationMarker snapshot.domain semantics command) = false
  prepared : CredentialAuthorityDomain.Prepared snapshot authorityReadPatch

def markerFamily (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) :
    SemanticEffectFamily CredentialAuthorityState.layout CredentialAuthorityCell.materializer Nat where
  Declaration := Command
  declarationCodec := commandCodec
  pre := snapshot.cell
  request := fun command => ⟨command.first.kind, request snapshot semantics ambient command snapshot.cell.root⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => DeclaredActionLowering.unitCodec
  ModeEvidence := fun command _ => MarkerMode snapshot semantics command
  Postcondition := fun _ _ logical => authorityReadPatch.ResultAt snapshot.logical logical
  effectDigest := effectsDigest snapshot.domain semantics
  patch := fun _ _ => authorityReadPatch
  nullifier := fun command _ => some (operationMarker snapshot.domain semantics command)
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ decision => decision = .sealed

def prepareMarker (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) :
    Except Reject (MarkerMode snapshot semantics command) :=
  if unused : snapshot.spent (operationMarker snapshot.domain semantics command) = false then
    match CredentialAuthorityDomain.prepare snapshot authorityReadPatch with
    | none => .error .authorityPreparation
    | some prepared => .ok ⟨unused, prepared⟩
  else .error .nullifierUsed

def sourceStore (domain : Digest) (directory : Directory Nat Registry) :
    CanonicalPolicyRegistry.PayloadStore where
  fetch := CanonicalCellRegistry.fetchPolicySource domain directory

/-! ## The run check (K-RAN, NOCK §2.4) -/

/-- The policy slots of one stream append: the entry's fields as request
slots, so a stream law can name its author (`request/subject`), its topics
(`request/topic/…`) or its addressee (`request/to`); plus the position. -/
def streamSlots (request : StreamCell.Append) (before : Store StreamCell.headLayout) :
    List (String × Int) :=
  [("request/topic/length", Int.ofNat request.topic.length),
   ("stream/sequence", Int.ofNat (StreamCell.nextSeqOf before))] ++
  Minidregg.Compiler.ResourceAuthorityProjection.bytesSlots "request/topic" 0 request.topic ++
  (match request.recipient with
    | some subject => [("request/to", Int.ofNat subject.value)]
    | none => []) ++
  (match request.ref with
    | some (cell, sequence) => [("request/ref/cell", Int.ofNat cell), ("request/ref/sequence", Int.ofNat sequence)]
    | none => [])

/-- Exact scalar/content/stream projection from the committed old and candidate
final states. Local names remain convenient; joint names expose every declared
participant without granting a view of unrelated cells. -/
def targetProjection (target : Target) (before after : Store target.layout) : List (String × Int) := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact DeclaredResourceProjection.project id before after
    | content content => exact ContentResource.project before after content
    | append request => exact streamSlots request before

/-- The participant slot a sample reads: target `i`'s projection of its loaded
pre-state (before = after = pre), so a program sees only committed values. -/
def sampleRead (command : Command) (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (i : Nat) (slot : String) : Option Int :=
  if h : i < command.targets.length then
    (⟨targetProjection command.targets[(⟨i, h⟩ : Fin _)] (pre ⟨i, h⟩) (pre ⟨i, h⟩)⟩ :
      Minidregg.Pred.State).get slot
  else none

/-- One action as a field write of the command's `i`-th target, when it is one. -/
def actionWrite (i target : Nat) : DeclaredActionLowering.Action → Option Eval.FieldWrite
  | .write (.objectField object field) _ value =>
      if object.value = target then some ⟨i, field.value, value⟩ else none
  | .create (.objectField object field) value =>
      if object.value = target then some ⟨i, field.value, value⟩ else none
  | _ => none

def targetWrites (i : Nat) (target : Target) : Option (List Eval.FieldWrite) :=
  match target.payload with
  | .scalar actions => actions.mapM (actionWrite i target.target)
  | .content _ => none
  -- A stream append is not a field write a program's output can name.
  | .append _ => none

def writesFrom : Nat → List Target → Option (List Eval.FieldWrite)
  | _, [] => some []
  | i, target :: rest => do
      let here ← targetWrites i target
      let later ← writesFrom (i + 1) rest
      pure (here ++ later)

/-- Every write the command makes, as field writes; `none` when any action is not
an own-object field write (a move, a content edit) — under a run claim that is a
write the program's output cannot name. -/
def commandWrites (command : Command) : Option (List Eval.FieldWrite) :=
  writesFrom 0 command.targets

/-- What the controller learned from a checked run: the claim, the evaluator it ran
on (registry id), the ABI fuel, and the accepted product (its bytes, count, writes). -/
structure CheckedRun where
  claim : Run.RunClaim
  evaluator : Digest
  fuel : Nat
  verdict : Run.Accepted

/-- The kernel's own context for a run: its height, the signer, no room. A
`pinned` program's sample does not read it (`NockProgramCell.contextOf`). -/
def runContext (ambient : Ambient) (command : Command) : NockProgramCell.Context :=
  ⟨ambient.height, command.subject.value, 0⟩

/-- The program's own check on its evaluator `E`: a gate re-executes on the kernel's
sample (`Run.checkRun E`); a door re-executes its poke on target 0's stored state and
event number with the evaluator's door (`Door.checkPoke E d`, E4; Nock's is N11's). An
evaluator without doors refuses a door ABI `doorUnsupported`. -/
def checkProgram (E : Evaluator) (program : NockProgramCodec.Program)
    (libraries : List NockProgramCodec.Program)
    (ambient : Ambient) (command : Command)
    (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (claim : Run.RunClaim) (writes : List Eval.FieldWrite) :
    Except Run.Refusal Run.Accepted :=
  match program.abi.door with
  | none =>
    match E.overMax (sampleRead command pre) program.abi.sample with
    | some _ => .error .fieldOverMax
    | none =>
    match E.sampleOf program.abi (runContext ambient command)
        (command.targets.map Target.target) (sampleRead command pre) with
    | none => .error .sampleUnavailable
    | some sample =>
      (Run.checkRun E.toMachine program libraries sample claim writes).map
        (Run.Verdict.erase E.toMachine)
  | some door =>
    match E.door with
    | none => .error .doorUnsupported
    | some d =>
      match Door.viewOf door (sampleRead command pre) with
      | .error e => .error e
      | .ok view =>
        (Door.checkPoke E.toMachine d program door view claim writes).map (Run.Verdict.erase E.toMachine)

/-- Load the claimed program, resolve its evaluator against the compiled-in registry
(less what the operator disabled), load its libraries (on the same evaluator), and
re-execute it against the loaded pre-states (`checkProgram`). -/
def checkClaim (disabled : List Digest) (domain : Digest) (directory : Directory Nat Registry)
    (ambient : Ambient) (command : Command)
    (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (claim : Run.RunClaim) : Except Run.Refusal CheckedRun :=
  match CanonicalCellRegistry.loadProgram domain directory claim.programId with
  | none => .error .programUnknown
  | some program =>
    match Run.resolve disabled program.evaluator with
    | .error reason => .error reason
    | .ok E => do
      let libraries ← program.abi.libraries.mapM fun library =>
        Run.require .libraryUnknown (CanonicalCellRegistry.loadProgram domain directory library)
      if !Run.librariesAgree program libraries then throw .libraryEvaluator
      let writes ← Run.require .writeNotInOutput (commandWrites command)
      let verdict ← checkProgram E program libraries ambient command pre claim writes
      pure ⟨claim, E.id, program.abi.fuel, verdict⟩

/-- No claim: nothing to check. A claim: `checkClaim`, its refusal named `run`. -/
def checkCommandRun (disabled : List Digest) (domain : Digest) (directory : Directory Nat Registry)
    (ambient : Ambient) (command : Command)
    (pre : (i : Fin command.targets.length) → Store command.targets[i].layout) :
    Except Reject (Option CheckedRun) :=
  match command.run with
  | none => .ok none
  | some claim => ((checkClaim disabled domain directory ambient command pre claim).map some).mapError .run

structure PreparedInvocation {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) where
  private mk ::
  nonempty : command.targets ≠ []
  distinct : (command.targets.map Target.target).Nodup
  directory : LoadedDirectory durable
  authority : Loaded deployment durable.snapshot
  /-- The deployment clock of the same physical snapshot; its slots enter
  every target law and its root is a read guard of the record. -/
  clock : ClockCellDomain.Loaded deployment durable.snapshot
  targets : (i : TargetIndex command) → PreparedTarget deployment directory.directory
    authority.snapshot profile.semantics ambient command command.targets[i]
  marker : MarkerMode authority.snapshot profile.semantics command
  /-- The re-executed run, when the command claims one. -/
  run : Option CheckedRun
  runChecked : checkCommandRun profile.disabledEvaluators deployment.domain directory.directory
    ambient command (fun i => (targets i).pre.logical) = .ok run

/-- `prepare` over a directory the caller already holds for this image (the
Host's `Opened.directory`), or `none` for an image whose directory does not load.
`prepare_eq_prepareFrom`: with any held directory it is `prepare`. -/
def prepareFrom {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient)
    (durable : Durable) (directory? : Option (LoadedDirectory durable)) (command : Command) :
    Except Reject (PreparedInvocation deployment profile ambient durable command) := do
  if nonempty : command.targets ≠ [] then
    if distinct : (command.targets.map Target.target).Nodup then
      let directory ← requireSome .directoryUnavailable directory?
      let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
      let clock ← requireSome .clockUnavailable (ClockCellDomain.load deployment durable.snapshot)
      let targets ← collect command.targets (prepareTarget deployment directory.directory
        authority.snapshot profile.semantics ambient command)
      let marker ← prepareMarker authority.snapshot profile.semantics command
      match checked : checkCommandRun profile.disabledEvaluators deployment.domain
          directory.directory ambient command (fun i => (targets i).pre.logical) with
      | .error reason => .error reason
      | .ok run => .ok ⟨nonempty, distinct, directory, authority, clock, targets, marker, run, checked⟩
    else .error .duplicateTargets
  else .error .emptyTargets

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient)
    (durable : Durable) (command : Command) :
    Except Reject (PreparedInvocation deployment profile ambient durable command) :=
  prepareFrom deployment profile ambient durable (loadDirectory durable) command

/-- A held directory of the image prepares exactly what `prepare` does. -/
theorem prepare_eq_prepareFrom {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient)
    (durable : Durable) (held : LoadedDirectory durable) (command : Command) :
    prepare deployment profile ambient durable command =
      prepareFrom deployment profile ambient durable (some held) command := by
  unfold prepare
  rw [LoadedDirectory.load_eq held]

/-- The authority cell after the transaction: the (empty) authority read patch
applied to the loaded cell. -/
def PreparedInvocation.authorityPost {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
    {command : Command} (prepared : PreparedInvocation deployment profile ambient durable command) :
    CredentialAuthorityDomain.Cell :=
  prepared.marker.prepared.validated.apply

/-- The transaction leaves the authority cell's logical content unchanged. -/
theorem PreparedInvocation.authorityPost_logical {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
    {command : Command} (prepared : PreparedInvocation deployment profile ambient durable command) :
    prepared.authorityPost.logical = prepared.authority.snapshot.logical := by
  simp only [PreparedInvocation.authorityPost, ValidatedPatch.apply_logical, authorityReadPatch,
    Patch.run_nil]
  rfl


/-! ## The run check is what prepared -/

theorem checkCommandRun_none {disabled : List Digest} {domain : Digest}
    {directory : Directory Nat Registry} {ambient : Ambient}
    {command : Command} {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    (unclaimed : command.run = none) :
    checkCommandRun disabled domain directory ambient command pre = .ok none := by
  unfold checkCommandRun; rw [unclaimed]

/-- What an accepted `checkProgram` ran: a gate's `checkRun` on its evaluator and the
kernel's sample, or a door's `checkPoke` with the evaluator's door on target 0's stored view. -/
def ProgramAccepted (E : Evaluator) (program : NockProgramCodec.Program)
    (libraries : List NockProgramCodec.Program)
    (ambient : Ambient) (command : Command)
    (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (claim : Run.RunClaim) (writes : List Eval.FieldWrite) (verdict : Run.Accepted) : Prop :=
  match program.abi.door with
  | none => ∃ sample v, E.sampleOf program.abi (runContext ambient command)
      (command.targets.map Target.target) (sampleRead command pre) = some sample ∧
      Run.checkRun E.toMachine program libraries sample claim writes = .ok v ∧
      Run.Verdict.erase E.toMachine v = verdict
  | some door => ∃ d view v, E.door = some d ∧
      Door.viewOf door (sampleRead command pre) = .ok view ∧
      Door.checkPoke E.toMachine d program door view claim writes = .ok v ∧
      Run.Verdict.erase E.toMachine v = verdict

theorem checkProgram_sound {E : Evaluator} {program : NockProgramCodec.Program}
    {libraries : List NockProgramCodec.Program} {ambient : Ambient} {command : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} {writes : List Eval.FieldWrite} {verdict : Run.Accepted}
    (accepted : checkProgram E program libraries ambient command pre claim writes = .ok verdict) :
    ProgramAccepted E program libraries ambient command pre claim writes verdict := by
  unfold checkProgram at accepted
  unfold ProgramAccepted
  split at accepted
  · split at accepted
    · cases accepted
    split at accepted
    · cases accepted
    · rename_i sample hsample
      cases hrun : Run.checkRun E.toMachine program libraries sample claim writes with
      | error e => rw [hrun] at accepted; cases accepted
      | ok v =>
        rw [hrun] at accepted
        cases accepted
        exact ⟨sample, v, hsample, hrun, rfl⟩
  · rename_i door _
    split at accepted
    · cases accepted
    · rename_i d hd
      split at accepted
      · cases accepted
      · rename_i view hview
        cases hpoke : Door.checkPoke E.toMachine d program door view claim writes with
        | error e => rw [hpoke] at accepted; cases accepted
        | ok v =>
          rw [hpoke] at accepted
          cases accepted
          exact ⟨d, view, v, hd, hview, hpoke, rfl⟩

/-- **`checkProgram_fieldOverMax`** (NC-2): a gate whose sample slot value lies above the slot's
declared maximum is refused by name, before any sample is built or any run. -/
theorem checkProgram_fieldOverMax {E : Evaluator} {program : NockProgramCodec.Program}
    {libraries : List NockProgramCodec.Program} {ambient : Ambient} {command : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} {writes : List Eval.FieldWrite} {slot : NockProgramCodec.SampleSlot}
    (gate : program.abi.door = none)
    (above : E.overMax (sampleRead command pre) program.abi.sample = some slot) :
    checkProgram E program libraries ambient command pre claim writes = .error .fieldOverMax := by
  unfold checkProgram
  rw [gate]
  simp only [above]

/-- **`checkClaim_sound`**: an accepted run check loaded the claimed program, resolved
its evaluator to a compiled-in, enabled entry, loaded its libraries (on that
evaluator) from the directory, and re-executed it against the loaded pre-states: a
gate on the kernel's own sample (`Run.checkRun`), a door on target 0's stored state
(`Door.checkPoke` with the evaluator's door), accepting the command's writes. -/
theorem checkClaim_sound {disabled : List Digest} {domain : Digest}
    {directory : Directory Nat Registry} {ambient : Ambient}
    {command : Command} {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} {checked : CheckedRun}
    (accepted : checkClaim disabled domain directory ambient command pre claim = .ok checked) :
    ∃ program E libraries writes,
      checked.claim = claim ∧
      CanonicalCellRegistry.loadProgram domain directory checked.claim.programId = some program ∧
      Run.resolve disabled program.evaluator = .ok E ∧ checked.evaluator = E.id ∧
      program.abi.libraries.mapM (fun library => Run.require .libraryUnknown
        (CanonicalCellRegistry.loadProgram domain directory library)) = .ok libraries ∧
      Run.librariesAgree program libraries = true ∧
      commandWrites command = some writes ∧
      checked.fuel = program.abi.fuel ∧
      ProgramAccepted E program libraries ambient command pre checked.claim writes
        checked.verdict := by
  unfold checkClaim at accepted
  cases hprog : CanonicalCellRegistry.loadProgram domain directory claim.programId with
  | none => rw [hprog] at accepted; cases accepted
  | some program =>
    rw [hprog] at accepted
    simp only at accepted
    cases hres : Run.resolve disabled program.evaluator with
    | error e => rw [hres] at accepted; cases accepted
    | ok E =>
      rw [hres] at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      cases hlibs : program.abi.libraries.mapM (fun library => Run.require .libraryUnknown
          (CanonicalCellRegistry.loadProgram domain directory library)) with
      | error e => rw [hlibs] at accepted; cases accepted
      | ok libraries =>
        rw [hlibs] at accepted
        simp only at accepted
        split at accepted
        · cases accepted
        rename_i hagree
        revert accepted
        cases hwrites : commandWrites command with
        | none => intro accepted; cases accepted
        | some writes =>
          intro accepted
          simp only [Run.require_some] at accepted
          revert accepted
          cases hrun : checkProgram E program libraries ambient command pre claim writes with
          | error e => intro accepted; cases accepted
          | ok verdict =>
            intro accepted
            simp only [Except.ok.injEq] at accepted
            subst accepted
            exact ⟨program, E, libraries, writes, rfl, hprog, hres, rfl, hlibs,
              by simpa using hagree, rfl, rfl, checkProgram_sound hrun⟩

/-- **`checkClaim_unknownEvaluator`**: a stored program whose record names an id no
compiled-in evaluator has is refused `unknownEvaluator`, before any library is loaded
or anything runs. -/
theorem checkClaim_unknownEvaluator {disabled : List Digest} {domain : Digest}
    {directory : Directory Nat Registry} {ambient : Ambient}
    {command : Command} {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} {program : NockProgramCodec.Program}
    (stored : CanonicalCellRegistry.loadProgram domain directory claim.programId = some program)
    (absent : ∀ E ∈ Evaluator.registry, E.id ≠ program.evaluator) :
    checkClaim disabled domain directory ambient command pre claim = .error .unknownEvaluator := by
  unfold checkClaim
  rw [stored]
  simp only
  rw [Run.resolve_unknown absent]

/-- **`checkCommandRun_sound`**: a checked run in a prepared invocation is the
command's own claim, accepted by `checkClaim`. -/
theorem checkCommandRun_sound {disabled : List Digest} {domain : Digest}
    {directory : Directory Nat Registry} {ambient : Ambient}
    {command : Command} {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {checked : CheckedRun}
    (accepted : checkCommandRun disabled domain directory ambient command pre = .ok (some checked)) :
    command.run = some checked.claim ∧
      checkClaim disabled domain directory ambient command pre checked.claim = .ok checked := by
  unfold checkCommandRun at accepted
  cases hclaim : command.run with
  | none => rw [hclaim] at accepted; cases accepted
  | some claim =>
    rw [hclaim] at accepted
    cases hc : checkClaim disabled domain directory ambient command pre claim with
    | error e => simp [hc, Except.map, Except.mapError] at accepted
    | ok c =>
      simp only [hc, Except.map, Except.mapError, Except.ok.injEq, Option.some.injEq] at accepted
      subst accepted
      obtain ⟨_, _, _, _, same, -⟩ := checkClaim_sound hc
      rw [same]
      exact ⟨rfl, hc⟩

/-- A claim is never dropped: a command that claims a run is either refused
with the claim's `run` refusal, or carries the checked run. -/
theorem checkCommandRun_claimed {disabled : List Digest} {domain : Digest}
    {directory : Directory Nat Registry}
    {ambient : Ambient} {command : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} (claimed : command.run = some claim) :
    checkCommandRun disabled domain directory ambient command pre ≠ .ok none := by
  unfold checkCommandRun
  rw [claimed]
  cases h : checkClaim disabled domain directory ambient command pre claim <;>
    simp [h, Except.map, Except.mapError]

/-- **`PreparedInvocation.run_sound`**: a prepared invocation whose command claims
a run carries that run checked on the program's own (registered, enabled) evaluator
against the kernel's own sample and the loaded pre-states, and the program's own
check (`checkRun` for a gate, `checkPoke` for a door) accepted exactly the command's
writes. With `Run.no_accepted_of_output_mismatch` / `NockDoor.door_poke_sound` this
is the T8 statement at the controller: no invocation prepares whose writes differ
from the program's. -/
theorem PreparedInvocation.run_sound {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
    {command : Command} (prepared : PreparedInvocation deployment profile ambient durable command)
    {claim : Run.RunClaim} (claimed : command.run = some claim) :
    ∃ checked program E libraries writes,
      prepared.run = some checked ∧ checked.claim = claim ∧
      CanonicalCellRegistry.loadProgram deployment.domain prepared.directory.directory
        claim.programId = some program ∧
      Run.resolve profile.disabledEvaluators program.evaluator = .ok E ∧
      checked.evaluator = E.id ∧
      program.abi.libraries.mapM (fun library => Run.require .libraryUnknown
        (CanonicalCellRegistry.loadProgram deployment.domain prepared.directory.directory library)) =
          .ok libraries ∧
      commandWrites command = some writes ∧
      ProgramAccepted E program libraries ambient command (fun i => (prepared.targets i).pre.logical)
        claim writes checked.verdict := by
  have h := prepared.runChecked
  cases hrun : prepared.run with
  | none => rw [hrun] at h; exact absurd h (checkCommandRun_claimed claimed)
  | some checked =>
    rw [hrun] at h
    obtain ⟨same, hc⟩ := checkCommandRun_sound h
    rw [claimed] at same
    cases same
    obtain ⟨program, E, libraries, writes, -, hp, he, hid, hl, -, hw, -, hr⟩ := checkClaim_sound hc
    exact ⟨checked, program, E, libraries, writes, rfl, rfl, hp, he, hid, hl, hw, hr⟩

/-- Without a claim, no run slot: the controller projects nothing under `run/`. -/
theorem PreparedInvocation.run_unclaimed {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
    {command : Command} (prepared : PreparedInvocation deployment profile ambient durable command)
    (unclaimed : command.run = none) : prepared.run = none := by
  have h := prepared.runChecked
  rw [checkCommandRun_none unclaimed] at h
  exact (Except.ok.inj h).symm

/-! ## Pinned programs: one claim, any height (K-RUN-PIN), on any evaluator -/

/-- **`pinned_claim_admissible_across_heights`**: a pinned gate's claim that the
kernel accepted at one admission is accepted, with the same verdict, at any
other — another height, another signer, another command — over the same
targets, whenever the ABI's named slots hold the values they held. A job whose
sample reads only its order's write-once fields therefore has one truth at
every height (COMPUTE §2.2). -/
theorem pinned_claim_admissible_across_heights {E : Evaluator} {program : NockProgramCodec.Program}
    {libraries : List NockProgramCodec.Program} {ambient ambient' : Ambient}
    {command command' : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {pre' : (i : Fin command'.targets.length) → Store command'.targets[i].layout}
    {claim : Run.RunClaim} {writes : List Eval.FieldWrite} {verdict : Run.Accepted}
    (gate : program.abi.door = none) (pinned : program.abi.context = .pinned)
    (sameTargets : command'.targets.map Target.target = command.targets.map Target.target)
    (unchanged : ∀ slot ∈ program.abi.sample,
      sampleRead command' pre' slot.target slot.slot = sampleRead command pre slot.target slot.slot)
    (accepted : checkProgram E program libraries ambient command pre claim writes = .ok verdict) :
    checkProgram E program libraries ambient' command' pre' claim writes = .ok verdict := by
  have same : E.sampleOf program.abi (runContext ambient' command')
      (command'.targets.map Target.target) (sampleRead command' pre') =
      E.sampleOf program.abi (runContext ambient command)
      (command.targets.map Target.target) (sampleRead command pre) := by
    rw [sameTargets]
    exact E.sampleOf_pinned_of_fields pinned _ _ _ unchanged
  have hmax : E.overMax (sampleRead command' pre') program.abi.sample =
      E.overMax (sampleRead command pre) program.abi.sample := E.overMax_congr unchanged
  unfold checkProgram at accepted ⊢
  rw [gate] at accepted ⊢
  simp only at accepted ⊢
  rw [hmax, same]
  exact accepted

/-- **`pinned_claim_stale_on_field_change`** (at the controller): once exactly
one named slot of a pinned gate moved, the claim the kernel accepted before
refuses `sampleStale` naming that slot's key, at any height. -/
theorem pinned_claim_stale_on_field_change {E : Evaluator} {program : NockProgramCodec.Program}
    {libraries : List NockProgramCodec.Program} {ambient ambient' : Ambient}
    {command command' : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {pre' : (i : Fin command'.targets.length) → Store command'.targets[i].layout}
    {claim : Run.RunClaim} {writes writes' : List Eval.FieldWrite}
    {verdict : Run.Accepted} {slot : NockProgramCodec.SampleSlot} {sample' : E.Input}
    (gate : program.abi.door = none) (pinned : program.abi.context = .pinned)
    (sameTargets : command'.targets.map Target.target = command.targets.map Target.target)
    (accepted : checkProgram E program libraries ambient command pre claim writes = .ok verdict)
    (current : E.sampleOf program.abi (runContext ambient' command')
      (command'.targets.map Target.target) (sampleRead command' pre') = some sample')
    (named : slot ∈ program.abi.sample)
    (changed : sampleRead command pre slot.target slot.slot ≠
      sampleRead command' pre' slot.target slot.slot)
    (only : ∀ s ∈ program.abi.sample, s ≠ slot →
      sampleRead command pre s.target s.slot = sampleRead command' pre' s.target s.slot) :
    checkProgram E program libraries ambient' command' pre' claim writes' =
      .error (.sampleStale (some slot.key)) := by
  have sound := checkProgram_sound accepted
  unfold ProgramAccepted at sound
  rw [gate] at sound
  obtain ⟨sample, v, hsample, ran, -⟩ := sound
  obtain ⟨-, -, -, -, -, computed, -⟩ := Run.checkRun_sound ran
  have under : E.overMax (sampleRead command' pre') program.abi.sample = none := by
    cases hs : E.overMax (sampleRead command' pre') program.abi.sample with
    | none => rfl
    | some s =>
      have refused : E.sampleOf program.abi (runContext ambient' command')
          (command'.targets.map Target.target) (sampleRead command' pre') = none :=
        E.sampleOf_overMax hs
      rw [refused] at current; cases current
  unfold checkProgram
  rw [gate]
  simp only [under]
  rw [current]
  dsimp only
  rw [sameTargets] at current
  rw [Run.pinned_claim_stale_on_field_change pinned hsample current computed named changed only]
  rfl

/-! ### The same at Nock (K-RUN-PIN's and NC-2's statements) -/

namespace nock

theorem checkProgram_fieldOverMax {program : NockProgramCodec.Program}
    {libraries : List NockProgramCodec.Program} {ambient : Ambient} {command : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} {writes : List Eval.FieldWrite} {slot : NockProgramCodec.SampleSlot}
    (gate : program.abi.door = none)
    (above : NockProgramCell.overMax (sampleRead command pre) program.abi.sample = some slot) :
    checkProgram Evaluator.nock program libraries ambient command pre claim writes =
      .error .fieldOverMax :=
  DeclaredResourceController.checkProgram_fieldOverMax (E := Evaluator.nock) gate above

theorem pinned_claim_admissible_across_heights {program : NockProgramCodec.Program}
    {libraries : List NockProgramCodec.Program} {ambient ambient' : Ambient}
    {command command' : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {pre' : (i : Fin command'.targets.length) → Store command'.targets[i].layout}
    {claim : Run.RunClaim} {writes : List Eval.FieldWrite} {verdict : Run.Accepted}
    (gate : program.abi.door = none) (pinned : program.abi.context = .pinned)
    (sameTargets : command'.targets.map Target.target = command.targets.map Target.target)
    (unchanged : ∀ slot ∈ program.abi.sample,
      sampleRead command' pre' slot.target slot.slot = sampleRead command pre slot.target slot.slot)
    (accepted : checkProgram Evaluator.nock program libraries ambient command pre claim writes =
      .ok verdict) :
    checkProgram Evaluator.nock program libraries ambient' command' pre' claim writes = .ok verdict :=
  DeclaredResourceController.pinned_claim_admissible_across_heights gate pinned sameTargets
    unchanged accepted

theorem pinned_claim_stale_on_field_change {program : NockProgramCodec.Program}
    {libraries : List NockProgramCodec.Program} {ambient ambient' : Ambient}
    {command command' : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {pre' : (i : Fin command'.targets.length) → Store command'.targets[i].layout}
    {claim : Run.RunClaim} {writes writes' : List Eval.FieldWrite}
    {verdict : Run.Accepted} {slot : NockProgramCodec.SampleSlot} {sample' : Noun}
    (gate : program.abi.door = none) (pinned : program.abi.context = .pinned)
    (sameTargets : command'.targets.map Target.target = command.targets.map Target.target)
    (accepted : checkProgram Evaluator.nock program libraries ambient command pre claim writes =
      .ok verdict)
    (current : NockProgramCell.sampleOf program.abi (runContext ambient' command')
      (command'.targets.map Target.target) (sampleRead command' pre') = some sample')
    (named : slot ∈ program.abi.sample)
    (changed : sampleRead command pre slot.target slot.slot ≠
      sampleRead command' pre' slot.target slot.slot)
    (only : ∀ s ∈ program.abi.sample, s ≠ slot →
      sampleRead command pre s.target s.slot = sampleRead command' pre' s.target s.slot) :
    checkProgram Evaluator.nock program libraries ambient' command' pre' claim writes' =
      .error (.sampleStale (some slot.key)) :=
  DeclaredResourceController.pinned_claim_stale_on_field_change (E := Evaluator.nock) gate pinned
    sameTargets accepted current named changed only

end nock

end Minidregg.Kernel.DeclaredResourceController

/-- info: 'Minidregg.Kernel.DeclaredResourceController.pinned_claim_admissible_across_heights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.pinned_claim_admissible_across_heights
/-- info: 'Minidregg.Kernel.DeclaredResourceController.pinned_claim_stale_on_field_change' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.pinned_claim_stale_on_field_change
/-- info: 'Minidregg.Kernel.DeclaredResourceController.checkCommandRun_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.checkCommandRun_none
/-- info: 'Minidregg.Kernel.DeclaredResourceController.checkProgram_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.checkProgram_sound
/-- info: 'Minidregg.Kernel.DeclaredResourceController.checkProgram_fieldOverMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.checkProgram_fieldOverMax
/-- info: 'Minidregg.Kernel.DeclaredResourceController.checkClaim_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.checkClaim_sound
/-- info: 'Minidregg.Kernel.DeclaredResourceController.checkCommandRun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.checkCommandRun_sound
/-- info: 'Minidregg.Kernel.DeclaredResourceController.checkCommandRun_claimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.checkCommandRun_claimed
/-- info: 'Minidregg.Kernel.DeclaredResourceController.PreparedInvocation.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.PreparedInvocation.run_sound
/-- info: 'Minidregg.Kernel.DeclaredResourceController.PreparedInvocation.run_unclaimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.PreparedInvocation.run_unclaimed
/-- info: 'Minidregg.Kernel.DeclaredResourceController.checkClaim_unknownEvaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.checkClaim_unknownEvaluator
/-- info: 'Minidregg.Kernel.DeclaredResourceController.nock.checkProgram_fieldOverMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.nock.checkProgram_fieldOverMax
/-- info: 'Minidregg.Kernel.DeclaredResourceController.nock.pinned_claim_admissible_across_heights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.nock.pinned_claim_admissible_across_heights
/-- info: 'Minidregg.Kernel.DeclaredResourceController.nock.pinned_claim_stale_on_field_change' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.nock.pinned_claim_stale_on_field_change
