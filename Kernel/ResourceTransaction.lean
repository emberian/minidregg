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
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev AuthoritySnapshot := CredentialAuthorityDomain.Snapshot
abbrev Ambient := DeclaredResourceScalar.Ambient

inductive Payload where
  | scalar (actions : List DeclaredActionLowering.Action)
  | content (command : ContentResource.Command)
  /-- An observe-only read of a content cell: no patch, authorized under the
  observe verb.  A `transclude` of another target of the same command names
  this cell as its source; this read is where the admission checks the
  transcluder's grant and the source's own policy at this height, and its
  loaded state is what the opening is checked against. -/
  | read
  deriving DecidableEq

/-- A content command shows as its canonical command bytes. -/
instance : Repr Payload where
  reprPrec payload prec := match payload with
    | .scalar actions => Repr.addAppParen ("Payload.scalar " ++ reprArg actions) prec
    | .content command =>
        Repr.addAppParen ("Payload.content " ++ reprArg (ContentResource.commandCodec.encode command)) prec
    | .read => "Payload.read"

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
      (StreamCodec.sum ContentResource.commandStream StoreCodec.unitStream))
    (fun payload => match payload with
      | .scalar actions => .inl actions
      | .content command => .inr (.inl command)
      | .read => .inr (.inr ()))
    (fun payload => match payload with
      | .inl actions => .scalar actions
      | .inr (.inl command) => .content command
      | .inr (.inr ()) => .read)
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
      (StreamCodec.product StreamCodec.nat (StreamCodec.list targetStream)))
    (fun command => (command.subject, command.nonce, command.targets))
    (fun (subject, nonce, targets) => ⟨subject, nonce, targets⟩)
    (by intro command; cases command; rfl)

/-- Version 5 (K-TRANSCLUDE): a target's payload may be an observe-only `read`.
Version 4 had no authority root in the command; version-3 and version-4
commands refuse. -/
def commandFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [5]

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

def observeVerb : (kind : ResourceKind) → Verb kind
  | .object => .observeObject
  | .account => .observeAccount
  | .program => .observeProgram

/-- The verb a target's authorization leg is checked under: observe for an
observe-only read target, the kind's ordinary write verb otherwise. -/
def Target.verb (target : Target) : Verb target.kind :=
  match target.payload with
  | .read => observeVerb target.kind
  | _ => ordinaryVerb target.kind

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
  | observationRequired | observationRejected
  deriving Repr

def requireSome {α : Type} (reason : Reject) : Option α → Except Reject α
  | none => .error reason | some value => .ok value

/-- The store layout of the target's role: a declared-effect cell for scalar
actions, a hyperdocument content cell for content commands. -/
def Target.layout (target : Target) : Layout.{0, 0, 0} := match target.payload with
  | .scalar _ => EffectDeclaration.effectLayout
  | .content _ | .read => Hyperdocument.layout

def Target.materializer (target : Target) : Materializer target.layout Digest := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact DeclaredEffectCell.materializer
    | content _ => exact HyperdocumentCell.contentMaterializer
    | read => exact HyperdocumentCell.contentMaterializer

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
    | read => exact ⟨.content, cell⟩

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
    | read => exact if kind = .object then
        if CanonicalCellRegistry.CellLaw deployment id cell then
          match cell with | ⟨.content, value⟩ => some value | _ => none
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

/-- The source policy identity a transclusion records: the policy id, epoch and
revision the source cell's read leg is checked against at this height. -/
def sourcePolicy (snapshot : AuthoritySnapshot) (source : Nat) : Digest :=
  ContentResource.contentDigest "DREGG/CONTENT/DISCLOSURE-POLICY"
    ((StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)).encode
      (source, snapshot.authState.policyEpoch ⟨source⟩, snapshot.authState.policyRevision ⟨source⟩))

/-- What a content target's actions consume of their transaction: the height,
and for each cell the transaction reads observe-only, the observe capability
that read carries and the source's policy. -/
def contentContext (snapshot : AuthoritySnapshot) (ambient : Ambient) (command : Command) :
    ContentResource.Context :=
  ⟨ambient.height, fun source =>
    (command.targets.find? fun target =>
        decide (target.target = source) && decide (target.payload = .read)).bind
      fun target => target.observeCapability.map fun capability =>
        ⟨capability, sourcePolicy snapshot source⟩⟩

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
            (contentOperation snapshot semantics command) (ContentResource.documentOf id)
            (contentContext snapshot ambient command) pre content with
        | .error reason => .error (.content reason)
        | .ok prepared => .ok prepared.post.logical
    | read => exact do
        if kind != .object then throw .wrongRole
        if version != ContentResource.commandVersion then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        pure pre.logical

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
          (contentContext snapshot ambient command) pre.logical content
        exact match computed with
          | .ok progress => progress.2
          | .error _ => []
    | read => exact []

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

/-- A prepared target's loaded content store, for a content or read target. -/
def Target.contentStore? (target : Target) (cell : TargetCell target) :
    Option ContentResource.ContentStore := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact none
    | content _ => exact some cell.logical
    | read => exact some cell.logical

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

/-- Every `transclude` of every content target names a cell this transaction
reads observe-only, and that cell's loaded state (this height) holds the
opening. -/
def openingsCheck (command : Command)
    (stores : TargetIndex command → Option ContentResource.ContentStore) : Bool :=
  (List.finRange command.targets.length).all fun i =>
    match command.targets[i].payload with
    | .content content => content.actions.all fun action =>
        match action with
        | .transclude _ _ request => (List.finRange command.targets.length).any fun j =>
            decide (command.targets[j].target = request.source) &&
              decide (command.targets[j].payload = .read) &&
              match stores j with
              | some store => ContentResource.openingHolds store request
              | none => false
        | _ => true
    | _ => true


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

structure PreparedInvocation {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) where
  private mk ::
  nonempty : command.targets ≠ []
  distinct : (command.targets.map Target.target).Nodup
  directory : LoadedDirectory durable
  authority : Loaded deployment durable.snapshot
  targets : (i : TargetIndex command) → PreparedTarget deployment directory.directory
    authority.snapshot profile.semantics ambient command command.targets[i]
  /-- Every transclusion's opening holds on its source read, at this height. -/
  openings : openingsCheck command (fun j => command.targets[j].contentStore? (targets j).pre) = true
  marker : MarkerMode authority.snapshot profile.semantics command

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
      if openings : openingsCheck command
          (fun j => command.targets[j].contentStore? (targets j).pre) = true then
        let marker ← prepareMarker authority.snapshot profile.semantics command
        .ok ⟨nonempty, distinct, directory, authority, targets, openings, marker⟩
      else .error (.content .staleOpening)
    else .error .duplicateTargets
  else .error .emptyTargets

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

end Minidregg.Kernel.DeclaredResourceController
