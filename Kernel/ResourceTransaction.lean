/- Source-owned finite resource transaction preparation. Scalar and typed content
operations share one command, exact old directory and authority snapshot, one
nullifier, one candidate tuple and one durable publication. No wire variant
contains a proposed post, raw patch, policy decision, or authority snapshot. -/
import Compiler.NativeProtocolFrames
import Kernel.DeclaredResourceScalar
import Kernel.WorldKindProjection
import Kernel.WorldKindMethods
import Kernel.WorldPrototypeConstruction
import Compiler.ObjectAudienceRoster
import Kernel.ObjectAudience
import Kernel.ContentResource
import Compiler.StreamCell
import Compiler.ResourceAuthorityProjection
import Kernel.Run
import Kernel.NockDoor
import Kernel.ClockCellDomain
import Kernel.RunComputeBudgetDomain
import Kernel.ResourceMoneyReceiver
import Kernel.BendNativeRun
import Kernel.ResourceObservationAdmission

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

/-- Transaction9's explicit consent to a source-derived Book burn. Payer and
capability are the containing signed account target, not duplicated here. -/
abbrev ComputeFunding := ResourceMoneyWire.FundingConsent
abbrev computeFundingStream := ResourceMoneyWire.fundingStream
abbrev MoneyConsent := ResourceMoneyWire.Consent

/-- A target's payload: declared scalar actions, a content command, or one
stream append (the entry's bytes; the receiver derives its sequence position
and digest). -/
inductive Payload where
  | scalar (actions : List DeclaredActionLowering.Action)
  | content (command : ContentResource.Command)
  | append (request : StreamCell.Append)
  | world (actions : List WorldKindInstance.Action)
  | kindDefinition (definition : WorldKindCell.Definition)
  /-- An observe-only read of a content cell: no patch, authorized under the
  observe verb.  A `transclude` of another target of the same command names
  this cell as its source; this read is where the admission checks the
  transcluder's grant and the source's own policy at this height, and its
  loaded state is what the opening is checked against. -/
  | read
  /-- Whole authenticated world-kind definition, observe-only. -/
  | kindRead
  | computeFunding (funding : ComputeFunding)
  | moneyConsent (consent : MoneyConsent)
  deriving DecidableEq

/-- A content command shows as its canonical command bytes. -/
instance : Repr Payload where
  reprPrec payload prec := match payload with
    | .scalar actions => Repr.addAppParen ("Payload.scalar " ++ reprArg actions) prec
    | .content command =>
        Repr.addAppParen ("Payload.content " ++ reprArg (ContentResource.commandCodec.encode command)) prec
    | .append request => Repr.addAppParen ("Payload.append " ++ reprArg request) prec
    | .world actions => Repr.addAppParen ("Payload.world " ++ reprArg actions) prec
    | .kindDefinition definition => Repr.addAppParen ("Payload.kindDefinition " ++ reprArg definition) prec
    | .read => "Payload.read"
    | .kindRead => "Payload.kindRead"
    | .computeFunding funding => Repr.addAppParen ("Payload.computeFunding " ++ reprArg funding) prec
    | .moneyConsent consent => Repr.addAppParen ("Payload.moneyConsent " ++ reprArg consent) prec

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
  /-- Protected object freshness and complete retained-holder binding. -/
  audienceEpoch : Option Nat := none
  audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster := none
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
  /-- Signed source execution; mutually exclusive with the historical Nock claim. -/
  bend : Option BendExecutionClaim.Claim := none
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

def payloadStream : StreamCodec Payload where
  encode
    | .scalar actions => 0 :: (StreamCodec.list DeclaredResourceScalar.actionStream).encode actions
    | .content command => 1 :: ContentResource.commandStream.encode command
    | .append request => 2 :: StreamCell.appendStream.encode request
    | .read => [3]
    | .world actions => 4 :: (StreamCodec.list WorldKindInstance.actionStream).encode actions
    | .kindDefinition definition => 5 :: WorldKindCell.definitionStream.encode definition
    | .computeFunding funding => 6 :: computeFundingStream.encode funding
    | .kindRead => [7]
    | .moneyConsent consent => 8 :: ResourceMoneyWire.consentStream.encode consent
  decodePrefix
    | 0 :: bytes => do
        let (actions, rest) ← (StreamCodec.list DeclaredResourceScalar.actionStream).decodePrefix bytes
        some (.scalar actions, rest)
    | 1 :: bytes => do
        let (command, rest) ← ContentResource.commandStream.decodePrefix bytes
        some (.content command, rest)
    | 2 :: bytes => do
        let (request, rest) ← StreamCell.appendStream.decodePrefix bytes
        some (.append request, rest)
    | 3 :: bytes => some (.read, bytes)
    | 4 :: bytes => do
        let (actions, rest) ← (StreamCodec.list WorldKindInstance.actionStream).decodePrefix bytes
        some (.world actions, rest)
    | 5 :: bytes => do
        let (definition, rest) ← WorldKindCell.definitionStream.decodePrefix bytes
        some (.kindDefinition definition, rest)
    | 6 :: bytes => do
        let (funding, rest) ← computeFundingStream.decodePrefix bytes
        some (.computeFunding funding, rest)
    | 7 :: bytes => some (.kindRead, bytes)
    | 8 :: bytes => do
        let (consent, rest) ← ResourceMoneyWire.consentStream.decodePrefix bytes
        some (.moneyConsent consent, rest)
    | _ => none
  decodePrefix_encode := by
    intro payload suffix
    cases payload <;> simp [StreamCodec.decodePrefix_encode]

def targetStream : StreamCodec Target :=
  StreamCodec.xmap
    (StreamCodec.product ResourceBirthCodec.resourceKindStream
      (StreamCodec.product StreamCodec.nat
      (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
      (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream
      (StreamCodec.product payloadStream
      (StreamCodec.product (StreamCodec.option CredentialAuthorityEntryCodec.capabilityIdStream)
      (StreamCodec.product (StreamCodec.option StreamCodec.nat)
      (StreamCodec.option Minidregg.Compiler.ObjectAudienceRoster.rosterStream)))))))))
    (fun target => (target.kind, target.target, target.capability, target.schemaVersion,
      target.expectedTargetRoot, target.payload, target.observeCapability,
      target.audienceEpoch, target.audienceRoster))
    (fun (kind, target, capability, version, root, payload, observe, epoch, roster) =>
      ⟨kind, target, capability, version, root, payload, observe, epoch, roster⟩)
    (by intro target; cases target; rfl)

/-- `DREGG/NOCK/RUN/v1` inside the command: program id, sample jam, output jam, steps. -/
def runClaimStream : StreamCodec Run.RunClaim :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream StreamCodec.nat)))
    (fun claim => (claim.programId, claim.sampleJam, claim.outputJam, claim.steps))
    (fun (program, sample, output, steps) => ⟨program, sample, output, steps⟩)
    (by intro claim; cases claim; rfl)

/-- Keep transaction10 bytes identical for every historical Nock command. -/
def legacyCommandStream : StreamCodec (SubjectId × Nat × List Target × Option Run.RunClaim) :=
  StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.list targetStream) (StreamCodec.option runClaimStream)))

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product legacyCommandStream (StreamCodec.option BendExecutionClaim.stream))
    (fun c => ((c.subject,c.nonce,c.targets,c.run),c.bend))
    (fun c => ⟨c.1.1,c.1.2.1,c.1.2.2.1,c.1.2.2.2,c.2⟩)
    (by intro c; cases c; rfl)

def bendCommandFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [11]

def rawCommandCodec : LawfulCodec Command where
  encode command := match command.bend with
    | none => commandFrame ++ legacyCommandStream.encode
        (command.subject,command.nonce,command.targets,command.run)
    | some _ => bendCommandFrame ++ commandStream.encode command
  decode bytes :=
    if bytes.take commandFrame.length = commandFrame then do
      let c ← legacyCommandStream.toLawful.decode (bytes.drop commandFrame.length)
      pure ⟨c.1,c.2.1,c.2.2.1,c.2.2.2,none⟩
    else if bytes.take bendCommandFrame.length = bendCommandFrame then
      commandStream.toLawful.decode (bytes.drop bendCommandFrame.length)
    else none
  decode_encode := by
    intro command
    cases command with
    | mk subject nonce targets run bend =>
      cases bend <;> simp [rawCommandCodec, commandStream, legacyCommandStream,
        StreamCodec.decodePrefix_encode, StreamCodec.toLawful]

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

/-- A version-5 command frame (K-STREAM's, K-RAN's or K-TRANSCLUDE's: three
different shapes) refuses to decode. -/
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

/-- Previous commands cannot be reinterpreted under the extended payload tags. -/
theorem v6_command_refused (payload : List UInt8) :
    rawCommandCodec.decode ("DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ 6 :: payload) = none := by
  let oldFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [6]
  have lengthExact : commandFrame.length = oldFrame.length := by
    simp [commandFrame, oldFrame]
  have different : oldFrame ≠ commandFrame := by decide +kernel
  have refused : rawCommandCodec.decode (oldFrame ++ payload) = none := by
    simp [rawCommandCodec, lengthExact, different]
  simpa only [oldFrame, List.append_assoc, List.singleton_append] using refused

/-- info: 'Minidregg.Kernel.DeclaredResourceController.v6_command_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v6_command_refused

/-- Neither retired v7 candidate can be read under the union target contract. -/
theorem v7_command_refused (payload : List UInt8) :
    rawCommandCodec.decode ("DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ 7 :: payload) = none := by
  let oldFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [7]
  have lengthExact : commandFrame.length = oldFrame.length := by simp [commandFrame, oldFrame]
  have different : oldFrame ≠ commandFrame := by decide +kernel
  have refused : rawCommandCodec.decode (oldFrame ++ payload) = none := by
    simp [rawCommandCodec, lengthExact, different]
  simpa only [oldFrame, List.append_assoc, List.singleton_append] using refused

/-- Core transaction8 is never reinterpreted under paid execution semantics. -/
theorem v8_command_refused (payload : List UInt8) :
    rawCommandCodec.decode ("DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ 8 :: payload) = none := by
  let oldFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [8]
  have lengthExact : commandFrame.length = oldFrame.length := by simp [commandFrame, oldFrame]
  have different : oldFrame ≠ commandFrame := by decide +kernel
  have refused : rawCommandCodec.decode (oldFrame ++ payload) = none := by
    simp [rawCommandCodec, lengthExact, different]
  simpa only [oldFrame, List.append_assoc, List.singleton_append] using refused

/-- Prototype receiver v10 cannot reinterpret a numeric-only v9 command. -/
theorem v9_command_refused (payload : List UInt8) :
    rawCommandCodec.decode ("DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ 9 :: payload) = none := by
  let oldFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [9]
  have lengthExact : commandFrame.length = oldFrame.length := by simp [commandFrame, oldFrame]
  have different : oldFrame ≠ commandFrame := by decide +kernel
  have refused : rawCommandCodec.decode (oldFrame ++ payload) = none := by
    simp [rawCommandCodec, lengthExact, different]
  simpa only [oldFrame, List.append_assoc, List.singleton_append] using refused

@[simp] theorem command_decode_encode (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command := commandCodec.decode_encode command

theorem command_decode_canonical {bytes : List UInt8} {command : Command}
    (decoded : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCommandCodec decoded

/-- Empty lists never reach preparation; the default merely makes this total. -/
def Command.first (command : Command) : Target :=
  command.targets.headD ⟨.object, 0, ⟨0⟩, 1, ⟨0⟩, .scalar [], none, none, none⟩

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

/-- The verb a target's authorization leg is checked under: `appendObject` for
a stream append on an object, observe for an observe-only read target, the
kind's ordinary write verb otherwise. -/
def payloadVerb : (kind : ResourceKind) → Payload → Verb kind
  | .object, .append _ => .appendObject
  | kind, .read | kind, .kindRead => observeVerb kind
  | kind, .moneyConsent _ => ordinaryVerb kind
  | kind, _ => ordinaryVerb kind

def Target.verb (target : Target) : Verb target.kind := payloadVerb target.kind target.payload

/-- Payment authority is charged the exact consented credit amount; all other
legs retain canonical command-byte cost. Structural preparation rejects a
funding payload on any role except account. -/
def requestCost (encodedCommand : List UInt8) (target : Target) : Nat :=
  match target.payload with
  | .computeFunding funding => funding.credits
  | .moneyConsent consent => encodedCommand.length +
      (consent.funding.map ResourceMoneyWire.FundingConsent.credits).getD 0
  | _ => encodedCommand.length

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
  cost := requestCost (commandCodec.encode command) target

/-- Encode the canonical command and its domain/profile frame once per
request. The same exact framed bytes feed both digest domains; the raw
funding credits are the funding leg cost; other legs retain canonical command length. -/
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
    cost := requestCost encodedCommand target }

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
  | bendExecution
  | observationRequired | observationRejected | clockUnavailable
  | streamTopic | streamPayload
  | worldKind | kindDefinition
  | computeFunding
  | computeBudget (reason : RunComputeBudgetDomain.Reject)
  | money (reason : ResourceMoneyReceiver.Reject)
  | audience (reason : ObjectAudience.Reject)
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
  | .scalar _ | .computeFunding _ | .moneyConsent _ => EffectDeclaration.effectLayout
  | .content _ | .read => Hyperdocument.layout
  | .append _ => StreamCell.headLayout
  | .world _ => WorldKindCell.instanceLayout
  | .kindDefinition _ | .kindRead => WorldKindCell.definitionLayout

def Target.materializer (target : Target) : Materializer target.layout Digest := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar _ | computeFunding _ | moneyConsent _ => exact DeclaredEffectCell.materializer
    | content _ => exact HyperdocumentCell.contentMaterializer
    | append _ => exact StreamCell.headMaterializer
    | world _ => exact WorldKindCell.instanceMaterializer
    | kindDefinition _ | kindRead => exact WorldKindCell.definitionMaterializer
    | read => exact HyperdocumentCell.contentMaterializer

abbrev TargetCell (target : Target) := Materialized target.materializer

/-- A target's outcome is its computed post store. -/
abbrev Target.Outcome (target : Target) : Type := Store target.layout

def Target.outcomeCodec (target : Target) : LawfulCodec target.Outcome :=
  target.materializer.codec

def packTarget (target : Target) (cell : TargetCell target) : PackedCell Registry := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar _ => exact DeclaredResourceScalar.packDeclared kind cell
    | computeFunding _ | moneyConsent _ => exact ⟨.accountMetadata, cell⟩
    | content _ => exact ⟨.content, cell⟩
    | append _ => exact ⟨.stream, cell⟩
    | world _ => exact ⟨.worldInstance, cell⟩
    | kindDefinition _ | kindRead => exact ⟨.worldKind, cell⟩
    | read => exact ⟨.content, cell⟩

def selectTarget (deployment : Deployment) (target : Target) (cell : PackedCell Registry) :
    Option (TargetCell target) := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar _ => exact CanonicalCellRegistry.selectDeclared deployment id kind cell
    | computeFunding _ | moneyConsent _ => exact if kind = .account then
        CanonicalCellRegistry.selectDeclared deployment id .account cell else none
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
    | world _ => exact if kind = .object then
        if CanonicalCellRegistry.CellLaw deployment id cell then
          match cell with | ⟨.worldInstance, value⟩ => some value | _ => none
        else none
      else none
    | kindDefinition _ | kindRead => exact if kind = .object then
        if CanonicalCellRegistry.CellLaw deployment id cell then
          match cell with | ⟨.worldKind, value⟩ => some value | _ => none
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

/-- The record an append stores: the request's entry plus the signing
subject, the admission height and the exact transaction id. -/
def streamRecord (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (request : StreamCell.Append) : StreamCell.StreamRecord :=
  ⟨command.subject, ambient.height, ⟨operationMarker snapshot.domain semantics command⟩, request.entry⟩

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
operation computed at the loaded cell; a scalar or content write then advances
the cell's blinding ratchet one link at the admission height
(`StoreCodec.Blinding.patch`, K-HIDE-ROTATE).  A stream append has no blinding. -/
def computeTarget (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (command : Command) (target : Target)
    (pre : TargetCell target) : Except Reject target.Outcome := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar actions =>
      let projected := scalarCommand command ⟨kind, id, capability, version, root, .scalar actions, observe, audienceEpoch, audienceRoster⟩ actions
      exact match DeclaredResourceScalar.prepareCell snapshot semantics ambient pre projected with
        | .error reason => .error (.scalar reason)
        | .ok prepared => .ok (Patch.run prepared.post
            (DeclaredEffectCell.blinding.patch pre.logical ambient.height))
    | computeFunding _ => exact do
        if kind != .account then throw .wrongRole
        if version != 1 then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        if audienceEpoch.isSome || audienceRoster.isSome then throw .computeFunding
        pure pre.logical
    | moneyConsent _ => exact do
        if kind != .account then throw .wrongRole
        if version != 1 then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        if audienceEpoch.isSome || audienceRoster.isSome then throw .computeFunding
        pure pre.logical
    | content content => exact do
        if kind != .object then throw .wrongRole
        if version != ContentResource.commandVersion then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        match ContentResource.prepareCell ⟨command.subject, kind, capability⟩
            (contentOperation snapshot semantics command) (ContentResource.documentOf id)
            (contentContext snapshot ambient command) pre content with
        | .error reason => .error (.content reason)
        | .ok prepared => .ok (Patch.run prepared.post.logical
            (HyperdocumentCell.contentBlinding.patch pre.logical ambient.height))
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
    | read => exact do
        if kind != .object then throw .wrongRole
        if version != ContentResource.commandVersion then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        pure pre.logical

    | kindRead => exact do
        if kind != .object then throw .wrongRole
        if version != 1 then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        -- Partial grants never receive canonical hidden defaults.
        if observe != some capability then throw .observationRequired
        let some stored := CredentialAuthorityState.readCapability snapshot.cell .object capability
          | throw .observationRejected
        if stored.head.scope.fields.isSome then throw .fieldNotNamed
        pure pre.logical

    | world actions => exact do
        if kind != .object then throw .wrongRole
        if version != 1 then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        let some patch := WorldKindCell.preparePatch pre.logical actions | throw .worldKind
        if !decide (Patch.ValidFrom pre.logical patch) then throw .worldKind
        let post := Patch.run pre.logical patch
        if (WorldKindProjection.footprint pre.logical post).isNone then throw .worldKind
        pure post
    | kindDefinition definition => exact do
        if kind != .object then throw .wrongRole
        if version != 1 then throw .unsupportedVersion
        if root != pre.root then throw .staleTarget
        let some patch := WorldKindCell.prepareDefinition pre.logical definition | throw .kindDefinition
        if !decide (Patch.ValidFrom pre.logical patch) then throw .kindDefinition
        pure (Patch.run pre.logical patch)

/-- The target's one guarded patch, generated by its source operation from the
loaded store: the scalar declaration's own lowering, or the content run's patch,
each followed by the kernel's ratchet of the cell's blinding (guarded at the
pre blinding, so a source patch that moved it refuses). -/
def targetPatch (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) (pre : TargetCell target) : Patch target.layout := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar actions =>
        exact DeclaredResourceScalar.cellPatch (scalarCommand command ⟨kind, id, capability, version, root, .scalar actions, observe, audienceEpoch, audienceRoster⟩ actions) ++
          DeclaredEffectCell.blinding.patch pre.logical ambient.height
    | content content =>
        let computed := ContentResource.run ⟨command.subject, kind, capability⟩
          (contentOperation snapshot semantics command) (ContentResource.documentOf id)
          (contentContext snapshot ambient command) pre.logical content
        exact match computed with
          | .ok progress => progress.2 ++
              HyperdocumentCell.contentBlinding.patch pre.logical ambient.height
          | .error _ => []
    | append request =>
        exact match StreamCell.headOf pre.logical with
          | some head => [StreamCell.headWriteOp head (StreamCell.appendEntry id head
              (streamRecord snapshot semantics ambient command request))]
          | none => []
    | read | kindRead | computeFunding _ | moneyConsent _ => exact []

    | world actions => exact (WorldKindCell.preparePatch pre.logical actions).getD []
    | kindDefinition definition => exact (WorldKindCell.prepareDefinition pre.logical definition).getD []

/-- The entry an append target records, at the cell `entryCellId target n`:
the loaded head's next position and tail. Scalar and content targets record none.
The head write is the target's own patch; this entry is its one fresh cell. -/
def appendedEntry (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) (pre : TargetCell target) : Option StreamCell.Entry := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar _ | computeFunding _ | moneyConsent _ => exact none
    | content _ => exact none
    | world _ => exact none
    | kindDefinition _ | kindRead => exact none
    | read => exact none
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

/-- A prepared target's loaded content store, for a content or read target. -/
def Target.contentStore? (target : Target) (cell : TargetCell target) :
    Option ContentResource.ContentStore := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar _ | computeFunding _ | moneyConsent _ => exact none
    | content _ => exact some cell.logical
    | append _ => exact none
    | read => exact some cell.logical
    | world _ | kindDefinition _ | kindRead => exact none

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
  audienceFresh : ObjectAudience.checkFresh source.record.audience target.target target.audienceEpoch = .ok ()

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
              match fresh : ObjectAudience.checkFresh source.record.audience target.target target.audienceEpoch with
              | .error reason => .error (.audience reason)
              | .ok () => .ok ⟨before, present, pre, selected, post, candidate, postExact, postLaw, source, fresh⟩
            else .error .invalidPost
          else .error .invalidPost

/-- **An admitted scalar write advances the target's blinding ratchet**
(K-HIDE-ROTATE): the post blinding of every prepared scalar leg of a blinded
declared cell is one ratchet step of the pre blinding at the admission height. -/
theorem PreparedTarget.scalar_ratchets {deployment : Deployment}
    {directory : Directory Nat Registry} {snapshot : AuthoritySnapshot} {semantics : Digest}
    {ambient : Ambient} {command : Command} {kind : ResourceKind} {id : Nat}
    {capability : CapabilityId} {version : Nat} {root : Digest}
    {actions : List DeclaredActionLowering.Action} {observe : Option CapabilityId}
    {audienceEpoch : Option Nat}
    {audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster}
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command
      ⟨kind, id, capability, version, root, .scalar actions, observe, audienceEpoch, audienceRoster⟩)
    {key : List UInt8}
    (blinded : StoreCodec.blindingKey DeclaredEffectCell.wire prepared.pre.logical = some key) :
    StoreCodec.blindingKey DeclaredEffectCell.wire prepared.post =
      some (DeclaredEffectCell.blinding.step ambient.height key) := by
  rw [← prepared.postExact]
  exact DeclaredEffectCell.blinding.run_leg_blinding prepared.pre.logical _ ambient.height blinded

/-- **An admitted content write advances the target's blinding ratchet**
(K-HIDE-ROTATE), as for a scalar write. -/
theorem PreparedTarget.content_ratchets {deployment : Deployment}
    {directory : Directory Nat Registry} {snapshot : AuthoritySnapshot} {semantics : Digest}
    {ambient : Ambient} {command : Command} {kind : ResourceKind} {id : Nat}
    {capability : CapabilityId} {version : Nat} {root : Digest}
    {content : ContentResource.Command} {observe : Option CapabilityId}
    {audienceEpoch : Option Nat}
    {audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster}
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command
      ⟨kind, id, capability, version, root, .content content, observe, audienceEpoch, audienceRoster⟩)
    {key : List UInt8}
    (blinded : StoreCodec.blindingKey HyperdocumentCell.contentWire prepared.pre.logical = some key)
    (ran : ∃ progress, ContentResource.run ⟨command.subject, kind, capability⟩
      (contentOperation snapshot semantics command) (ContentResource.documentOf id)
      (contentContext snapshot ambient command) prepared.pre.logical content = .ok progress) :
    StoreCodec.blindingKey HyperdocumentCell.contentWire prepared.post =
      some (HyperdocumentCell.contentBlinding.step ambient.height key) := by
  rw [← prepared.postExact]
  show StoreCodec.blindingKey HyperdocumentCell.contentWire
    (Patch.run prepared.pre.logical (targetPatch snapshot semantics ambient command
      ⟨kind, id, capability, version, root, .content content, observe, audienceEpoch, audienceRoster⟩ prepared.pre)) = _
  simp only [targetPatch]
  split
  · exact HyperdocumentCell.contentBlinding.run_leg_blinding prepared.pre.logical _ ambient.height
      blinded
  · rename_i failed
    obtain ⟨_, ok⟩ := ran
    rw [failed] at ok
    cases ok

/-- info: 'Minidregg.Kernel.DeclaredResourceController.PreparedTarget.scalar_ratchets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedTarget.scalar_ratchets
/-- info: 'Minidregg.Kernel.DeclaredResourceController.PreparedTarget.content_ratchets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedTarget.content_ratchets

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

/-- The explicit consent's numeric view. prepareCompute binds these exact
payer balance, Book root and credits to the loaded Book before an accepted invocation can use
them; no arbitrary balance mutation is installed in account metadata. -/
def fundingProject (funding : ComputeFunding) : List (String × Int) :=
  [("compute/charge", 1),
   ("compute/asset", Int.ofNat funding.asset),
   ("compute/credits", Int.ofNat funding.credits),
   ("compute/payer/before", funding.expectedPayerBalance),
   ("compute/payer/after", funding.expectedPayerBalance - Int.ofNat funding.credits)]

/-- Exact scalar/content/stream projection from the committed old and candidate
final states. Local names remain convenient; joint names expose every declared
participant without granting a view of unrelated cells. -/
def targetProjection (subject : SubjectId) (target : Target) (before after : Store target.layout) : List (String × Int) := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar _ => exact DeclaredResourceProjection.project id before after
    | computeFunding funding => exact fundingProject funding
    | moneyConsent consent => exact
        [("money/consent", 1), ("money/positions", Int.ofNat consent.positions.length)] ++
          (consent.funding.map fundingProject).getD []
    | content content => exact ContentResource.project before after content
    | append request => exact streamSlots request before
    | world _ => exact WorldKindProjection.project subject before after
    | kindDefinition _ => exact WorldKindProjection.definitionProject before after
    | kindRead => exact WorldPrototypeConstruction.observeProject before
    | read => exact ContentResource.project before after ⟨[]⟩

/-- The participant slot a sample reads: target `i`'s projection of its loaded
pre-state (before = after = pre), so a program sees only committed values. -/
def sampleRead (command : Command) (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (i : Nat) (slot : String) : Option Int :=
  if h : i < command.targets.length then
    (⟨targetProjection command.subject command.targets[(⟨i, h⟩ : Fin _)] (pre ⟨i, h⟩) (pre ⟨i, h⟩)⟩ :
      Minidregg.Pred.State).get slot
  else none

/-- The validated system funding leg is last and is not an evaluator participant.
Without the source budget token's index, every signed target remains in the sample. -/
def programTargets (command : Command) (validatedFundingIndex : Option Nat := none) : List Nat :=
  match validatedFundingIndex with
  | none => command.targets.map Target.target
  | some index => (command.targets.take index).map Target.target

/-- Preserve program-local coordinates while preventing a slot from reading the
funding participant (or any index beyond the actual program prefix). -/
def programSampleRead (command : Command)
    (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (validatedFundingIndex : Option Nat := none) : Nat → String → Option Int :=
  match validatedFundingIndex with
  | none => sampleRead command pre
  | some _ => fun i slot =>
      if i < (programTargets command validatedFundingIndex).length then sampleRead command pre i slot
      else none

theorem programTargets_unfunded (command : Command) :
    programTargets command none = command.targets.map Target.target := rfl

theorem programSampleRead_outside {command : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {fundingIndex i : Nat} (slot : String)
    (outside : (programTargets command (some fundingIndex)).length ≤ i) :
    programSampleRead command pre (some fundingIndex) i slot = none := by
  simp [programSampleRead, Nat.not_lt.mpr outside]

/-- One action as a field write of the command's `i`-th target, when it is one. -/
def actionWrite (i target : Nat) : DeclaredActionLowering.Action → Option Eval.FieldWrite
  | .write (.objectField object field) _ value =>
      if object.value = target then some ⟨i, field.value, value⟩ else none
  | .create (.objectField object field) value =>
      if object.value = target then some ⟨i, field.value, value⟩ else none
  | _ => none

/-- The actual pre-state supplies world method bindings. Output coordinates are
program-local names, never substitutes for capability semantic field IDs. -/
def targetWrites (i : Nat) (target : Target) (pre : Store target.layout)
    (program : Digest) (validatedFundingIndex : Option Nat := none) :
    Option (List Eval.FieldWrite) := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar actions => exact actions.mapM (actionWrite i id)
    | world actions => exact WorldKindMethods.writes pre program i actions
    | content content => exact some [⟨i, 0,
        WorldPrototypeConstruction.bytesValue (ContentResource.commandStream.encode content)⟩]
    | append request => exact some [⟨i, 0,
        WorldPrototypeConstruction.bytesValue (StreamCell.appendStream.encode request)⟩]
    | kindDefinition definition => exact some [WorldPrototypeConstruction.constructorWrite i definition]
    | read | kindRead => exact some []
    | computeFunding _ => exact if kind = .account ∧ validatedFundingIndex = some i then some [] else none
    | moneyConsent _ => exact none -- Nock field-write output cannot certify canonical money.

/-- Merely spelling a funding payload cannot remove it from run-effect
checking. Only prepareCompute's validated index enables the system-leg route. -/
theorem funding_unvalidated (index target : Nat) (capability : CapabilityId)
    (root program : Digest) (funding : ComputeFunding)
    (pre : Store EffectDeclaration.effectLayout) :
    targetWrites index ⟨.account, target, capability, 1, root,
      .computeFunding funding, none, none, none⟩ pre program none = none := by
  simp [targetWrites]

/-- Extract checked effects from every actual loaded participant. A world
participant must bind the claimed immutable program in its retained ROM table. -/
def commandWrites (command : Command)
    (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (program : Digest) (validatedFundingIndex : Option Nat := none) :
    Option (List Eval.FieldWrite) := do
  let groups ← (List.finRange command.targets.length).mapM fun i =>
    targetWrites i.val command.targets[i] (pre i) program validatedFundingIndex
  pure groups.flatten

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
    (claim : Run.RunClaim) (writes : List Eval.FieldWrite)
    (validatedFundingIndex : Option Nat := none) :
    Except Run.Refusal Run.Accepted :=
  match program.abi.door with
  | none =>
    match E.overMax (programSampleRead command pre validatedFundingIndex) program.abi.sample with
    | some _ => .error .fieldOverMax
    | none =>
    match E.sampleOf program.abi (runContext ambient command)
        (programTargets command validatedFundingIndex) (programSampleRead command pre validatedFundingIndex) with
    | none => .error .sampleUnavailable
    | some sample =>
      (Run.checkRun E.toMachine program libraries sample claim writes).map
        (Run.Verdict.erase E.toMachine)
  | some door =>
    match E.door with
    | none => .error .doorUnsupported
    | some d =>
      match Door.viewOf door (programSampleRead command pre validatedFundingIndex) with
      | .error e => .error e
      | .ok view =>
        (Door.checkPoke E.toMachine d program door view claim writes).map (Run.Verdict.erase E.toMachine)

/-- Load the claimed program, resolve its evaluator against the compiled-in registry
(less what the operator disabled), load its libraries (on the same evaluator), and
re-execute it against the loaded pre-states (`checkProgram`). -/
def checkClaim (disabled : List Digest) (domain : Digest) (directory : Directory Nat Registry)
    (ambient : Ambient) (command : Command)
    (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (claim : Run.RunClaim) (validatedFundingIndex : Option Nat := none) :
    Except Run.Refusal CheckedRun :=
  match CanonicalCellRegistry.loadProgram domain directory claim.programId with
  | none => .error .programUnknown
  | some program =>
    match Run.resolve disabled program.evaluator with
    | .error reason => .error reason
    | .ok E => do
      let libraries ← program.abi.libraries.mapM fun library =>
        Run.require .libraryUnknown (CanonicalCellRegistry.loadProgram domain directory library)
      if !Run.librariesAgree program libraries then throw .libraryEvaluator
      let writes ← Run.require .writeNotInOutput (commandWrites command pre claim.programId validatedFundingIndex)
      let verdict ← checkProgram E program libraries ambient command pre claim writes validatedFundingIndex
      pure ⟨claim, E.id, program.abi.fuel, verdict⟩

/-- No claim: nothing to check. A claim: `checkClaim`, its refusal named `run`. -/
def checkCommandRun (disabled : List Digest) (domain : Digest) (directory : Directory Nat Registry)
    (ambient : Ambient) (command : Command)
    (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (validatedFundingIndex : Option Nat := none) : Except Reject (Option CheckedRun) :=
  match command.run with
  | none => .ok none
  | some claim => ((checkClaim disabled domain directory ambient command pre claim validatedFundingIndex).map some).mapError .run

/-- Extract at most one explicit account funding leg from the actual signed
command. No run means no funding; caller-selected exclusion indices do not enter
this API. The domain quote and Book preparation run before the evaluator. -/
def prepareCompute (deployment : Deployment) (physical : RunComputeBudgetDomain.Physical)
    (clock : ClockCell.Clock) (command : Command) :
    Except Reject (Option (RunComputeBudgetDomain.Prepared deployment physical command.subject)) := do
  let funding ← (List.finRange command.targets.length).foldlM
    (fun (selected : Option RunComputeBudgetDomain.FundingInput) i => do
      let target := command.targets[i]
      match target.payload with
      | .computeFunding consent =>
          if target.kind != .account || selected.isSome || i.val + 1 != command.targets.length then
            throw .computeFunding
          pure (some ⟨i.val, target.target, target.capability, consent.asset, consent.credits,
            consent.expectedPayerBalance, consent.expectedBookRoot⟩)
      | .moneyConsent consent =>
          match consent.funding with
          | none => pure selected
          | some funding =>
            if target.kind != .account || selected.isSome || i.val + 1 != command.targets.length then
              throw .computeFunding
            pure (some ⟨i.val, target.target, target.capability, funding.asset, funding.credits,
              funding.expectedPayerBalance, funding.expectedBookRoot⟩)
      | _ => pure selected) none
  match command.run, command.bend with
  | none, none => if funding.isSome then throw .computeFunding else pure none
  | some claim, none =>
      let prepared ← (RunComputeBudgetDomain.prepare deployment physical clock command.subject
        claim.steps funding).mapError Reject.computeBudget
      pure (some prepared)
  | none, some claim =>
      let prepared ← (RunComputeBudgetDomain.prepare deployment physical clock command.subject
        claim.capacity.proofWork funding).mapError Reject.computeBudget
      if prepared.credits != claim.capacity.feeDebit then throw .computeFunding
      pure (some prepared)
  | some _, some _ => throw .bendExecution

/-- The account identity is taken only from the containing signed target. -/
def moneyEntries (command : Command) : List ResourceMoneyWire.Entry :=
  command.targets.filterMap fun target => match target.payload with
    | .moneyConsent consent => some ⟨target.target, consent⟩
    | _ => none

def prepareMoney (deployment : Deployment) (physical : RunComputeBudgetDomain.Physical)
    (command : Command)
    (compute : Option (RunComputeBudgetDomain.Prepared deployment physical command.subject)) :
    Except Reject (Option (ResourceMoneyReceiver.Prepared deployment physical (moneyEntries command))) :=
  (ResourceMoneyReceiver.prepare compute (moneyEntries command)).mapError Reject.money

def computeFundingIndex {deployment : Deployment} {physical : RunComputeBudgetDomain.Physical}
    {subject : SubjectId} (compute : Option (RunComputeBudgetDomain.Prepared deployment physical subject)) :
    Option Nat := compute.bind (fun prepared => prepared.fundingIndex)

/-- No compute plan can settle an unchecked/differently counted execution. -/
def computeRunMatches {deployment : Deployment} {physical : RunComputeBudgetDomain.Physical}
    {subject : SubjectId} :
    Option (RunComputeBudgetDomain.Prepared deployment physical subject) → Option CheckedRun → Bool
  | none, none => true
  | some compute, some run => decide (compute.steps = run.verdict.steps)
  | _, _ => false

def computeExecutionMatches {deployment : Deployment} {physical : RunComputeBudgetDomain.Physical}
    {subject : SubjectId} (command : Command)
    (compute : Option (RunComputeBudgetDomain.Prepared deployment physical subject))
    (run : Option CheckedRun) : Bool :=
  match command.bend with
  | none => computeRunMatches compute run
  | some claim => run.isNone && compute.any (fun funded =>
      decide (funded.steps = claim.capacity.proofWork ∧ funded.credits = claim.capacity.feeDebit))

/-- Native source input is constructed from the SAME current directory and
read scopes as the signed transaction. It never accepts a sampled store from
the client. Source/funding dependencies remain native read guards, even when
excluded from the application-visible observation vector. -/
def bendObservations {deployment : Deployment} {durable : Durable} (context : ResourceObservationAdmission.Context deployment durable)
    (command : Command) (sourceIndex : Nat)
    (compute : Option (RunComputeBudgetDomain.Prepared deployment durable.snapshot command.subject)) :
    Option (List BendNativeInput.Observation) := do
  let indices := (List.finRange command.targets.length).filter fun i =>
    i.val != sourceIndex &&
      match command.targets[i].payload with | .computeFunding _ => false | _ => true
  indices.mapM fun i => do
    let target := command.targets[i]
    let .present packed := context.directory.directory.slots target.target | none
    let fields := ResourceObservationAdmission.readerFields context target.kind
      (target.observeCapability.getD ⟨0⟩)
    let narrowed := ResourceObservationAdmission.narrowPacked fields packed
    let balances ← match compute with
      | some funded => if target.kind = .account then
          some (CanonicalAccountView.accountCut
            (CanonicalResourceKernel.logicalBook funded.budget.book.post.logical) target.target)
        else some []
      | none => ResourceObservationAdmission.balances context target.kind target.target
    pure ⟨target.target, target.expectedTargetRoot, packed.kind.tag.toNat,
      (CanonicalCellRegistry.materializer narrowed.kind).codec.encode narrowed.payload.logical,
      CanonicalAccountView.balanceStream.encode
        (ResourceObservationAdmission.narrowBalances fields balances)⟩

structure PreparedBend (command : Command) where
  private mk ::
  claim : BendExecutionClaim.Claim
  claimExact : command.bend = some claim
  artifact : BendWorldProgramCodec.Artifact
  observations : List BendNativeInput.Observation
  source : BendNativeRun.Checked artifact claim observations
  workFits : source.source.sourceCount ≤ claim.capacity.proofWork

/-- The complete source result is retained internally for the pinned typed
Plan/Surface/Card decoder at actual native admission. No source count appears
in signed public receipts, and no source diagnostic is returned here. -/
def checkCommandBend {F : Type} [Field F] [DecidableEq F] {durable : Durable}
    (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F)
    (context : ResourceObservationAdmission.Context deployment durable)
    (command : Command) (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (compute : Option (RunComputeBudgetDomain.Prepared deployment durable.snapshot command.subject)) :
    Except Reject (Option (PreparedBend command)) := do
  match selected : command.bend with
  | none => pure none
  | some claim =>
    if command.run.isSome then throw .bendExecution
    if BendNativeRun.evaluatorId ∈ profile.disabledEvaluators then throw .bendExecution
    let some sourceIndex := if h : claim.sourceIndex < command.targets.length then
        some (⟨claim.sourceIndex,h⟩ : Fin command.targets.length) else none
      | throw .bendExecution
    let target := command.targets[sourceIndex]
    if target.payload != .read then throw .bendExecution
    if ResourceObservationAdmission.readerFields context target.kind
        (target.observeCapability.getD ⟨0⟩) != none then throw .bendExecution
    let some store := target.contentStore? (materialize target.materializer (pre sourceIndex))
      | throw .bendExecution
    let some artifact := BendArtifactSource.lookup store ⟨claim.sourceAtom⟩ | throw .bendExecution
    let some observations := bendObservations context command claim.sourceIndex compute
      | throw .bendExecution
    let source ← (BendNativeRun.check artifact claim observations).mapError (fun _ => Reject.bendExecution)
    if work : source.source.sourceCount ≤ claim.capacity.proofWork then
      pure (some ⟨claim,selected,artifact,observations,source,work⟩)
    else throw .bendExecution

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
  /-- Every transclusion's opening holds on its source read, at this height. -/
  openings : openingsCheck command (fun j => command.targets[j].contentStore? (targets j).pre) = true
  marker : MarkerMode authority.snapshot profile.semantics command
  compute : Option (RunComputeBudgetDomain.Prepared deployment durable.snapshot command.subject)
  computeChecked : prepareCompute deployment durable.snapshot clock.clock command = .ok compute
  money : Option (ResourceMoneyReceiver.Prepared deployment durable.snapshot (moneyEntries command))
  moneyChecked : prepareMoney deployment durable.snapshot command compute = .ok money
  /-- The re-executed run, when the command claims one. -/
  run : Option CheckedRun
  runChecked : checkCommandRun profile.disabledEvaluators deployment.domain directory.directory
    ambient command (fun i => (targets i).pre.logical) (computeFundingIndex compute) = .ok run
  bend : Option (PreparedBend command)
  bendChecked : checkCommandBend deployment profile ⟨directory,authority⟩ command
    (fun i => (targets i).pre.logical) compute = .ok bend
  computeRunExact : computeExecutionMatches command compute run = true

/-- The accounting plan's amount is tied to the actual accepted oracle count. -/
theorem PreparedInvocation.compute_steps_exact {F : Type} [Field F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (compute : RunComputeBudgetDomain.Prepared deployment durable.snapshot command.subject)
    (run : CheckedRun) (hasCompute : prepared.compute = some compute)
    (hasRun : prepared.run = some run) : compute.steps = run.verdict.steps := by
  have exact := prepared.computeRunExact
  cases selected : command.bend with
  | none => simpa [computeExecutionMatches, selected, hasCompute, hasRun, computeRunMatches] using exact
  | some claim => simp [computeExecutionMatches, selected, hasCompute, hasRun, computeRunMatches] at exact

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
      if openings : openingsCheck command
          (fun j => command.targets[j].contentStore? (targets j).pre) = true then
        let marker ← prepareMarker authority.snapshot profile.semantics command
        match computeChecked : prepareCompute deployment durable.snapshot clock.clock command with
        | .error reason => .error reason
        | .ok compute =>
          match checked : checkCommandRun profile.disabledEvaluators deployment.domain directory.directory ambient command
              (fun i => (targets i).pre.logical) (computeFundingIndex compute) with
          | .error reason => .error reason
          | .ok run =>
            match bendChecked : checkCommandBend deployment profile ⟨directory,authority⟩ command
                (fun i => (targets i).pre.logical) compute with
            | .error reason => .error reason
            | .ok bend =>
              if computeRunExact : computeExecutionMatches command compute run = true then
                match moneyChecked : prepareMoney deployment durable.snapshot command compute with
                | .error reason => .error reason
                | .ok money =>
                  .ok ⟨nonempty, distinct, directory, authority, clock, targets, openings, marker,
                    compute, computeChecked, money, moneyChecked, run, checked, bend, bendChecked, computeRunExact⟩
              else .error .computeFunding
      else .error (.content .staleOpening)
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
    {validatedFundingIndex : Option Nat}
    {directory : Directory Nat Registry} {ambient : Ambient}
    {command : Command} {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    (unclaimed : command.run = none) :
    checkCommandRun disabled domain directory ambient command pre validatedFundingIndex = .ok none := by
  unfold checkCommandRun; rw [unclaimed]

/-- What an accepted `checkProgram` ran: a gate's `checkRun` on its evaluator and the
kernel's sample, or a door's `checkPoke` with the evaluator's door on target 0's stored view. -/
def ProgramAccepted (E : Evaluator) (program : NockProgramCodec.Program)
    (libraries : List NockProgramCodec.Program)
    (ambient : Ambient) (command : Command)
    (pre : (i : Fin command.targets.length) → Store command.targets[i].layout)
    (claim : Run.RunClaim) (writes : List Eval.FieldWrite) (verdict : Run.Accepted)
    (validatedFundingIndex : Option Nat := none) : Prop :=
  match program.abi.door with
  | none => ∃ sample v, E.sampleOf program.abi (runContext ambient command)
      (programTargets command validatedFundingIndex) (programSampleRead command pre validatedFundingIndex) = some sample ∧
      Run.checkRun E.toMachine program libraries sample claim writes = .ok v ∧
      Run.Verdict.erase E.toMachine v = verdict
  | some door => ∃ d view v, E.door = some d ∧
      Door.viewOf door (programSampleRead command pre validatedFundingIndex) = .ok view ∧
      Door.checkPoke E.toMachine d program door view claim writes = .ok v ∧
      Run.Verdict.erase E.toMachine v = verdict

theorem checkProgram_sound {E : Evaluator} {program : NockProgramCodec.Program}
    {validatedFundingIndex : Option Nat}
    {libraries : List NockProgramCodec.Program} {ambient : Ambient} {command : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} {writes : List Eval.FieldWrite} {verdict : Run.Accepted}
    (accepted : checkProgram E program libraries ambient command pre claim writes validatedFundingIndex = .ok verdict) :
    ProgramAccepted E program libraries ambient command pre claim writes verdict validatedFundingIndex := by
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
    {validatedFundingIndex : Option Nat}
    {libraries : List NockProgramCodec.Program} {ambient : Ambient} {command : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} {writes : List Eval.FieldWrite} {slot : NockProgramCodec.SampleSlot}
    (gate : program.abi.door = none)
    (above : E.overMax (programSampleRead command pre validatedFundingIndex) program.abi.sample = some slot) :
    checkProgram E program libraries ambient command pre claim writes validatedFundingIndex = .error .fieldOverMax := by
  unfold checkProgram
  rw [gate]
  simp only [above]

/-- **`checkClaim_sound`**: an accepted run check loaded the claimed program, resolved
its evaluator to a compiled-in, enabled entry, loaded its libraries (on that
evaluator) from the directory, and re-executed it against the loaded pre-states: a
gate on the kernel's own sample (`Run.checkRun`), a door on target 0's stored state
(`Door.checkPoke` with the evaluator's door), accepting the command's writes. -/
theorem checkClaim_sound {disabled : List Digest} {domain : Digest}
    {validatedFundingIndex : Option Nat}
    {directory : Directory Nat Registry} {ambient : Ambient}
    {command : Command} {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} {checked : CheckedRun}
    (accepted : checkClaim disabled domain directory ambient command pre claim validatedFundingIndex = .ok checked) :
    ∃ program E libraries writes,
      checked.claim = claim ∧
      CanonicalCellRegistry.loadProgram domain directory checked.claim.programId = some program ∧
      Run.resolve disabled program.evaluator = .ok E ∧ checked.evaluator = E.id ∧
      program.abi.libraries.mapM (fun library => Run.require .libraryUnknown
        (CanonicalCellRegistry.loadProgram domain directory library)) = .ok libraries ∧
      Run.librariesAgree program libraries = true ∧
      commandWrites command pre claim.programId validatedFundingIndex = some writes ∧
      checked.fuel = program.abi.fuel ∧
      ProgramAccepted E program libraries ambient command pre checked.claim writes
        checked.verdict validatedFundingIndex := by
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
        cases hwrites : commandWrites command pre claim.programId validatedFundingIndex with
        | none => intro accepted; cases accepted
        | some writes =>
          intro accepted
          simp only [Run.require_some] at accepted
          revert accepted
          cases hrun : checkProgram E program libraries ambient command pre claim writes validatedFundingIndex with
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
    {validatedFundingIndex : Option Nat}
    {directory : Directory Nat Registry} {ambient : Ambient}
    {command : Command} {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} {program : NockProgramCodec.Program}
    (stored : CanonicalCellRegistry.loadProgram domain directory claim.programId = some program)
    (absent : ∀ E ∈ Evaluator.registry, E.id ≠ program.evaluator) :
    checkClaim disabled domain directory ambient command pre claim validatedFundingIndex = .error .unknownEvaluator := by
  unfold checkClaim
  rw [stored]
  simp only
  rw [Run.resolve_unknown absent]

/-- **`checkCommandRun_sound`**: a checked run in a prepared invocation is the
command's own claim, accepted by `checkClaim`. -/
theorem checkCommandRun_sound {disabled : List Digest} {domain : Digest}
    {validatedFundingIndex : Option Nat}
    {directory : Directory Nat Registry} {ambient : Ambient}
    {command : Command} {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {checked : CheckedRun}
    (accepted : checkCommandRun disabled domain directory ambient command pre validatedFundingIndex = .ok (some checked)) :
    command.run = some checked.claim ∧
      checkClaim disabled domain directory ambient command pre checked.claim validatedFundingIndex = .ok checked := by
  unfold checkCommandRun at accepted
  cases hclaim : command.run with
  | none => rw [hclaim] at accepted; cases accepted
  | some claim =>
    rw [hclaim] at accepted
    cases hc : checkClaim disabled domain directory ambient command pre claim validatedFundingIndex with
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
    {validatedFundingIndex : Option Nat}
    {directory : Directory Nat Registry}
    {ambient : Ambient} {command : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} (claimed : command.run = some claim) :
    checkCommandRun disabled domain directory ambient command pre validatedFundingIndex ≠ .ok none := by
  unfold checkCommandRun
  rw [claimed]
  cases h : checkClaim disabled domain directory ambient command pre claim validatedFundingIndex <;>
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
      commandWrites command (fun i => (prepared.targets i).pre.logical) claim.programId
        (computeFundingIndex prepared.compute) = some writes ∧
      ProgramAccepted E program libraries ambient command (fun i => (prepared.targets i).pre.logical)
        claim writes checked.verdict (computeFundingIndex prepared.compute) := by
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
    {validatedFundingIndex : Option Nat}
    {libraries : List NockProgramCodec.Program} {ambient ambient' : Ambient}
    {command command' : Command} {validatedFundingIndex' : Option Nat}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {pre' : (i : Fin command'.targets.length) → Store command'.targets[i].layout}
    {claim : Run.RunClaim} {writes : List Eval.FieldWrite} {verdict : Run.Accepted}
    (gate : program.abi.door = none) (pinned : program.abi.context = .pinned)
    (sameTargets : programTargets command' validatedFundingIndex' = programTargets command validatedFundingIndex)
    (unchanged : ∀ slot ∈ program.abi.sample,
      programSampleRead command' pre' validatedFundingIndex' slot.target slot.slot = programSampleRead command pre validatedFundingIndex slot.target slot.slot)
    (accepted : checkProgram E program libraries ambient command pre claim writes validatedFundingIndex = .ok verdict) :
    checkProgram E program libraries ambient' command' pre' claim writes validatedFundingIndex' = .ok verdict := by
  have same : E.sampleOf program.abi (runContext ambient' command')
      (programTargets command' validatedFundingIndex') (programSampleRead command' pre' validatedFundingIndex') =
      E.sampleOf program.abi (runContext ambient command)
      (programTargets command validatedFundingIndex) (programSampleRead command pre validatedFundingIndex) := by
    rw [sameTargets]
    exact E.sampleOf_pinned_of_fields pinned _ _ _ unchanged
  have hmax : E.overMax (programSampleRead command' pre' validatedFundingIndex') program.abi.sample =
      E.overMax (programSampleRead command pre validatedFundingIndex) program.abi.sample := E.overMax_congr unchanged
  unfold checkProgram at accepted ⊢
  rw [gate] at accepted ⊢
  simp only at accepted ⊢
  rw [hmax, same]
  exact accepted

/-- **`pinned_claim_stale_on_field_change`** (at the controller): once exactly
one named slot of a pinned gate moved, the claim the kernel accepted before
refuses `sampleStale` naming that slot's key, at any height. -/
theorem pinned_claim_stale_on_field_change {E : Evaluator} {program : NockProgramCodec.Program}
    {validatedFundingIndex : Option Nat}
    {libraries : List NockProgramCodec.Program} {ambient ambient' : Ambient}
    {command command' : Command} {validatedFundingIndex' : Option Nat}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {pre' : (i : Fin command'.targets.length) → Store command'.targets[i].layout}
    {claim : Run.RunClaim} {writes writes' : List Eval.FieldWrite}
    {verdict : Run.Accepted} {slot : NockProgramCodec.SampleSlot} {sample' : E.Input}
    (gate : program.abi.door = none) (pinned : program.abi.context = .pinned)
    (sameTargets : programTargets command' validatedFundingIndex' = programTargets command validatedFundingIndex)
    (accepted : checkProgram E program libraries ambient command pre claim writes validatedFundingIndex = .ok verdict)
    (current : E.sampleOf program.abi (runContext ambient' command')
      (programTargets command' validatedFundingIndex') (programSampleRead command' pre' validatedFundingIndex') = some sample')
    (named : slot ∈ program.abi.sample)
    (changed : programSampleRead command pre validatedFundingIndex slot.target slot.slot ≠
      programSampleRead command' pre' validatedFundingIndex' slot.target slot.slot)
    (only : ∀ s ∈ program.abi.sample, s ≠ slot →
      programSampleRead command pre validatedFundingIndex s.target s.slot = programSampleRead command' pre' validatedFundingIndex' s.target s.slot) :
    checkProgram E program libraries ambient' command' pre' claim writes' validatedFundingIndex' =
      .error (.sampleStale (some slot.key)) := by
  have sound := checkProgram_sound accepted
  unfold ProgramAccepted at sound
  rw [gate] at sound
  obtain ⟨sample, v, hsample, ran, -⟩ := sound
  obtain ⟨-, -, -, -, -, computed, -⟩ := Run.checkRun_sound ran
  have under : E.overMax (programSampleRead command' pre' validatedFundingIndex') program.abi.sample = none := by
    cases hs : E.overMax (programSampleRead command' pre' validatedFundingIndex') program.abi.sample with
    | none => rfl
    | some s =>
      have refused : E.sampleOf program.abi (runContext ambient' command')
          (programTargets command' validatedFundingIndex') (programSampleRead command' pre' validatedFundingIndex') = none :=
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
    {validatedFundingIndex : Option Nat}
    {libraries : List NockProgramCodec.Program} {ambient : Ambient} {command : Command}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {claim : Run.RunClaim} {writes : List Eval.FieldWrite} {slot : NockProgramCodec.SampleSlot}
    (gate : program.abi.door = none)
    (above : NockProgramCell.overMax (programSampleRead command pre validatedFundingIndex) program.abi.sample = some slot) :
    checkProgram Evaluator.nock program libraries ambient command pre claim writes validatedFundingIndex =
      .error .fieldOverMax :=
  DeclaredResourceController.checkProgram_fieldOverMax (E := Evaluator.nock) gate above

theorem pinned_claim_admissible_across_heights {program : NockProgramCodec.Program}
    {validatedFundingIndex : Option Nat}
    {libraries : List NockProgramCodec.Program} {ambient ambient' : Ambient}
    {command command' : Command} {validatedFundingIndex' : Option Nat}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {pre' : (i : Fin command'.targets.length) → Store command'.targets[i].layout}
    {claim : Run.RunClaim} {writes : List Eval.FieldWrite} {verdict : Run.Accepted}
    (gate : program.abi.door = none) (pinned : program.abi.context = .pinned)
    (sameTargets : programTargets command' validatedFundingIndex' = programTargets command validatedFundingIndex)
    (unchanged : ∀ slot ∈ program.abi.sample,
      programSampleRead command' pre' validatedFundingIndex' slot.target slot.slot = programSampleRead command pre validatedFundingIndex slot.target slot.slot)
    (accepted : checkProgram Evaluator.nock program libraries ambient command pre claim writes validatedFundingIndex =
      .ok verdict) :
    checkProgram Evaluator.nock program libraries ambient' command' pre' claim writes validatedFundingIndex' = .ok verdict :=
  DeclaredResourceController.pinned_claim_admissible_across_heights gate pinned sameTargets
    unchanged accepted

theorem pinned_claim_stale_on_field_change {program : NockProgramCodec.Program}
    {validatedFundingIndex : Option Nat}
    {libraries : List NockProgramCodec.Program} {ambient ambient' : Ambient}
    {command command' : Command} {validatedFundingIndex' : Option Nat}
    {pre : (i : Fin command.targets.length) → Store command.targets[i].layout}
    {pre' : (i : Fin command'.targets.length) → Store command'.targets[i].layout}
    {claim : Run.RunClaim} {writes writes' : List Eval.FieldWrite}
    {verdict : Run.Accepted} {slot : NockProgramCodec.SampleSlot} {sample' : Noun}
    (gate : program.abi.door = none) (pinned : program.abi.context = .pinned)
    (sameTargets : programTargets command' validatedFundingIndex' = programTargets command validatedFundingIndex)
    (accepted : checkProgram Evaluator.nock program libraries ambient command pre claim writes validatedFundingIndex =
      .ok verdict)
    (current : NockProgramCell.sampleOf program.abi (runContext ambient' command')
      (programTargets command' validatedFundingIndex') (programSampleRead command' pre' validatedFundingIndex') = some sample')
    (named : slot ∈ program.abi.sample)
    (changed : programSampleRead command pre validatedFundingIndex slot.target slot.slot ≠
      programSampleRead command' pre' validatedFundingIndex' slot.target slot.slot)
    (only : ∀ s ∈ program.abi.sample, s ≠ slot →
      programSampleRead command pre validatedFundingIndex s.target s.slot = programSampleRead command' pre' validatedFundingIndex' s.target s.slot) :
    checkProgram Evaluator.nock program libraries ambient' command' pre' claim writes' validatedFundingIndex' =
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
