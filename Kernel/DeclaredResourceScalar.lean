/- Scalar action lowering used by the joint resource receiver. This module has no signed ingress or durable receiving path. Its command is an internal projection of one scalar target; joint authority and policy are checked only by DeclaredResourceController.

The target is a declared-effect cell (`Compiler.DeclaredEffectCell`): a store over `effectLayout`. Preparation validates the command's own guarded patch against the cell at the quoted root and runs it; the post is `Patch.run`. There is no page, no shard, no capacity: the reject reasons `invalidPage`, `pageMutation` (with its `overflow`/`unsupportedAddress`) and `pageValidation` are removed, and a failed guard is `guardRejected i`, naming the first disabled operation. -/
import Compiler.CredentialAuthorityDomainReceiver
import Compiler.CredentialAuthorityPolicyRegistry
import Compiler.CredentialAuthorityReplay
import Compiler.DeclaredEffectCell
import Compiler.CanonicalRuntimeProfile
import Kernel.MultiCellHyperedge
import Kernel.ResourceBirthController
import Kernel.DeclaredResourceProjection

namespace Minidregg.Kernel.DeclaredResourceScalar

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.DeclaredEffectCell (stateKeyStream)
open Minidregg.Compiler.IntStream (intStream)
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.EffectDeclaration (effectLayout StateKey)
open Minidregg.Theory.Store
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev EffectCell := DeclaredEffectCell.Cell
abbrev AuthoritySnapshot := CredentialAuthorityDomain.Snapshot

/-! ## One compact transport for the existing action syntax -/

abbrev CreateWire := EffectDeclaration.StateKey × Int
abbrev WriteWire := EffectDeclaration.StateKey × Option Int × Int
abbrev MoveWire := ResourceId .account × ResourceId .account × Digest ×
  Option Int × Option Int × Int
abbrev ActionWire := Sum CreateWire (Sum WriteWire MoveWire)

def actionWireStream : StreamCodec ActionWire :=
  StreamCodec.sum
    (StreamCodec.product stateKeyStream intStream)
    (StreamCodec.sum
      (StreamCodec.product stateKeyStream
        (StreamCodec.product (StreamCodec.option intStream) intStream))
      (StreamCodec.product (TypedAuthorizationRequestCodec.resourceIdStream .account)
        (StreamCodec.product (TypedAuthorizationRequestCodec.resourceIdStream .account)
          (StreamCodec.product digestStream
            (StreamCodec.product (StreamCodec.option intStream)
              (StreamCodec.product (StreamCodec.option intStream) intStream))))))

def actionWire : Action → ActionWire
  | .create key initial => .inl (key, initial)
  | .write key expected replacement => .inr (.inl (key, expected, replacement))
  | .move source destination resource expectedSource expectedDestination amount =>
      .inr (.inr (source, destination, resource, expectedSource, expectedDestination, amount))

def actionOfWire : ActionWire → Action
  | .inl (key, initial) => .create key initial
  | .inr (.inl (key, expected, replacement)) => .write key expected replacement
  | .inr (.inr (source, destination, resource, expectedSource, expectedDestination, amount)) =>
      .move source destination resource expectedSource expectedDestination amount

@[simp] theorem actionOfWire_wire (action : Action) : actionOfWire (actionWire action) = action := by
  cases action <;> rfl

def actionStream : StreamCodec Action :=
  StreamCodec.xmap actionWireStream actionWire actionOfWire actionOfWire_wire

/-- The caller chooses an operation and expected versions, never its policy,
authority projection, proposed post, or independently supplied effect digest.
The native signing envelopes are separate proofs over source-derived requests.
`kind` and `target` are literal command coordinates, retained in its digest. -/
structure Command where
  kind : ResourceKind
  target : Nat
  subject : SubjectId
  capability : CapabilityId
  schemaVersion : Nat
  expectedTargetRoot : Digest
  nonce : Nat
  actions : List Action
  deriving DecidableEq, Repr

abbrev CommandWire := ResourceKind × Nat × SubjectId × CapabilityId ×
  Nat × Digest × Nat × List Action

def commandWireStream : StreamCodec CommandWire :=
  StreamCodec.product ResourceBirthCodec.resourceKindStream
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product digestStream
              (StreamCodec.product StreamCodec.nat (StreamCodec.list actionStream)))))))

def Command.toWire (command : Command) : CommandWire :=
  (command.kind, command.target, command.subject, command.capability,
    command.schemaVersion, command.expectedTargetRoot, command.nonce, command.actions)

def Command.ofWire : CommandWire → Command
  | (kind, target, subject, capability, version, targetRoot, nonce, actions) =>
      ⟨kind, target, subject, capability, version, targetRoot, nonce, actions⟩

@[simp] theorem Command.ofWire_toWire (command : Command) :
    Command.ofWire command.toWire = command := by cases command; rfl

def commandStream : StreamCodec Command :=
  StreamCodec.xmap commandWireStream Command.toWire Command.ofWire Command.ofWire_toWire

/-- Version 2: the command carries no authority root (`Theory.PlanBinding`). -/
def commandFrame : List UInt8 := "DREGG/RESOURCE/INVOKE".toUTF8.toList ++ [2]

def rawCommandCodec : LawfulCodec Command where
  encode command := commandFrame ++ commandStream.encode command
  decode bytes :=
    if bytes.take commandFrame.length = commandFrame then
      commandStream.toLawful.decode (bytes.drop commandFrame.length)
    else none
  decode_encode := by
    intro command
    have decoded := commandStream.toLawful.decode_encode command
    change commandStream.toLawful.decode (commandStream.encode command) = some command at decoded
    simp [decoded]

def commandCodec : LawfulCodec Command := ResourceBirthCodec.strictCodec rawCommandCodec

@[simp] theorem command_decode_encode (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_decode_canonical {bytes : List UInt8} {command : Command}
    (decoded : commandCodec.decode bytes = some command) :
    commandCodec.encode command = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCommandCodec decoded

def Command.declaration (command : Command) :
    DeclaredActionLowering.Declaration (⟨command.target⟩ : ResourceId command.kind) :=
  ⟨command.schemaVersion, command.expectedTargetRoot, command.nonce, command.actions⟩

/-- The full command is included in every incidence's source commitment.
Domain and receiver semantics are source-owned deployment coordinates. -/
def commandBytes (domain semantics : Digest) (command : Command) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
    (domain, semantics, commandCodec.encode command)

def argsDigest (domain semantics : Digest) (command : Command) : Digest :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.INVOKE.ARGS/v1".toUTF8.toList
    (commandBytes domain semantics command)).digest

def effectsDigest (domain semantics : Digest) (command : Command) : Digest :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.INVOKE.EFFECT/v1".toUTF8.toList
    (commandBytes domain semantics command)).digest

def operationMarker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.INVOKE.NULLIFIER/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product ResourceBirthCodec.resourceKindStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream StreamCodec.nat))))).encode
      (domain, semantics, command.kind, command.target, command.subject, command.nonce))).digest.value

def ordinaryVerb : (kind : ResourceKind) → Verb kind
  | .object => .mutateObject
  | .account => .transfer
  | .program => .installProgram

/-- Trusted ambient inputs are not read from an incoming command. The shared
runtime compiler profile supplies `semantics`; no per-operation policy profile
is invented by this controller. The caller's height is the receiver clock. -/
structure Ambient where
  federation : FederationId
  height : Height

def request (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (preRoot : Digest) : Request command.kind where
  domain := snapshot.domain
  semantics := semantics
  federation := ambient.federation
  subject := command.subject
  subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
  target := ⟨command.target⟩
  verb := ordinaryVerb command.kind
  argsDigest := argsDigest snapshot.domain semantics command
  effectsDigest := effectsDigest snapshot.domain semantics command
  nonce := command.nonce
  height := ambient.height
  preStateRoot := preRoot
  policyId := ⟨command.target⟩
  policyEpoch := snapshot.authState.policyEpoch ⟨command.target⟩
  policyRevision := snapshot.authState.policyRevision ⟨command.target⟩
  cost := (commandCodec.encode command).length

theorem request_policy_is_target (snapshot : AuthoritySnapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) (preRoot : Digest) :
    (request snapshot semantics ambient command preRoot).policyId = ⟨command.target⟩ := rfl

theorem ordinary_program_verb_distinct : ordinaryVerb .program ≠ .installPolicy := by decide

/-! ## Source-owned cell preparation, before portals or authorization -/

inductive Reject where
  | malformedCommand
  | unsupportedVersion
  | accountRequiresBook
  | emptyActions
  | wrongRole
  | missingTarget
  | staleTarget
  | staleAuthority
  | inadmissibleAction
  | guardRejected (index : Nat)
  | invalidPost
  | authorityUnavailable
  | directoryUnavailable
  | nullifierUsed
  | authorityPreparation
  | physicalPreparation
  | policyUnavailable
  | signature (reason : CredentialSignatureAdmission.Reject)
  | capabilityRejected
  | policyRejected
  | policyInputRange
  | policyCastAlias
  | conflictingIncidences
  deriving Repr

def requireSome {α : Type} (reason : Reject) : Option α → Except Reject α
  | none => .error reason
  | some value => .ok value

def packDeclared (kind : ResourceKind) (payload : EffectCell) : PackedCell Registry :=
  match kind with
  | .object => ⟨.declaredObject, payload⟩
  | .account => ⟨.accountMetadata, payload⟩
  | .program => ⟨.declaredProgram, payload⟩

/-- The command's one guarded patch.  It is the declaration's own lowering,
not a whole-cell replacement computed beside it. -/
def cellPatch (command : Command) : Patch effectLayout :=
  command.declaration.patch

/-- The guard relation is the existing sequential action semantics, with
exact sparse presence. It says nothing about an unrelated host proposal. -/
def CanonicalActionResult (pre : EffectCell) (command : Command)
    (post : Store effectLayout) : Prop :=
  command.declaration.run pre.logical = some post

structure CellMode (pre : EffectCell) (command : Command) (post : Store effectLayout) : Type where
  beforeLaw : CanonicalCellRegistry.DeclaredCellLaw command.kind command.target pre.logical
  rootExact : command.expectedTargetRoot = pre.root
  versionExact : command.schemaVersion = 1
  ordinary : command.kind ≠ .account
  actionsPresent : command.actions ≠ []
  admitted : command.declaration.Admitted
  postLaw : CanonicalCellRegistry.DeclaredCellLaw command.kind command.target post
  semanticsExact : CanonicalActionResult pre command post

def cellFamily (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (pre : EffectCell) :
    SemanticEffectFamily effectLayout DeclaredEffectCell.materializer Nat where
  Declaration := Command
  declarationCodec := commandCodec
  pre := pre
  request := fun command => ⟨command.kind, request snapshot semantics ambient command pre.root⟩
  Outcome := fun _ => Store effectLayout
  outcomeCodec := fun _ => DeclaredEffectCell.materializer.codec
  ModeEvidence := fun command post => CellMode pre command post
  Postcondition := fun command post logical =>
    logical = post ∧ CanonicalActionResult pre command post ∧
      CanonicalCellRegistry.DeclaredCellLaw command.kind command.target post
  effectDigest := effectsDigest snapshot.domain semantics
  patch := fun command _ => cellPatch command
  nullifier := fun _ _ => none
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ decision => decision = .sealed

/-- Computation precedes policy admission. The retained candidate has no
authorization token; a requester cannot construct it by supplying a post. -/
structure PreparedCell (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (pre : EffectCell) (command : Command) where
  private mk ::
  post : Store effectLayout
  candidate : PolicyInstall.Candidate (cellFamily snapshot semantics ambient pre)
    pre command post

def prepareCell (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (pre : EffectCell) (command : Command) :
    Except Reject (PreparedCell snapshot semantics ambient pre command) := do
  if ordinary : command.kind ≠ .account then
    if version : command.schemaVersion = 1 then
      if nonempty : command.actions ≠ [] then
        if root : command.expectedTargetRoot = pre.root then
          if preLaw : CanonicalCellRegistry.DeclaredCellLaw command.kind command.target
              pre.logical then
            if admitted : command.declaration.admissionCheck = true then
              match validate DeclaredEffectCell.materializer pre
                  pre.root (cellPatch command) with
              | .rejected (.stalePreRoot) => .error .staleTarget
              | .rejected (.disabledOperation index) => .error (.guardRejected index)
              | .accepted validated =>
                  let post := Patch.run pre.logical (cellPatch command)
                  if postLaw : CanonicalCellRegistry.DeclaredCellLaw command.kind
                      command.target post then
                    let semantic : CanonicalActionResult pre command post :=
                      (command.declaration.run_eq_some_iff _ _).mpr
                        ⟨admitted, validated.valid, rfl⟩
                    .ok ⟨post,
                      { preStateBound := rfl
                        modeEvidence :=
                          ⟨preLaw, root, version, ordinary, nonempty, admitted, postLaw,
                            semantic⟩
                        validated := validated
                        postcondition := ⟨rfl, semantic, postLaw⟩ }⟩
                  else .error .invalidPost
            else .error .inadmissibleAction
          else .error .wrongRole
        else .error .staleTarget
      else .error .emptyActions
    else .error .unsupportedVersion
  else .error .accountRequiresBook

theorem PreparedCell.action_semantics_exact
    {snapshot : AuthoritySnapshot} {semantics : Digest} {ambient : Ambient}
    {pre : EffectCell} {command : Command}
    (prepared : PreparedCell snapshot semantics ambient pre command) :
    CanonicalActionResult pre command prepared.post :=
  prepared.candidate.postcondition.2.1


end Minidregg.Kernel.DeclaredResourceScalar
