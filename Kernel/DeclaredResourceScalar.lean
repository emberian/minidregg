/- Scalar action lowering used by the joint resource receiver. This module has no signed ingress or durable receiving path. Its command is an internal projection of one scalar target; joint authority and policy are checked only by DeclaredResourceController.

The target is a declared-effect cell (`Compiler.DeclaredEffectCell`): a store over `effectLayout`. Preparation validates the command's own guarded patch against the cell at the quoted root and runs it; the post is `Patch.run`. There is no page, no shard, no capacity: the reject reasons `invalidPage`, `pageMutation` (with its `overflow`/`unsupportedAddress`) and `pageValidation` are removed, and a failed guard is `guardRejected i`, naming the first disabled operation. -/
module

public import Compiler.CredentialAuthorityDomainReceiver
public import Compiler.CredentialAuthorityPolicyRegistry
public import Compiler.CredentialAuthorityReplay
public import Compiler.DeclaredEffectCell
public import Compiler.CanonicalRuntimeProfileCore
public import Kernel.MultiCellHyperedge
public import Kernel.ResourceBirthController
public import Kernel.DeclaredResourceProjection

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

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

def commandCodec : LawfulCodec Command := (StreamCodec.framed commandFrame commandStream).toLawful

@[simp] theorem command_decode_encode (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_decode_canonical {bytes : List UInt8} {command : Command}
    (decoded : commandCodec.decode bytes = some command) :
    commandCodec.encode command = bytes :=
  StreamCodec.toLawful_canonical _ _ _ decoded

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
  /-- K-FIELD-CLOSURE: the write changed field `field`, which the cell did not
  declare at birth (`FieldClosure.check`). -/
  | undeclaredField (field : Nat)
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
  /-- Every field the write changed is one the cell declares (K-FIELD-CLOSURE). -/
  closed : FieldClosure.check command.target pre.logical post = none
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

/-- The actions' one guarded patch. A command's patch is this, whatever its schema version,
expected root and nonce (`cellPatch_actions`). -/
def actionsPatch (actions : List Action) : Patch effectLayout :=
  actions.flatMap Action.ops

theorem cellPatch_actions (command : Command) : cellPatch command = actionsPatch command.actions := rfl

/-- **The root-free core of a scalar preparation**: what the actions do to a store under a role
and a cell id, with no schema version, expected root, signer or nonce. The role's cell law at
the loaded store, the scoped admission of every action, every guard in sequence, field closure
(K-FIELD-CLOSURE: a field the cell did not declare is refused by name, before any law is
evaluated), then the cell law at the post. It answers the actions' patch. -/
def prepareStore (kind : ResourceKind) (target : Nat) (actions : List Action)
    (store : Store effectLayout) : Except Reject (Patch effectLayout) :=
  if CanonicalCellRegistry.DeclaredCellLaw kind target store then
    if actions.all (Action.admissionCheck (⟨target⟩ : ResourceId kind)) = true then
      match Patch.firstDisabled? store (actionsPatch actions) with
      | some index => .error (.guardRejected index)
      | none =>
          match FieldClosure.check target store (Patch.run store (actionsPatch actions)) with
          | some field => .error (.undeclaredField field)
          | none =>
              if CanonicalCellRegistry.DeclaredCellLaw kind target
                  (Patch.run store (actionsPatch actions)) then .ok (actionsPatch actions)
              else .error .invalidPost
    else .error .inadmissibleAction
  else .error .wrongRole

/-- What an answered core says: the patch is the actions', the cell law holds before and after,
every action is admitted, every guard holds in sequence, and the write is closed. -/
theorem prepareStore_ok {kind : ResourceKind} {target : Nat} {actions : List Action}
    {store : Store effectLayout} {patch : Patch effectLayout}
    (answered : prepareStore kind target actions store = .ok patch) :
    patch = actionsPatch actions ∧
      CanonicalCellRegistry.DeclaredCellLaw kind target store ∧
      actions.all (Action.admissionCheck (⟨target⟩ : ResourceId kind)) = true ∧
      Patch.ValidFrom store (actionsPatch actions) ∧
      FieldClosure.check target store (Patch.run store (actionsPatch actions)) = none ∧
      CanonicalCellRegistry.DeclaredCellLaw kind target (Patch.run store (actionsPatch actions)) := by
  unfold prepareStore at answered
  split at answered
  · rename_i preLaw
    split at answered
    · rename_i admitted
      split at answered
      · cases answered
      · rename_i enabled
        split at answered
        · cases answered
        · rename_i closed
          split at answered
          · rename_i postLaw
            cases answered
            exact ⟨rfl, preLaw, admitted,
              (Patch.firstDisabled?_eq_none_iff store (actionsPatch actions)).1 enabled, closed,
              postLaw⟩
          · cases answered
    · cases answered
  · cases answered

/-- An answered core is the command's sequential action semantics at the loaded cell. -/
theorem prepareStore_semantic {pre : EffectCell} {command : Command} {patch : Patch effectLayout}
    (answered : prepareStore command.kind command.target command.actions pre.logical = .ok patch) :
    CanonicalActionResult pre command (Patch.run pre.logical (cellPatch command)) :=
  (command.declaration.run_eq_some_iff _ _).mpr
    ⟨(prepareStore_ok answered).2.2.1, (prepareStore_ok answered).2.2.2.1, rfl⟩

/-- No admitted action writes the blinding: no role's writable key is it (`writableKeyCheck`). -/
theorem admitted_writes_no_blinding {kind : ResourceKind} {target : ResourceId kind}
    (actions : List Action) (admitted : actions.all (Action.admissionCheck target) = true) :
    DeclaredEffectCell.blinding.address ∉ Patch.writeFootprint (actionsPatch actions) := by
  intro written
  rw [Patch.mem_writeFootprint_iff] at written
  obtain ⟨op, member, address⟩ := written
  obtain ⟨action, actionMember, opMember⟩ := List.mem_flatMap.mp member
  have actionAdmitted : action.admissionCheck target = true :=
    List.all_eq_true.mp admitted action actionMember
  have blinding : DeclaredEffectCell.blinding.address = EffectDeclaration.StateKey.blinding.address := rfl
  rw [blinding] at address
  cases action with
  | create key initial =>
    simp only [Action.ops, List.mem_singleton] at opMember
    subst opMember
    rw [guardedSet_address] at address
    have same := EffectDeclaration.StateKey.address_injective (Option.some.inj address)
    subst same
    cases kind <;> simp [Action.admissionCheck, writableKeyCheck] at actionAdmitted
  | write key expected replacement =>
    simp only [Action.ops, List.mem_singleton] at opMember
    subst opMember
    rw [guardedSet_address] at address
    have same := EffectDeclaration.StateKey.address_injective (Option.some.inj address)
    subst same
    cases kind <;> simp [Action.admissionCheck, writableKeyCheck] at actionAdmitted
  | move source destination resource sourceExpected destinationExpected amount =>
    simp only [Action.ops, List.mem_cons, List.not_mem_nil, or_false] at opMember
    rcases opMember with rfl | rfl <;>
    · rw [guardedSet_address] at address
      have same := EffectDeclaration.StateKey.address_injective (Option.some.inj address)
      cases same

/-- **An answered core replays with the kernel's ratchet** (K-HIDE-ROTATE): its patch leaves the
blinding where the loaded store has it, so the ratchet's guard at the pre blinding holds after
it, at every height. The leg's whole patch is valid from the loaded store. -/
theorem prepareStore_ratchet_valid {kind : ResourceKind} {target : Nat} {actions : List Action}
    {store : Store effectLayout} {patch : Patch effectLayout}
    (answered : prepareStore kind target actions store = .ok patch) (height : Nat) :
    Patch.ValidFrom store (patch ++ DeclaredEffectCell.blinding.patch store height) := by
  obtain ⟨same, _, admitted, valid, _, _⟩ := prepareStore_ok answered
  subst same
  have kept : Patch.run store (actionsPatch actions) DeclaredEffectCell.blinding.address =
      store DeclaredEffectCell.blinding.address :=
    Patch.run_frame _ _ _ (admitted_writes_no_blinding actions admitted)
  refine (Patch.validFrom_append _ _ _).2 ⟨valid, ?_⟩
  unfold StoreCodec.Blinding.patch
  split
  · rename_i value present
    refine ⟨⟨rfl, ?_⟩, trivial⟩
    change Patch.run store (actionsPatch actions) DeclaredEffectCell.blinding.address = some value
    rw [kept]
    exact present
  · trivial

/-- **A scalar preparation**: the command's own header (an ordinary role, schema version 1,
some action, the loaded root), then the root-free core (`prepareStore`) at the loaded store.
`prepareCell_factors` says so of its answer. -/
def prepareCell (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (pre : EffectCell) (command : Command) :
    Except Reject (PreparedCell snapshot semantics ambient pre command) := do
  if ordinary : command.kind ≠ .account then
    if version : command.schemaVersion = 1 then
      if nonempty : command.actions ≠ [] then
        if root : command.expectedTargetRoot = pre.root then
          match core : prepareStore command.kind command.target command.actions pre.logical with
          | .error reason => .error reason
          | .ok _ =>
              let post := Patch.run pre.logical (cellPatch command)
              .ok ⟨post,
                { preStateBound := rfl
                  modeEvidence :=
                    ⟨(prepareStore_ok core).2.1, root, version, ordinary, nonempty,
                      (prepareStore_ok core).2.2.1, (prepareStore_ok core).2.2.2.2.1,
                      (prepareStore_ok core).2.2.2.2.2, prepareStore_semantic core⟩
                  validated := (validate_accepts DeclaredEffectCell.materializer pre pre.root
                    (cellPatch command) rfl (prepareStore_ok core).2.2.2.1).elim fun found _ => found
                  postcondition :=
                    ⟨rfl, prepareStore_semantic core, (prepareStore_ok core).2.2.2.2.2⟩ }⟩
        else .error .staleTarget
      else .error .emptyActions
    else .error .unsupportedVersion
  else .error .accountRequiresBook

/-- **`prepareCell` is its header, then the root-free core.** The header reads the command's
role, schema version, action count and expected root; everything after it reads only the role,
the cell id, the actions and the loaded store. -/
theorem prepareCell_factors (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (pre : EffectCell) (command : Command) :
    (prepareCell snapshot semantics ambient pre command).map (·.post) =
      if command.kind = .account then .error .accountRequiresBook
      else if command.schemaVersion ≠ 1 then .error .unsupportedVersion
      else if command.actions = [] then .error .emptyActions
      else if command.expectedTargetRoot ≠ pre.root then .error .staleTarget
      else (prepareStore command.kind command.target command.actions pre.logical).map
        (Patch.run pre.logical) := by
  unfold prepareCell
  by_cases account : command.kind = .account
  · rw [dif_neg (not_not.mpr account), if_pos account]; rfl
  rw [dif_pos account, if_neg account]
  by_cases version : command.schemaVersion = 1
  swap
  · rw [dif_neg version, if_pos version]; rfl
  rw [dif_pos version, if_neg (not_not.mpr version)]
  by_cases empty : command.actions = []
  · rw [dif_neg (not_not.mpr empty), if_pos empty]; rfl
  rw [dif_pos empty, if_neg empty]
  by_cases root : command.expectedTargetRoot = pre.root
  swap
  · rw [dif_neg root, if_pos root]; rfl
  rw [dif_pos root, if_neg (not_not.mpr root)]
  split
  · rename_i reason core; rw [core]; rfl
  · rename_i patch core
    have answered : (prepareStore command.kind command.target command.actions pre.logical).map
        (Patch.run pre.logical) = .ok (Patch.run pre.logical (cellPatch command)) := by
      rw [core, (prepareStore_ok core).1]; rfl
    rw [answered]
    rfl

theorem PreparedCell.action_semantics_exact
    {snapshot : AuthoritySnapshot} {semantics : Digest} {ambient : Ambient}
    {pre : EffectCell} {command : Command}
    (prepared : PreparedCell snapshot semantics ambient pre command) :
    CanonicalActionResult pre command prepared.post :=
  prepared.candidate.postcondition.2.1

/-! ## K-FIELD-CLOSURE at the scalar receiver

Invoke's and grain birth's scalar targets are computed here
(`ResourceTransaction.computeTarget`), and preparation precedes every policy
evaluation (`DeclaredResourceController.authorizeLeg`), so a refusal here is
a refusal whatever the target's law says. -/

/-- **An accepted write changes only declared fields.** -/
theorem PreparedCell.changes_only_declared
    {snapshot : AuthoritySnapshot} {semantics : Digest} {ambient : Ambient}
    {pre : EffectCell} {command : Command}
    (prepared : PreparedCell snapshot semantics ambient pre command) (n : Nat)
    (changed : DeclaredResourceProjection.get (DeclaredResourceProjection.values command.target pre.logical) n ≠
      DeclaredResourceProjection.get (DeclaredResourceProjection.values command.target prepared.post) n) :
    FieldClosure.declaredIn command.target pre.logical n = true :=
  (FieldClosure.firstUndeclared_none_iff _ _ _).mp prepared.candidate.modeEvidence.closed n changed

/-- **An accepted write leaves the cell's declaration as it was.** -/
theorem PreparedCell.declaration_fixed
    {snapshot : AuthoritySnapshot} {semantics : Digest} {ambient : Ambient}
    {pre : EffectCell} {command : Command}
    (prepared : PreparedCell snapshot semantics ambient pre command) (n : Nat) :
    FieldClosure.declaredIn command.target prepared.post n =
      FieldClosure.declaredIn command.target pre.logical n := by
  obtain ⟨admitted, _, post⟩ := (command.declaration.run_eq_some_iff _ _).mp
    prepared.action_semantics_exact
  rw [post]
  exact FieldClosure.admitted_preserves_declared _ admitted _ _ n

/-- **`undeclared_field_refused`.** A write that changes a field its cell did not
declare is refused at preparation, naming the field, whatever the target's law
says: every earlier stage passing, the computed post naming `field` is enough. -/
theorem undeclared_field_refused
    {snapshot : AuthoritySnapshot} {semantics : Digest} {ambient : Ambient}
    {pre : EffectCell} {command : Command}
    (ordinary : command.kind ≠ .account) (version : command.schemaVersion = 1)
    (nonempty : command.actions ≠ []) (root : command.expectedTargetRoot = pre.root)
    (preLaw : CanonicalCellRegistry.DeclaredCellLaw command.kind command.target pre.logical)
    (admitted : command.declaration.admissionCheck = true)
    (enabled : Patch.firstDisabled? pre.logical (cellPatch command) = none)
    {field : Nat}
    (named : FieldClosure.check command.target pre.logical
      (Patch.run pre.logical (cellPatch command)) = some field) :
    prepareCell snapshot semantics ambient pre command = .error (.undeclaredField field) := by
  have core : prepareStore command.kind command.target command.actions pre.logical =
      .error (.undeclaredField field) := by
    unfold prepareStore
    rw [if_pos preLaw, if_pos (show command.actions.all
      (Action.admissionCheck (⟨command.target⟩ : ResourceId command.kind)) = true from admitted)]
    rw [show Patch.firstDisabled? pre.logical (actionsPatch command.actions) = none from enabled]
    dsimp only
    rw [show FieldClosure.check command.target pre.logical
      (Patch.run pre.logical (actionsPatch command.actions)) = some field from named]
  unfold prepareCell
  rw [dif_pos ordinary, dif_pos version, dif_pos nonempty, dif_pos root]
  split
  · rename_i reason found
    rw [core] at found
    cases found
    rfl
  · rename_i found
    rw [core] at found
    cases found

/-- info: 'Minidregg.Kernel.DeclaredResourceScalar.PreparedCell.changes_only_declared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedCell.changes_only_declared
/-- info: 'Minidregg.Kernel.DeclaredResourceScalar.PreparedCell.declaration_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedCell.declaration_fixed
/-- info: 'Minidregg.Kernel.DeclaredResourceScalar.undeclared_field_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms undeclared_field_refused


end Minidregg.Kernel.DeclaredResourceScalar
