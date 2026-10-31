/-
# `Kernel.ContentCommutingAppend` — appends to one document commute, STATED

The ruling of 2026-10-28 (qualification, composed scenario at load 45: five members appending
one line each to a room's notes exhausted the client's re-plans): append-only content commands
commute, and starving an appender is the bug.  This file states what the controller now does
for them and proves nothing; the witnesses' DATA is built here, their proofs follow the
statements auditor's read.

## What changed, and why it is safe

`computeTarget`'s content arm refused every command whose plan named a root other than the
loaded cell's (`staleTarget`).  A plan's signed bytes never carry that root
(`TypedAuthorizationRequestCodec.planOf` zeroes `preStateRoot` and `height`); the arm's
comparison against the command's own `expectedTargetRoot` was the only pin, and it pinned
the WHOLE cell.  A doc append (`ContentResource.Command.commutes`: nonempty, every action a
`createAtom`) reads nothing a concurrent append moves: its atom id is the author's fresh
draw, `appendLeaf` appends to the root's children and leaves the root's revision as it was,
and the content run is computed at the loaded cell in any case.  So the arm now pins the
root only for commands that do not commute.

What still holds for a commuting append, each by the existing code, not by this change:

* the post is computed at the cell it meets and validated at that cell's own root
  (`prepareTarget`: `validate target.materializer pre pre.root`);
* audience freshness is checked against the CURRENT policy source
  (`PreparedTarget.audienceFresh`, `ObjectAudience.checkFresh`), so a sealed line written
  under an audience epoch that has since rotated is refused;
* the read leg of a target with an observe capability is built at the loaded cell
  (`DeclaredResourceController.readRequest` takes `before.payload.root`, and
  `ResourceTargetAdmission.observe` compares it with that same cell), never at the signed
  root;
* replay: the command's operation marker is a durable nullifier.  An admitted invocation's
  data intent consumes it (`AdmittedConsumesMarker`), the durable engine never un-consumes a
  nullifier (`DurableEngineSuffix.consumed_install`), and on a ground where it is spent the
  same command never prepares (`ReplayRefused`), at every later state.  The root pin was
  never the replay guard.

## What is stated

* `CommutingAppend` (KEYSTONE, effect level): a commuting content command's computed
  outcome is the same at every planned root.
* `CommutingPrepare` (receiver level, the per-target preparation the invocation reads
  targets through): the same for `prepareTarget`, its post packed, its refusals alike.
* Teeth: `KeptPin` (every other content command is still refused `staleTarget` away from
  its planned root), `CommutesExactly` (the exemption is exactly nonempty `createAtom`
  lists), `AdmittedConsumesMarker` and `ReplayRefused` (a landed append never lands again).
* Satisfiable: `MovedRootAccepted` (an append planned over a root that is not the loaded
  cell's lands on a blinded document cell, its line is the document's, and the kernel's
  ratchet runs from the cell it met).
* Premise inhabitation: `TwoAppendersOneObservation` (two members plan from one
  observation; both land, in either order, each line once, in landing order).
* `CommutingPrepare`'s accepting pole is the Effects one over `ContentProofs.blindedStore`
  (`Kernel.EffectsRevival.Statements.HostMovedRootAccepted`, through `PrepareFactors`).

Scope, said in the same breath: per target, at the controller.  The Effects declaration of
the same arm (`Kernel.EffectsRevival.Statements.ContentAgreement`, `contentSpec.commutes`) states
the agreement and carries its own teeth (`ContentCommuteTeeth`).
-/
module

public import Kernel.DeclaredResourceController

@[expose] public section

namespace Minidregg.Kernel.ContentCommutingAppend

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController

set_option autoImplicit false

/-- A content target with its header. -/
abbrev contentTarget (kind : ResourceKind) (id : Nat) (capability : CapabilityId) (version : Nat)
    (root : Digest) (content : ContentResource.Command) (observe : Option CapabilityId)
    (epoch : Option Nat) (roster : Option ObjectAudienceRoster.Roster) : Target :=
  ⟨kind, id, capability, version, root, .content content, observe, epoch, roster⟩

/-! ## The keystone -/

/-- **KEYSTONE.**  A commuting content command is computed at the cell it meets: its outcome
(post or refusal) is the same whatever root its plan observed. -/
def CommutingAppend : Prop :=
  ∀ (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (id : Nat) (capability : CapabilityId) (version : Nat)
    (root root' : Digest) (content : ContentResource.Command) (observe : Option CapabilityId)
    (epoch : Option Nat) (roster : Option ObjectAudienceRoster.Roster)
    (pre : ContentResource.ContentCell),
    content.commutes = true →
    computeTarget snapshot semantics ambient command
        (contentTarget kind id capability version root content observe epoch roster) pre =
      computeTarget snapshot semantics ambient command
        (contentTarget kind id capability version root' content observe epoch roster) pre

/-- **The receiver's per-target preparation** reads the planned root only through
`computeTarget`: for a commuting command it is the same at every planned root (the packed
post on acceptance, the named refusal otherwise). -/
def CommutingPrepare : Prop :=
  ∀ (deployment : Deployment) (directory : CellRegistry.Directory Nat Registry)
    (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (id : Nat) (capability : CapabilityId) (version : Nat)
    (root root' : Digest) (content : ContentResource.Command) (observe : Option CapabilityId)
    (epoch : Option Nat) (roster : Option ObjectAudienceRoster.Roster),
    content.commutes = true →
    (prepareTarget deployment directory snapshot semantics ambient command
        (contentTarget kind id capability version root content observe epoch roster)).map
        (fun prepared => packTarget
          (contentTarget kind id capability version root content observe epoch roster)
          prepared.candidate.post) =
      (prepareTarget deployment directory snapshot semantics ambient command
        (contentTarget kind id capability version root' content observe epoch roster)).map
        (fun prepared => packTarget
          (contentTarget kind id capability version root' content observe epoch roster)
          prepared.candidate.post)

/-! ## Teeth -/

/-- **The pin is kept for everything else.**  A content command that does not commute,
planned over a root that is not the loaded cell's, is refused `staleTarget`. -/
def KeptPin : Prop :=
  ∀ (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (id : Nat) (capability : CapabilityId) (root : Digest) (content : ContentResource.Command)
    (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster) (pre : ContentResource.ContentCell),
    content.commutes = false → root ≠ pre.root →
    computeTarget snapshot semantics ambient command
        (contentTarget .object id capability ContentResource.commandVersion root content
          observe epoch roster) pre = .error .staleTarget

/-- **The exemption is exactly the append-only commands**: nonempty, every action a
`createAtom`.  An edit, a move, a transclusion, a section, a mark, or any mixture with
them, is not exempt. -/
def CommutesExactly : Prop :=
  ∀ content : ContentResource.Command, content.commutes = true ↔
    (content.actions ≠ [] ∧ ∀ action ∈ content.actions,
      ∃ atom kind payload, action = .createAtom atom kind payload)

/-- **An admitted invocation spends its operation marker.**  Its durable data intent carries
the marker's replay nullifier, whatever its targets. -/
def AdmittedConsumesMarker : Prop :=
  ∀ {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {ground : Ground deployment}
    {command : Command} {prepared : PreparedInvocation deployment profile ambient ground command}
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed)
    (shape : PhysicalShape prepared),
    invocationNullifier ground.authority.domain
        (operationMarker ground.authority.domain profile.semantics command) ∈
      (accepted.dataIntent shape).nullifiers

/-- **A landed append never lands again.**  On any ground where a command's operation
marker is spent, that command does not prepare: no root, current or planned, matters. -/
def ReplayRefused : Prop :=
  ∀ {F : Type} [Field F] (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (ground : Ground deployment) (command : Command),
    ground.markerSpent (operationMarker ground.authority.domain profile.semantics command) = some true →
    IsEmpty (PreparedInvocation deployment profile ambient ground command)

/-! ## Witness data -/

/-- The witness document's root element. -/
def witnessRoot : ElementId := ⟨⟨0⟩⟩

/-- A blinded cell holding one empty document, as birth (the blinding, `⟨0⟩`, the store of
`Kernel.EffectsRevival.ContentProofs.blindedStore`) and then `createDocument` leave it. -/
def witnessStore (document : DocumentId) (author : PrincipalRef) (operation : OperationId) :
    ContentResource.ContentStore :=
  (((0 : ContentResource.ContentStore).set ⟨.blinding, ()⟩ (some (⟨0⟩ : Digest))).set
      ⟨.documents, document⟩ (some (⟨witnessRoot, ⟨0⟩, author, operation⟩ : DocumentRecord))).set
    ⟨.elements, witnessRoot⟩
    (some (⟨document, none, .container [], author, operation, operation, none⟩ : ElementRecord))

/-- The witness cell of target `id`, its document written by `command₀`'s author. -/
def witnessCell (snapshot : AuthoritySnapshot) (semantics : Digest) (command₀ : Command) (id : Nat)
    (capability : CapabilityId) : ContentResource.ContentCell :=
  CellState.materialize _ (witnessStore (ContentResource.documentOf id)
    ⟨command₀.subject, .object, capability⟩ (contentOperation snapshot semantics command₀))

/-- Line `n`: one text atom, id `n` (never the root element's id `0`). -/
def witnessLine (n : Nat) : ContentResource.Command := ⟨[.createAtom ⟨⟨n⟩⟩ .text [0x78]]⟩

/-! ## Satisfiable and premise inhabitation -/

/-- **Satisfiable.**  On the blinded witness document, a line planned over some root that is
not the loaded cell's lands, it is the document's one line, and the post's blinding is one
ratchet step of the blinding of the cell the line met. -/
def MovedRootAccepted : Prop :=
  ∀ (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command₀ command : Command) (id : Nat) (capability : CapabilityId)
    (observe : Option CapabilityId) (epoch : Option Nat) (roster : Option ObjectAudienceRoster.Roster),
    ∃ (root : Digest) (post : Store.Store Hyperdocument.layout),
      root ≠ (witnessCell snapshot semantics command₀ id capability).root ∧
      computeTarget snapshot semantics ambient command
          (contentTarget .object id capability ContentResource.commandVersion root (witnessLine 1)
            observe epoch roster) (witnessCell snapshot semantics command₀ id capability) = .ok post ∧
      ContentResource.childrenOf post witnessRoot = [ContentResource.atomElement ⟨⟨1⟩⟩] ∧
      StoreCodec.blindingKey HyperdocumentCell.contentWire post =
        some (HyperdocumentCell.contentBlinding.step ambient.height
          ((HyperdocumentCell.contentWire.valueStream .blinding).encode (⟨0⟩ : Digest)))

/-- **Premise inhabitation.**  Two members plan from ONE observation of the witness document
(both name its root).  Either may land first; the other then lands over the moved cell; each
line is in the document once, in landing order. -/
def TwoAppendersOneObservation : Prop :=
  ∀ (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command₀ command₁ command₂ : Command) (id : Nat) (capability : CapabilityId)
    (observe : Option CapabilityId) (epoch : Option Nat) (roster : Option ObjectAudienceRoster.Roster),
    ∃ p₁ p₁₂ p₂ p₂₁ : Store.Store Hyperdocument.layout,
      computeTarget snapshot semantics ambient command₁
          (contentTarget .object id capability ContentResource.commandVersion
            (witnessCell snapshot semantics command₀ id capability).root (witnessLine 1)
            observe epoch roster) (witnessCell snapshot semantics command₀ id capability) = .ok p₁ ∧
      computeTarget snapshot semantics ambient command₂
          (contentTarget .object id capability ContentResource.commandVersion
            (witnessCell snapshot semantics command₀ id capability).root (witnessLine 2)
            observe epoch roster) (CellState.materialize _ p₁) = .ok p₁₂ ∧
      computeTarget snapshot semantics ambient command₂
          (contentTarget .object id capability ContentResource.commandVersion
            (witnessCell snapshot semantics command₀ id capability).root (witnessLine 2)
            observe epoch roster) (witnessCell snapshot semantics command₀ id capability) = .ok p₂ ∧
      computeTarget snapshot semantics ambient command₁
          (contentTarget .object id capability ContentResource.commandVersion
            (witnessCell snapshot semantics command₀ id capability).root (witnessLine 1)
            observe epoch roster) (CellState.materialize _ p₂) = .ok p₂₁ ∧
      ContentResource.childrenOf p₁₂ witnessRoot =
        [ContentResource.atomElement ⟨⟨1⟩⟩, ContentResource.atomElement ⟨⟨2⟩⟩] ∧
      ContentResource.childrenOf p₂₁ witnessRoot =
        [ContentResource.atomElement ⟨⟨2⟩⟩, ContentResource.atomElement ⟨⟨1⟩⟩]

end Minidregg.Kernel.ContentCommutingAppend
