/-
# `Kernel/EffectsRevival/PrepareProofs.lean` — the receiver's preparation of a content target

The wrong-role pole (`ContentWrongRole`, `ContentWrongRoleUncharged`, `ContentWrongRoleCommand`),
and `PrepareFactors contentSpec` on every target under a role that is not an object, the case
the hand arm's selection never reached. `PrepareFactors contentSpec` on object targets is owed.
-/
module

public import Kernel.EffectsRevival.CommutingProofs
public import Effects.Revival.EngineProofs
public import Theory.AssertAxioms

import all Init.Control.Except
import all Init.Data.List.Basic

@[expose] public section

namespace Minidregg.Effects.Revival

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel

set_option autoImplicit false

/-- The computation of a content target under a role that is not an object. -/
theorem computeTarget_content_wrongRole (ctx : LiveCtx) (command : ContentResource.Command)
    (version : Nat) (root : Digest) (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster) (pre : ContentResource.ContentCell)
    (wrong : ctx.kind ≠ .object) :
    DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics ctx.ambient ctx.command
      (contentTarget ctx version root command observe epoch roster) pre = .error .wrongRole := by
  have computed := DeclaredResourceController.computeTarget_content ctx.snapshot ctx.semantics
    ctx.ambient ctx.command ctx.kind ctx.target ctx.capability version root command observe epoch
    roster pre
  rw [if_pos (by simpa using wrong)] at computed
  exact computed

theorem prepareTarget_content_absent (deployment : DeclaredResourceController.Deployment)
    (directory : CellRegistry.Directory Nat DeclaredResourceController.Registry)
    (ctx : LiveCtx) (command : ContentResource.Command) (version : Nat) (root : Digest)
    (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster)
    (absent : directory.slots ctx.target = .absent) :
    DeclaredResourceController.prepareTarget deployment directory ctx.snapshot ctx.semantics
        ctx.ambient ctx.command (contentTarget ctx version root command observe epoch roster) =
      .error .missingTarget := by
  unfold DeclaredResourceController.prepareTarget
  split
  · rfl
  · rename_i before found
    have clash := found.symm.trans absent
    cases clash

theorem prepareTarget_content_wrongRole (deployment : DeclaredResourceController.Deployment)
    (directory : CellRegistry.Directory Nat DeclaredResourceController.Registry)
    (ctx : LiveCtx) (command : ContentResource.Command) (version : Nat) (root : Digest)
    (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster)
    (before : CellRegistry.PackedCell DeclaredResourceController.Registry)
    (wrong : ctx.kind ≠ .object) (present : directory.slots ctx.target = .present before) :
    DeclaredResourceController.prepareTarget deployment directory ctx.snapshot ctx.semantics
        ctx.ambient ctx.command (contentTarget ctx version root command observe epoch roster) =
      .error .wrongRole := by
  unfold DeclaredResourceController.prepareTarget
  split
  · rename_i absent
    have clash := absent.symm.trans present
    cases clash
  · split
    · rfl
    · rename_i pre selected
      have refused := computeTarget_content_wrongRole ctx command version root observe epoch
        roster pre wrong
      split
      · rename_i reason computed
        cases computed.symm.trans refused
        rfl
      · rename_i post computed
        cases computed.symm.trans refused

theorem contentWrongRole : ContentWrongRole := by
  intro deployment directory ctx command version root observe epoch roster wrong
  cases present : directory.slots ctx.target with
  | absent =>
    exact prepareTarget_content_absent deployment directory ctx command version root observe epoch
      roster present
  | present before =>
    exact prepareTarget_content_wrongRole deployment directory ctx command version root observe
      epoch roster before wrong present

theorem contentWrongRoleUncharged : ContentWrongRoleUncharged := by
  have target : ∀ (deployment : DeclaredResourceController.Deployment)
      (directory : CellRegistry.Directory Nat DeclaredResourceController.Registry)
      (ctx : LiveCtx) (command : ContentResource.Command) (version : Nat) (root : Digest)
      (observe : Option CapabilityId) (epoch : Option Nat)
      (roster : Option ObjectAudienceRoster.Roster),
      ctx.kind ≠ .object →
      IsEmpty (DeclaredResourceController.PreparedTarget deployment directory ctx.snapshot
        ctx.semantics ctx.ambient ctx.command
        (contentTarget ctx version root command observe epoch roster)) := by
    intro deployment directory ctx command version root observe epoch roster wrong
    refine ⟨fun prepared => ?_⟩
    have computed := prepared.candidate.modeEvidence.down
    have refused := computeTarget_content_wrongRole ctx command version root observe epoch roster
      prepared.pre wrong
    cases computed.symm.trans refused
  refine ⟨target, ?_⟩
  intro F _ deployment profile ambient directory authority cells declared command i kind id
    capability version root content observe epoch roster at_ wrong
  refine ⟨fun prepared => ?_⟩
  have one := prepared.targets i
  rw [at_] at one
  exact (target deployment directory ⟨authority, profile.semantics, ambient, command, kind, id,
    capability⟩ content version root observe epoch roster wrong).false one

theorem contentWrongRoleCommand : ContentWrongRoleCommand := by
  intro F _ deployment profile ambient directory authority cells subject nonce run family kind id
    capability version root content observe epoch roster before clock wrong present loaded writes
  have refused := prepareTarget_content_wrongRole deployment directory
    ⟨authority, profile.semantics, ambient,
      ⟨subject, nonce, [⟨kind, id, capability, version, root, .content content, observe, epoch,
        roster⟩], run, family⟩, kind, id, capability⟩ content version root observe epoch roster
    before wrong present
  simp only [contentTarget] at refused
  unfold DeclaredResourceController.prepareOn
  rw [dif_pos (by simp), dif_pos (by simp), dif_pos writes, dif_pos rfl]
  simp only [loaded, DeclaredResourceController.requireSome, DeclaredResourceController.collect,
    refused, bind, Except.bind, Except.map]

/-- The spec-side header refuses a role that is not an object, whatever the cell. -/
theorem contentHeader_wrongRole (ctx : LiveCtx) (deployment : DeclaredResourceController.Deployment)
    (version : Nat) (root : Digest) (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster) (before : HostCell) (wrong : ctx.kind ≠ .object) :
    contentHeader (hostCtxOf ctx deployment version root observe epoch roster) before =
      .error (.wrongRole 1) := by
  unfold contentHeader
  rw [if_pos (Or.inl (by simp [hostCtxOf, wrong]))]

set_option backward.isDefEq.respectTransparency false in
theorem dispatch_content (ctx : HostCtx) (cell : HostCell) (command : ContentResource.Command) :
    dispatch [(1, contentHandlerOf contentSpec)] 1 (ContentResource.commandStream.encode command) ctx cell =
      (contentHandlerOf contentSpec).fire 1 ctx command cell := by
  simp only [dispatch, List.lookup, beq_self_eq_true]
  rw [show (contentHandlerOf contentSpec).spec.opStream = ContentResource.commandStream from rfl,
    decode_encode_op]

/-- **`PrepareFactors contentSpec` at every role that is not an object**: both sides refuse
`wrongRole` under code 1. -/
theorem prepareFactors_wrongRole (deployment : DeclaredResourceController.Deployment)
    (directory : CellRegistry.Directory Nat DeclaredResourceController.Registry)
    (ctx : LiveCtx) (command : ContentResource.Command) (version : Nat) (root : Digest)
    (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster) (before : HostCell)
    (wrong : ctx.kind ≠ .object) (present : directory.slots ctx.target = .present before) :
    ((DeclaredResourceController.prepareTarget deployment directory ctx.snapshot ctx.semantics
        ctx.ambient ctx.command (contentTarget ctx version root command observe epoch roster)).map
        (fun prepared => DeclaredResourceController.packTarget
          (contentTarget ctx version root command observe epoch roster) prepared.candidate.post)).mapError
        (ofReject 1) =
      (dispatch [(1, contentHandlerOf contentSpec)] 1 (ContentResource.commandStream.encode command)
          (hostCtxOf ctx deployment version root observe epoch roster) before) >>=
        genericChecks deployment directory ctx.snapshot ctx.target epoch before := by
  rw [prepareTarget_content_wrongRole deployment directory ctx command version root observe epoch
    roster before wrong present, dispatch_content]
  simp only [Handler.fire, Handler.admits, contentHandlerOf,
    contentHeader_wrongRole ctx deployment version root observe epoch roster before wrong]
  rfl

/-- **`CommutingPrepare` at every role that is not an object**: the two planned roots are refused
alike, whether or not the command commutes. -/
theorem commutingPrepare_wrongRole (deployment : DeclaredResourceController.Deployment)
    (directory : CellRegistry.Directory Nat DeclaredResourceController.Registry)
    (snapshot : DeclaredResourceController.AuthoritySnapshot) (semantics : Digest)
    (ambient : DeclaredResourceController.Ambient) (command : DeclaredResourceController.Command)
    (kind : ResourceKind) (id : Nat) (capability : CapabilityId) (version : Nat)
    (root root' : Digest) (content : ContentResource.Command) (observe : Option CapabilityId)
    (epoch : Option Nat) (roster : Option ObjectAudienceRoster.Roster) (wrong : kind ≠ .object) :
    (DeclaredResourceController.prepareTarget deployment directory snapshot semantics ambient command
        (ContentCommutingAppend.contentTarget kind id capability version root content observe epoch
          roster)).map
        (fun prepared => DeclaredResourceController.packTarget
          (ContentCommutingAppend.contentTarget kind id capability version root content observe epoch
            roster) prepared.candidate.post) =
      (DeclaredResourceController.prepareTarget deployment directory snapshot semantics ambient command
        (ContentCommutingAppend.contentTarget kind id capability version root' content observe epoch
          roster)).map
        (fun prepared => DeclaredResourceController.packTarget
          (ContentCommutingAppend.contentTarget kind id capability version root' content observe epoch
            roster) prepared.candidate.post) := by
  have planned := contentWrongRole deployment directory
    ⟨snapshot, semantics, ambient, command, kind, id, capability⟩ content version root observe epoch
    roster wrong
  have moved := contentWrongRole deployment directory
    ⟨snapshot, semantics, ambient, command, kind, id, capability⟩ content version root' observe epoch
    roster wrong
  simp only [contentTarget] at planned moved
  simp only [ContentCommutingAppend.contentTarget]
  rw [planned, moved]
  cases directory.slots id <;> rfl

/-! ## The pole, executed on the sample cell -/

/-- The sample context under an account role. -/
def accountCtx : LiveCtx := { sampleCtx with kind := .account }

/-- A directory holding the blinded sample content cell at the sample target, and nothing else. -/
def sampleDirectory : CellRegistry.Directory Nat DeclaredResourceController.Registry where
  slots := fun id => if id = 0 then .present ⟨.content, cellOf blindedStore⟩ else .absent
  used := {0}
  present_used := by
    intro id cell held
    split at held
    · simp_all
    · cases held

/-- **Refused.** The commuting line over the moved root, on the sample content cell, under an
account role: `wrongRole`, though the cell is a content cell and the command would be computed
under the object role (`sampleAtom_moved_computed`). -/
theorem sampleWrongRole :
    DeclaredResourceController.prepareTarget sampleDeployment sampleDirectory accountCtx.snapshot
        accountCtx.semantics accountCtx.ambient accountCtx.command
        (contentTarget accountCtx contentSpec.version movedRoot sampleAtomCommand none none none) =
      .error .wrongRole :=
  prepareTarget_content_wrongRole sampleDeployment sampleDirectory accountCtx sampleAtomCommand
    contentSpec.version movedRoot none none none ⟨.content, cellOf blindedStore⟩ (by decide) rfl

/-- **The role is what refuses.** The same cell, command, version and planned root under the
object role are computed, and under the account role are refused `wrongRole`. -/
theorem sampleRole_teeth :
    (∃ post, DeclaredResourceController.computeTarget sampleCtx.snapshot sampleCtx.semantics
      sampleCtx.ambient sampleCtx.command (contentTarget sampleCtx contentSpec.version movedRoot
        sampleAtomCommand none none none) (cellOf blindedStore) = .ok post) ∧
    DeclaredResourceController.computeTarget accountCtx.snapshot accountCtx.semantics
      accountCtx.ambient accountCtx.command (contentTarget accountCtx contentSpec.version movedRoot
        sampleAtomCommand none none none) (cellOf blindedStore) = .error .wrongRole :=
  ⟨sampleAtom_moved_computed, computeTarget_content_wrongRole accountCtx sampleAtomCommand
    contentSpec.version movedRoot none none none (cellOf blindedStore) (by decide)⟩

#assert_axioms contentWrongRole
#assert_axioms contentWrongRoleUncharged
#assert_axioms contentWrongRoleCommand
#assert_axioms prepareFactors_wrongRole
#assert_axioms commutingPrepare_wrongRole
#assert_axioms sampleWrongRole
#assert_axioms sampleRole_teeth

end Minidregg.Effects.Revival
