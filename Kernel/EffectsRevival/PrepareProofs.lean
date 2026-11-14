/-
# `Kernel/EffectsRevival/PrepareProofs.lean` — the receiver's preparation of a registered target

`PrepareFactors`, proved for every bound code: what `prepareTarget` answers at a registered
target is the registry's dispatch of its operation, then the generic checks. The proof reads
`prepareTarget` through `prepareTarget_packed` and the deployed arms through
`effect_dispatch_fire`; nothing in it is about one effect.

The wrong-role pole of the content binding (`ContentWrongRole`, `ContentWrongRoleUncharged`,
`ContentWrongRoleCommand`), executed on the sample cell.
-/
module

public import Kernel.EffectsRevival.CommutingProofs
public import Kernel.EffectsRevival.RegistryProofs
public import Kernel.ResourcePreparePacked
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

theorem registeredWrongRole : RegisteredWrongRole := by
  intro deployment directory snapshot semantics ambient command kind id capability version root
    code op observe epoch roster wrong
  have refused : ∀ pre, DeclaredResourceController.computeTarget snapshot semantics ambient command
      ⟨kind, id, capability, version, root, .registered code op, observe, epoch, roster⟩ pre =
        .error .wrongRole := by
    intro pre
    have wrong' : (DeclaredResourceController.effectAt code.toNat).spec.accepts
        (DeclaredResourceController.targetCtx snapshot semantics ambient command kind id capability
          observe epoch roster).kind = false := wrong
    show (DeclaredResourceController.Effect.compute _ code.toNat _ version root op pre).mapError
      DeclaredResourceController.Reject.ofDispatch = _
    unfold DeclaredResourceController.Effect.compute
    rw [if_pos wrong']
    rfl
  have absentCase : directory.slots id = .absent →
      DeclaredResourceController.prepareTarget deployment directory snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .registered code op, observe, epoch, roster⟩ =
        .error .missingTarget := by
    intro absent
    unfold DeclaredResourceController.prepareTarget
    split
    · rfl
    · rename_i before found
      cases found.symm.trans absent
  have presentCase : ∀ before, directory.slots id = .present before →
      DeclaredResourceController.prepareTarget deployment directory snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .registered code op, observe, epoch, roster⟩ =
        .error .wrongRole := by
    intro before present
    unfold DeclaredResourceController.prepareTarget
    split
    · rename_i absent
      cases absent.symm.trans present
    · split
      · rfl
      · rename_i pre selected
        split
        · rename_i reason computed
          cases computed.symm.trans (refused pre)
          rfl
        · rename_i post computed
          cases computed.symm.trans (refused pre)
  cases slot : directory.slots id with
  | absent => exact absentCase slot
  | present before => exact presentCase before slot

theorem readRoles : ReadRoles := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#assert_axioms registeredWrongRole
#assert_axioms readRoles

/-! ## `PrepareFactors`: the receiver's preparation is the registry's dispatch, then the generic checks -/

theorem hostRegistry_lookup_bound {code : Nat}
    (bound : DeclaredResourceController.registeredCode code = true) :
    hostRegistry.lookup code =
      some (((DeclaredResourceController.effectAt code).handler code).comap dispatchCtxOf) := by
  rw [hostRegistry_lookup_eq]
  unfold DeclaredResourceController.registeredCode at bound
  unfold DeclaredResourceController.effectAt
  cases found : DeclaredResourceController.liveEffects.lookup code with
  | none => rw [found] at bound; cases bound
  | some e => rfl

theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {a : α}
    (ok : x.mapError f = .ok a) : x = .ok a := by
  cases x with
  | error e => cases ok
  | ok b => cases ok; rfl

/-- **The receiver's four reads of a registered target are its handler fired, then the generic
checks**, at every context, operation and loaded cell. -/
theorem receive_registered
    (directory : CellRegistry.Directory Nat DeclaredResourceController.Registry) (h : HostCtx)
    (tag : UInt8) (op : (DeclaredResourceController.effectAt tag.toNat).O) (before : HostCell) :
    (DeclaredResourceController.receive (.present before)
        (DeclaredResourceController.selectTarget h.deployment (hostTarget h (.registered tag op)))
        (DeclaredResourceController.computeTarget h.snapshot h.semantics h.ambient h.command
          (hostTarget h (.registered tag op)))
        (fun before pre post => DeclaredResourceController.afterTarget h.deployment directory
          h.snapshot (hostTarget h (.registered tag op)).materializer
          (DeclaredResourceController.packTarget (hostTarget h (.registered tag op)))
          (hostTarget h (.registered tag op)).target
          (hostTarget h (.registered tag op)).audienceEpoch before pre
          (DeclaredResourceController.targetPatch h.snapshot h.semantics h.ambient h.command
            (hostTarget h (.registered tag op)) pre) post)).mapError (ofReject tag.toNat) =
      ((DeclaredResourceController.effectAt tag.toNat).handler tag.toNat).fire tag.toNat
          (dispatchCtxOf h) op before >>=
        genericChecks tag.toNat h.deployment directory h.snapshot h.target h.epoch before := by
  rw [← effect_dispatch_fire (DeclaredResourceController.effectAt tag.toNat) tag.toNat
    (dispatchCtxOf h) op before]
  cases selected : DeclaredResourceController.selectTarget h.deployment
      (hostTarget h (.registered tag op)) before with
  | none =>
    have selected' : (DeclaredResourceController.effectAt tag.toNat).select
        (dispatchCtxOf h).deployment (dispatchCtxOf h).target (dispatchCtxOf h).kind before =
          none := selected
    simp only [DeclaredResourceController.receive, selected, selected']
    rfl
  | some pre =>
    have selected' : (DeclaredResourceController.effectAt tag.toNat).select
        (dispatchCtxOf h).deployment (dispatchCtxOf h).target (dispatchCtxOf h).kind before =
          some pre := selected
    cases computed : DeclaredResourceController.computeTarget h.snapshot h.semantics h.ambient
        h.command (hostTarget h (.registered tag op)) pre with
    | error reason =>
      have computed' : ((DeclaredResourceController.effectAt tag.toNat).compute tag.toNat
          (dispatchCtxOf h).toEffectCtx (dispatchCtxOf h).version (dispatchCtxOf h).root op
          pre).mapError DeclaredResourceController.Reject.ofDispatch = .error reason := computed
      simp only [DeclaredResourceController.receive, selected, selected', computed, computed']
      rfl
    | ok post =>
      have computed' : ((DeclaredResourceController.effectAt tag.toNat).compute tag.toNat
          (dispatchCtxOf h).toEffectCtx (dispatchCtxOf h).version (dispatchCtxOf h).root op
          pre).mapError DeclaredResourceController.Reject.ofDispatch = .ok post := computed
      obtain ⟨-, -, ps, emitted, replayed⟩ :=
        (DeclaredResourceController.effectAt tag.toNat).compute_ok (mapError_ok computed')
      have patched : (DeclaredResourceController.effectAt tag.toNat).patch
          (dispatchCtxOf h).toEffectCtx op pre.logical =
            ps ++ (DeclaredResourceController.effectAt tag.toNat).spec.rotate
              (dispatchCtxOf h).toEffectCtx pre.logical := by
        unfold DeclaredResourceController.Effect.patch EffectSpec.emitted
        rw [emitted]
        rfl
      rw [← patched] at replayed
      obtain ⟨valid, ran⟩ := (store_run_iff _ _ _).mp replayed
      have disabled : Patch.firstDisabled? pre.logical
          (DeclaredResourceController.targetPatch h.snapshot h.semantics h.ambient h.command
            (hostTarget h (.registered tag op)) pre) = none :=
        (Patch.firstDisabled?_eq_none_iff _ _).2 valid
      have ran' : Patch.run pre.logical
          (DeclaredResourceController.targetPatch h.snapshot h.semantics h.ambient h.command
            (hostTarget h (.registered tag op)) pre) = post := ran
      simp only [DeclaredResourceController.receive, selected, selected', computed, computed',
        DeclaredResourceController.afterTarget, disabled]
      rw [ran', if_pos rfl, if_pos valid]
      simp only [bind, Except.bind, genericChecks]
      by_cases law : CanonicalCellRegistry.FinalPostLaw h.deployment
          (hostTarget h (.registered tag op)).target before
          (DeclaredResourceController.packTarget (hostTarget h (.registered tag op))
            (materialize (hostTarget h (.registered tag op)).materializer post))
      · rw [if_pos law, if_pos (show CanonicalCellRegistry.FinalPostLaw h.deployment h.target before
          ((DeclaredResourceController.effectAt tag.toNat).pack (dispatchCtxOf h).kind
            (materialize (DeclaredResourceController.effectAt tag.toNat).materializer post)) from law)]
        cases source : CanonicalCellRegistry.loadPolicySource h.snapshot.domain directory
            (h.snapshot.authState.policyAddress ⟨h.target⟩
              (h.snapshot.authState.policyRevision ⟨h.target⟩)) with
        | none => rfl
        | some loaded =>
          dsimp only
          cases fresh : ObjectAudience.checkFresh loaded.record.audience h.target h.epoch with
          | error reason => rfl
          | ok unit => rfl
      · rw [if_neg law, if_neg (show ¬ CanonicalCellRegistry.FinalPostLaw h.deployment h.target before
          ((DeclaredResourceController.effectAt tag.toNat).pack (dispatchCtxOf h).kind
            (materialize (DeclaredResourceController.effectAt tag.toNat).materializer post)) from law)]
        rfl

theorem prepareFactors : PrepareFactors := by
  intro deployment directory ctx tag op version root observe epoch roster before bound present
  have fired : dispatch hostRegistry tag.toNat
        ((DeclaredResourceController.effectAt tag.toNat).spec.opStream.encode op)
        (hostCtxOf ctx deployment version root observe epoch roster) before =
      ((DeclaredResourceController.effectAt tag.toNat).handler tag.toNat).fire tag.toNat
        (dispatchCtxOf (hostCtxOf ctx deployment version root observe epoch roster)) op before := by
    rw [dispatch_found (hostRegistry_lookup_bound bound)]
    unfold Handler.read
    have decoded : (((DeclaredResourceController.effectAt tag.toNat).handler tag.toNat).comap
          dispatchCtxOf).spec.opStream.toLawful.decode
        ((DeclaredResourceController.effectAt tag.toNat).spec.opStream.encode op) = some op :=
      decode_encode_op (DeclaredResourceController.effectAt tag.toNat).spec.opStream op
    rw [decoded]
    exact Handler.comap_fire dispatchCtxOf
      ((DeclaredResourceController.effectAt tag.toNat).handler tag.toNat) tag.toNat
      (hostCtxOf ctx deployment version root observe epoch roster) op before
  rw [fired, DeclaredResourceController.prepareTarget_packed]
  have present' : directory.slots
      (hostTarget (hostCtxOf ctx deployment version root observe epoch roster)
        (.registered tag op)).target = .present before := present
  rw [present']
  exact receive_registered directory (hostCtxOf ctx deployment version root observe epoch roster)
    tag op before

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
#assert_axioms prepareFactors
#assert_axioms sampleWrongRole
#assert_axioms sampleRole_teeth

end Minidregg.Effects.Revival
