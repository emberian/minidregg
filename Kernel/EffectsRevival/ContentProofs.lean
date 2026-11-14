/-
# `Kernel/EffectsRevival/ContentProofs.lean` — `ContentAgreement` and the live keystone's poles, PROVED

The content declaration's own obligation, `ContentComplete`, is proved upstream with the
declaration (`Kernel/ContentEffect.lean`, `contentSpec_complete`) and read here under the live
context. This file proves that the deployed hand arm IS the declaration (`contentAgreement`), the
narrowed-frame and ghost teeth, and the accepting poles on hand-built cells.
-/
module

public import Kernel.EffectsRevival.Statements
public import Effects.Revival.EngineProofs
public import Theory.AssertAxioms

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

namespace Minidregg.Effects.Revival

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.ContentResource (Progress)
/-- `throw` in `Except` is `.error`; under Lean 4.35's instance transparency `simp` no longer
unfolds the `MonadExceptOf` instance on its own. -/
@[local simp] private theorem except_throw {ε α : Type _} (e : ε) :
    (throw e : Except ε α) = .error e := rfl

set_option autoImplicit false

theorem contentComplete : ContentComplete := fun ctx command s ps emitted =>
  DeclaredResourceController.contentSpec_complete (liveEffectCtx ctx) command s ps emitted

/-! ## The narrowed half of `ContentTeeth`. -/

/-- A transaction context: every field a zero, the authority cell empty. -/
def sampleCtx : LiveCtx where
  snapshot := CredentialAuthorityDomain.Snapshot.ofCell ⟨0⟩ 0 (fun _ => false)
    (materialize CredentialAuthorityCell.materializer 0)
  semantics := ⟨0⟩
  ambient := { federation := ⟨0⟩, height := 0 }
  command := { subject := ⟨0⟩, nonce := 0, targets := [] }
  kind := .object
  target := 0
  capability := ⟨0⟩

/-- One link, with no source range, to an external target. -/
def sampleLink : Hyperdocument.LinkId := ⟨⟨0⟩⟩

def sampleLinkCommand : ContentResource.Command :=
  ⟨[.link sampleLink none (.external [] [] []) ⟨0⟩]⟩

/-- **Frame teeth.**  The declaration whose frame omits `annotations` is not complete: a
link (field `annotations`) is admitted by the lowering and written outside that frame. -/
theorem contentNarrowed_incomplete : ¬ contentNarrowed.Complete := by
  intro complete
  have emitted : contentNarrowed.sem sampleCtx sampleLinkCommand (0 : ContentResource.ContentStore) =
      .ok [.allocate .links sampleLink
        ⟨ContentResource.documentOf sampleCtx.target, none, .external [] [] [], ⟨0⟩,
          ⟨sampleCtx.command.subject, sampleCtx.kind, sampleCtx.capability⟩,
          DeclaredResourceController.contentOperation sampleCtx.snapshot sampleCtx.semantics
            sampleCtx.command, none⟩] := by
    simp [contentSpec_sem, contentNarrowed, sampleLinkCommand, ContentResource.run,
      ContentResource.step, ContentResource.allocate, Except.map, bind, Except.bind, pure,
      Except.pure]
    rfl
  have inFrame := (complete sampleCtx sampleLinkCommand (0 : ContentResource.ContentStore) _ emitted).1
  have written := inFrame ⟨.links, sampleLink⟩ (by
      change ⟨.links, sampleLink⟩ ∈ (Option.toFinset (some ⟨.links, sampleLink⟩) ∪
        ((storeSubstrate Hyperdocument.layout).footprint
          (contentNarrowed.rotate sampleCtx (0 : ContentResource.ContentStore))) : Finset CAddr)
      exact Finset.mem_union_left _ (Option.mem_toFinset.mpr rfl)) rfl
  simp [contentNarrowed, contentFrame, contentActionFrame, sampleLinkCommand,
    ResourceObservationAdmission.contentFieldAt, ResourceObservationAdmission.contentField] at written

/-! ## `ContentAgreement contentSpec`: the deployed content arm IS the declaration. -/

/-- The content arm of `computeTarget` under a passing header: the source preparation, its
post followed by the kernel's blinding rotation. -/
theorem computeTarget_content_header (ctx : LiveCtx) (command : ContentResource.Command)
    (pre : ContentResource.ContentCell) (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster) (root : Digest) (object : ctx.kind = .object)
    (fresh : root = pre.root ∨ contentSpec.commutes command = true) :
    DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics ctx.ambient ctx.command
        (contentTarget ctx contentSpec.version root command observe epoch roster) pre =
      match ContentResource.prepareCell ⟨ctx.command.subject, ctx.kind, ctx.capability⟩
          (DeclaredResourceController.contentOperation ctx.snapshot ctx.semantics ctx.command)
          (ContentResource.documentOf ctx.target)
          (DeclaredResourceController.contentContext ctx.snapshot ctx.ambient ctx.command) pre command with
      | .error reason => .error (.effect (.refused 1 (DeclaredResourceController.contentRefusalName reason) .empty))
      | .ok prepared => .ok (Patch.run prepared.post.logical
          (HyperdocumentCell.contentBlinding.patch pre.logical ctx.ambient.height)) := by
  simp [DeclaredResourceController.computeTarget_content_arm, contentTarget, object, bind,
    Except.bind, pure, Except.pure]
  split
  · rename_i stale
    rcases fresh with same | commuting
    · exact absurd same stale.2
    · simp at commuting
      simp [commuting] at stale
  · generalize ContentResource.prepareCell ⟨ctx.command.subject, ctx.kind, ctx.capability⟩
        (DeclaredResourceController.contentOperation ctx.snapshot ctx.semantics ctx.command)
        (ContentResource.documentOf ctx.target)
        (DeclaredResourceController.contentContext ctx.snapshot ctx.ambient ctx.command) pre command =
      result
    cases result <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem contentAgreement : ContentAgreement contentSpec := by
  intro ctx command pre observe epoch roster
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro version root rejected
    have notObject : ctx.kind ≠ .object := by
      intro object; simp [object] at rejected
    simp [DeclaredResourceController.computeTarget_content_arm, contentTarget, notObject, bind, Except.bind]
  · intro version root accepted wrongVersion
    have object : ctx.kind = .object := by simpa using accepted
    have wrongVersion' : version ≠ ContentResource.commandVersion := wrongVersion
    simp [DeclaredResourceController.computeTarget_content_arm, contentTarget, object, wrongVersion', bind,
      Except.bind, pure, Except.pure]
  · intro root accepted commutes stale
    have object : ctx.kind = .object := by simpa using accepted
    have commutes' : command.commutes = false := commutes
    simp [DeclaredResourceController.computeTarget_content_arm, contentTarget, object, commutes',
      bind, Except.bind, pure, Except.pure]
    intro same
    exact absurd same stale
  · intro root accepted fresh
    have object : ctx.kind = .object := by simpa using accepted
    rw [computeTarget_content_header ctx command pre observe epoch roster root object fresh]
    by_cases empty : command.actions.isEmpty
    · have refused : contentSpec.sem ctx command pre.logical = .error .emptyActions := by
        simp [contentSpec_sem, empty]
      have prepared : ContentResource.prepareCell ⟨ctx.command.subject, ctx.kind, ctx.capability⟩
          (DeclaredResourceController.contentOperation ctx.snapshot ctx.semantics ctx.command)
          (ContentResource.documentOf ctx.target)
          (DeclaredResourceController.contentContext ctx.snapshot ctx.ambient ctx.command) pre command =
            .error .emptyActions := by
        unfold ContentResource.prepareCell
        rw [dif_neg (by simpa using empty)]
      refine ⟨?_, ?_, ?_⟩
      · intro post
        simp [EffectSpec.exec, refused, prepared]
      · intro name detail computed
        rw [prepared] at computed
        cases computed
        simp [EffectSpec.exec, refused]
      · intro ps emitted
        rw [refused] at emitted
        cases emitted
    · have nonempty : command.actions ≠ [] := by simpa using empty
      cases ran : ContentResource.run ⟨ctx.command.subject, ctx.kind, ctx.capability⟩
          (DeclaredResourceController.contentOperation ctx.snapshot ctx.semantics ctx.command)
          (ContentResource.documentOf ctx.target)
          (DeclaredResourceController.contentContext ctx.snapshot ctx.ambient ctx.command)
          pre.logical command with
      | error reason =>
        have refused : contentSpec.sem ctx command pre.logical = .error reason := by
          simp [contentSpec_sem, empty, ran, Except.map]
        have prepared : ContentResource.prepareCell ⟨ctx.command.subject, ctx.kind, ctx.capability⟩
            (DeclaredResourceController.contentOperation ctx.snapshot ctx.semantics ctx.command)
            (ContentResource.documentOf ctx.target)
            (DeclaredResourceController.contentContext ctx.snapshot ctx.ambient ctx.command) pre command =
              .error reason := by
          unfold ContentResource.prepareCell
          rw [dif_pos nonempty]
          split
          · rename_i other computed
            rw [ran] at computed
            cases computed
            rfl
          · rename_i other computed
            rw [ran] at computed
            cases computed
        refine ⟨?_, ?_, ?_⟩
        · intro post
          simp [EffectSpec.exec, refused, prepared]
        · intro name detail computed
          rw [prepared] at computed
          cases computed
          simp [EffectSpec.exec, refused]
        · intro ps emitted
          rw [refused] at emitted
          cases emitted
      | ok progress =>
        have emitted : contentSpec.sem ctx command pre.logical = .ok progress.2 := by
          simp [contentSpec_sem, empty, ran, Except.map]
        obtain ⟨prepared, preparedOk⟩ := ContentResource.prepareCell_ok_of_run _ _ _ _ pre command
          progress nonempty ran
        have sameProgress : prepared.progress = progress := by
          have computed := prepared.computed
          rw [ran] at computed
          injection computed with same
          exact same.symm
        have postExact : prepared.post.logical = Patch.run pre.logical progress.2 := by
          rw [prepared.post_exact, sameProgress]
          exact (ContentResource.run_executes _ _ _ _ _ command progress ran).2.symm
        have patch : DeclaredResourceController.targetPatch ctx.snapshot ctx.semantics ctx.ambient
            ctx.command (contentTarget ctx contentSpec.version root command observe epoch roster) pre =
              progress.2 ++ HyperdocumentCell.contentBlinding.patch pre.logical ctx.ambient.height := by
          have arm := DeclaredResourceController.targetPatch_content_arm ctx.snapshot ctx.semantics
            ctx.ambient ctx.command ctx.kind ctx.target ctx.capability contentSpec.version root command
            observe epoch roster pre nonempty
          rw [ran] at arm
          exact arm
        have complete := contentComplete ctx command pre.logical progress.2 emitted
        refine ⟨?_, ?_, ?_⟩
        · intro post
          rw [preparedOk, patch]
          simp only [EffectSpec.exec, emitted, if_pos complete.1]
          constructor
          · intro executed
            split at executed
            · cases executed
            · rename_i s' replayed
              cases executed
              obtain ⟨valid, ran'⟩ := (store_run_iff _ _ _).1 replayed
              refine ⟨?_, valid⟩
              rw [postExact]
              erw [Patch.run_append] at ran'
              exact congrArg Except.ok ran'
          · rintro ⟨computed, valid⟩
            erw [store_run_validFrom (L := Hyperdocument.layout) _ _ valid]
            rw [postExact] at computed
            simpa [Patch.run_append] using computed
        · intro name detail computed
          rw [preparedOk] at computed
          cases computed
        · intro ps emitted'
          rw [emitted] at emitted'
          cases emitted'
          exact patch
  · intro version root
    refine ⟨fun _ => rfl, ?_, fun _ _ => rfl, ?_, fun _ _ => rfl⟩
    · rintro ⟨space, key⟩
      cases space <;> rfl
    cases ctx.kind <;> rfl

/-! ## The live keystone's poles, on hand-built cells (kernel proofs). -/

/-- A complete declaration's executor admits every operation its semantics emits. -/
theorem exec_ok_of_complete {Ctx : Type} {S : Substrate} {O R : Type} {E : EffectSpec Ctx S O R}
    (complete : E.Complete) {code : Nat} {ctx : Ctx} {op : O} {s : S.State} {ps : List S.Prim}
    (emitted : E.sem ctx op s = .ok ps) : ∃ s', E.exec code ctx op s = .ok s' := by
  obtain ⟨inFrame, runs⟩ := complete ctx op s ps emitted
  unfold EffectSpec.exec
  rw [emitted]
  simp only [if_pos inFrame]
  cases ran : S.run s (ps ++ E.rotate ctx s) with
  | none => rw [ran] at runs; cases runs
  | some s' => exact ⟨s', rfl⟩

/-- The content cell of a store. -/
abbrev cellOf (s : ContentResource.ContentStore) : ContentResource.ContentCell :=
  CellState.materialize HyperdocumentCell.contentMaterializer s

/-- A store whose blinding is set (the deployed cells carry one from birth). -/
def blindedStore : ContentResource.ContentStore :=
  Store.set (0 : ContentResource.ContentStore) ⟨.blinding, ()⟩ (some (⟨0⟩ : Digest))

/-- The link command's descriptor: its one allocation. -/
def sampleLinkOps : Patch Hyperdocument.layout :=
  [.allocate .links sampleLink
    ⟨ContentResource.documentOf sampleCtx.target, none, .external [] [] [], ⟨0⟩,
      ⟨sampleCtx.command.subject, sampleCtx.kind, sampleCtx.capability⟩,
      DeclaredResourceController.contentOperation sampleCtx.snapshot sampleCtx.semantics
        sampleCtx.command, none⟩]

/-- The link command emits its one allocation at the blinded store too. -/
theorem sampleLink_emits_blinded_eq :
    contentSpec.sem sampleCtx sampleLinkCommand blindedStore = .ok sampleLinkOps := by
  simp [contentSpec_sem, sampleLinkCommand, ContentResource.run,
    ContentResource.step, ContentResource.allocate, Except.map, bind, Except.bind, pure,
    Except.pure, blindedStore, Store.set, sampleLinkOps]
  rfl

theorem sampleLink_emits_blinded :
    ∃ ps, contentSpec.sem sampleCtx sampleLinkCommand blindedStore = .ok ps :=
  ⟨_, sampleLink_emits_blinded_eq⟩

/-- **The accepted branch, inhabited**: the live arm admits a link at the empty content
cell (the derived executor admits it, so `contentAgreement`'s clause 2 gives the live arm). -/
theorem contentAccepted : ContentAccepted := by
  obtain ⟨ps, emitted⟩ := sampleLink_emits_blinded
  obtain ⟨post, executed⟩ := exec_ok_of_complete (code := 1) contentComplete emitted
  obtain ⟨-, -, -, live, -⟩ := contentAgreement sampleCtx sampleLinkCommand (cellOf blindedStore)
    none none none
  obtain ⟨accepted, -, -⟩ := live _ rfl (Or.inl rfl)
  obtain ⟨computed, valid⟩ := (accepted post).1 executed
  exact ⟨sampleCtx, sampleLinkCommand, cellOf blindedStore, none, none, none, post, rfl,
    by simp [sampleLinkCommand], computed, valid⟩

/-- **The ghost half of `ContentTeeth`**: at a blinded cell the live patch carries the
rotation, so the declaration without it disagrees. -/
theorem contentGhost_disagrees : ¬ ContentAgreement contentGhost := by
  intro ghost
  obtain ⟨ps, emitted⟩ := sampleLink_emits_blinded
  obtain ⟨-, -, -, liveGhost, -⟩ := ghost sampleCtx sampleLinkCommand (cellOf blindedStore)
    none none none
  obtain ⟨-, -, -, live, -⟩ := contentAgreement sampleCtx sampleLinkCommand (cellOf blindedStore)
    none none none
  have withRotation := (live _ rfl (Or.inl rfl)).2.2 ps emitted
  have withoutRotation : DeclaredResourceController.targetPatch sampleCtx.snapshot sampleCtx.semantics
      sampleCtx.ambient sampleCtx.command
      (contentTarget sampleCtx contentSpec.version (cellOf blindedStore).root sampleLinkCommand none none none)
      (cellOf blindedStore) = ps ++ [] := (liveGhost _ rfl (Or.inl rfl)).2.2 ps emitted
  rw [withRotation] at withoutRotation
  have rotation : HyperdocumentCell.contentBlinding.patch blindedStore sampleCtx.ambient.height ≠ [] := by
    unfold StoreCodec.Blinding.patch
    simp [blindedStore, StoreCodec.Blinding.address, HyperdocumentCell.contentBlinding]
  exact rotation (List.append_cancel_left withoutRotation)

theorem contentTeeth : ContentTeeth := ⟨contentGhost_disagrees, contentNarrowed_incomplete⟩

/-- A valid deployment (three distinct cell ids). -/
def sampleDeployment : DeclaredResourceController.Deployment := ⟨⟨0⟩, 1, 2, 3⟩

/-- The blinded store holds only its blinding, so its records name no two documents. -/
theorem blindedStore_support (address : CAddr) (held : address ∈ blindedStore.support) :
    address = ⟨.blinding, ()⟩ := by
  by_contra other
  rw [Minidregg.Theory.SparseMap.mem_support_iff] at held
  exact held (by
    change Store.set (0 : ContentResource.ContentStore) ⟨.blinding, ()⟩ (some (⟨0⟩ : Digest)) address = _
    rw [Store.set_ne _ _ _ _ other]
    rfl)

theorem blindedCell_law :
    CanonicalCellRegistry.CellLaw sampleDeployment sampleCtx.target
      (⟨.content, cellOf blindedStore⟩ : HostCell) := by
  refine ⟨by decide, ?_⟩
  intro left inLeft right inRight
  rw [blindedStore_support left inLeft, blindedStore_support right inRight]
  exact Or.inr (Or.inr rfl)

/-- Code 1 is bound, so the deployed dispatch there is the controller's arms. -/
theorem liveTargetDispatch_content (bytes : List UInt8) (ctx : HostCtx) (cell : HostCell) :
    liveTargetDispatch 1 bytes ctx cell = hostTargetDispatch 1 bytes ctx cell := by
  unfold liveTargetDispatch
  exact if_neg fun both => by
    have bound : DeclaredResourceController.registeredCode 1 = true := rfl
    rw [bound] at both
    exact Bool.noConfusion both

/-- The content declaration selects the blinded sample cell under the object role. -/
theorem sample_selected :
    DeclaredResourceController.Effect.select DeclaredResourceController.contentEffect
        sampleDeployment sampleCtx.target sampleCtx.kind
        (⟨.content, cellOf blindedStore⟩ : HostCell) = some (cellOf blindedStore) := by
  unfold DeclaredResourceController.Effect.select
  rw [if_pos blindedCell_law]
  rfl

/-- The host context of the sample target at the blinded cell. -/
def sampleHostCtx : HostCtx :=
  hostCtxOf sampleCtx sampleDeployment contentSpec.version (cellOf blindedStore).root none none none

set_option backward.isDefEq.respectTransparency false in
/-- The host dispatch at the blinded cell: the derived executor's post, packed. -/
theorem hostDispatch_blinded : ∃ post,
    EffectSpec.exec contentSpec 1 sampleCtx sampleLinkCommand blindedStore = .ok post ∧
    hostTargetDispatch 1 (ContentResource.commandStream.encode sampleLinkCommand) sampleHostCtx
        (⟨.content, cellOf blindedStore⟩ : HostCell) =
      .ok (DeclaredResourceController.packTarget (hostTarget sampleHostCtx (.content sampleLinkCommand))
        (CellState.materialize (hostTarget sampleHostCtx (.content sampleLinkCommand)).materializer post)) := by
  obtain ⟨ps, emitted⟩ := sampleLink_emits_blinded
  obtain ⟨post, executed⟩ := exec_ok_of_complete (code := 1) contentComplete emitted
  refine ⟨post, executed, ?_⟩
  obtain ⟨-, -, -, live, -⟩ := contentAgreement sampleCtx sampleLinkCommand (cellOf blindedStore)
    none none none
  obtain ⟨computed, valid⟩ := ((live _ rfl (Or.inl rfl)).1 post).1 executed
  have decoded : DeclaredResourceController.payloadStream.toLawful.decode
      (UInt8.ofNat 1 :: ContentResource.commandStream.encode sampleLinkCommand) =
        some (.content sampleLinkCommand) :=
    DeclaredResourceController.payloadStream.toLawful.decode_encode (.content sampleLinkCommand)
  have selected : DeclaredResourceController.selectTarget sampleDeployment
      (hostTarget sampleHostCtx (.content sampleLinkCommand)) (⟨.content, cellOf blindedStore⟩ : HostCell) =
        some (cellOf blindedStore) := by
    simp only [DeclaredResourceController.selectTarget_content, hostTarget, sampleHostCtx, hostCtxOf]
    rw [if_pos blindedCell_law]
  unfold hostTargetDispatch
  rw [if_neg (by decide), decoded]
  simp only
  rw [show sampleHostCtx.deployment = sampleDeployment from rfl, selected]
  simp only
  rw [show DeclaredResourceController.computeTarget sampleHostCtx.snapshot sampleHostCtx.semantics
      sampleHostCtx.ambient sampleHostCtx.command (hostTarget sampleHostCtx (.content sampleLinkCommand))
      (cellOf blindedStore) = .ok post from computed]
  simp only
  have valid' : Patch.ValidFrom (cellOf blindedStore).logical
      (DeclaredResourceController.targetPatch sampleHostCtx.snapshot sampleHostCtx.semantics
        sampleHostCtx.ambient sampleHostCtx.command
        (hostTarget sampleHostCtx (.content sampleLinkCommand)) (cellOf blindedStore)) := valid
  exact if_pos valid'

/-- **The host dispatch's accepted branch, inhabited** (kernel proof): the encoded link
command is admitted at the blinded content cell. -/
theorem hostAccepted : HostAccepted := by
  obtain ⟨post, -, dispatched⟩ := hostDispatch_blinded
  exact ⟨sampleLinkCommand, sampleHostCtx, ⟨.content, cellOf blindedStore⟩, _,
    (liveTargetDispatch_content _ _ _).trans dispatched⟩

#assert_axioms contentComplete
#assert_axioms contentNarrowed_incomplete
#assert_axioms contentAgreement
#assert_axioms contentAccepted
#assert_axioms contentTeeth
#assert_axioms hostAccepted

end Minidregg.Effects.Revival
