/-
# `Kernel/ContentEffect.lean` — the content write's declaration, over the registry's context

The content-cell write behind `doc append` (payload code 1), as an `Effects.Revival.EffectSpec`
over `EffectCtx`, the context every registered effect's semantics reads
(`Kernel/ResourceEffect.lean`), upstream of the registry. Its semantics is the source-owned
lowering `ContentResource.run`; what it reads of its transaction is the signer, the role, the
capability, the transaction's operation id (`EffectCtx.operation`) and, for a transclusion, the
observe capability of the cell the same transaction reads (`EffectCtx.sourceRead`).

Proved here, the obligations an `Effect` record asks of a declaration:

* `contentSpec_complete` (`EffectSpec.Complete`): every content command the lowering admits
  writes only fields in its declared frame (`contentActionFrame`, action by action), never the
  blinding, and its descriptor followed by the kernel's blinding rotation replays. The frame half
  is a syntactic invariant over the lowering's progress (`Emits`), proved helper by helper and
  action by action against `ContentResource.step`'s write sites; the replay half is
  `ContentResource.run_executes` plus the rotation's guard, which holds because no content write
  touches the blinding.
* `contentSpec_writes`: its verb is never an observation.
* `JointSlots.contentProject_unjoint`: no slot of its view is a joint key.

The deployed hand arm (`computeTarget`'s content case) is still what runs; its agreement with
this declaration is `Kernel.EffectsRevival.Statements.ContentAgreement`.
-/
module

public import Kernel.ResourceEffect
public import Kernel.ResourceObservationAdmission
public import Kernel.ContentResource
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

abbrev CAddr := Address Hyperdocument.layout

/-- The fields one content action may write (`ResourceObservationAdmission.contentField`:
links, marks and annotations are `annotations`, every other namespace `body`; an atom is
also named by `atomsOf` of its low half). -/
def contentActionFrame : ContentResource.Action → Finset CellField
  | .createDocument _ _ => {.body}
  | .createAtom atom _ _ => {ResourceObservationAdmission.atomField atom.digest.value, .body}
  | .editAtom edit => {ResourceObservationAdmission.atomField edit.atomId.digest.value}
  | .rewrapAtom atom _ _ => {ResourceObservationAdmission.atomField atom.digest.value}
  | .link .. => {.annotations}
  | .createRun .. => {.body}
  | .annotate .. => {.annotations}
  | .rewrapAnnotation .. => {.annotations}
  | .transclude .. => {.body, .annotations}
  | .editElement _ => {.body}
  | .createContainer _ => {.body}
  | .unlink _ => {.annotations}
  | .mark .. => {.annotations}
  | .unmark _ => {.annotations}
  | .insertRun .. => {.body}

/-- The declared frame of a content command: the union of its actions' frames. -/
def contentFrame (command : ContentResource.Command) : Finset CellField :=
  command.actions.foldr (fun action acc => contentActionFrame action ∪ acc) ∅


abbrev ContentSubstrate := storeSubstrate Hyperdocument.layout

/-! ## The syntactic invariant: a step appends only writes at addresses satisfying `P`. -/

def Emits (P : CAddr → Prop) (progress next : Progress) : Prop :=
  ∃ ops : Patch Hyperdocument.layout, next.2 = progress.2 ++ ops ∧
    ∀ op ∈ ops, ∀ a, op.writeAddress? = some a → P a

theorem Emits.refl (P : CAddr → Prop) (progress : Progress) : Emits P progress progress :=
  ⟨[], by simp, fun _ member => by simp at member⟩

theorem Emits.trans {P : CAddr → Prop} {first second third : Progress}
    (left : Emits P first second) (right : Emits P second third) : Emits P first third := by
  obtain ⟨ops₁, eq₁, ok₁⟩ := left
  obtain ⟨ops₂, eq₂, ok₂⟩ := right
  refine ⟨ops₁ ++ ops₂, by rw [eq₂, eq₁, List.append_assoc], fun op member => ?_⟩
  rcases List.mem_append.mp member with member | member
  · exact ok₁ op member
  · exact ok₂ op member

theorem Emits.mono {P Q : CAddr → Prop} (weaken : ∀ a, P a → Q a) {progress next : Progress}
    (emits : Emits P progress next) : Emits Q progress next := by
  obtain ⟨ops, eq, ok⟩ := emits
  exact ⟨ops, eq, fun op member a written => weaken a (ok op member a written)⟩

theorem Emits.single {P : CAddr → Prop} (progress : Progress) (store : ContentResource.ContentStore)
    (op : Store.Op Hyperdocument.layout) (ok : ∀ a, op.writeAddress? = some a → P a) :
    Emits P progress (store, progress.2 ++ [op]) :=
  ⟨[op], rfl, fun o member => by rw [List.mem_singleton] at member; subst member; exact ok⟩

theorem writeAddress_write {space : Hyperdocument.Namespace} {key : Hyperdocument.Key space}
    {before after : Hyperdocument.Value space} (a : CAddr)
    (written : (Store.Op.write space key before after).writeAddress? = some a) :
    a = ⟨space, key⟩ := (Option.some.inj written).symm

theorem writeAddress_allocate {space : Hyperdocument.Namespace} {key : Hyperdocument.Key space}
    {value : Hyperdocument.Value space} (a : CAddr)
    (written : (Store.Op.allocate space key value).writeAddress? = some a) :
    a = ⟨space, key⟩ := (Option.some.inj written).symm

/-! ## Helpers, each with its write set. -/

theorem allocate_emits {progress next : Progress} {space : Hyperdocument.Namespace}
    {key : Hyperdocument.Key space} {value : Hyperdocument.Value space}
    (accepted : ContentResource.allocate progress space key value = .ok next) :
    Emits (fun a => a = ⟨space, key⟩) progress next := by
  obtain ⟨_, rfl⟩ := ContentResource.allocate_ok accepted
  exact Emits.single _ _ _ writeAddress_allocate

theorem rewriteElement_emits {progress next : Progress} {element : Hyperdocument.ElementId}
    {after : Hyperdocument.ElementRecord}
    (accepted : ContentResource.rewriteElement progress element after = .ok next) :
    Emits (fun a => a.1 = .elements) progress next := by
  obtain ⟨_, _, rfl⟩ := ContentResource.rewriteElement_ok accepted
  exact Emits.single _ _ _ fun a written => by rw [writeAddress_write a written]

theorem reparent_emits {progress next : Progress} {element : Hyperdocument.ElementId}
    {parent : Option Hyperdocument.ElementId}
    (accepted : ContentResource.reparent progress element parent = .ok next) :
    Emits (fun a => a.1 = .elements) progress next := by
  obtain ⟨_, _, rfl⟩ := ContentResource.reparent_ok accepted
  exact Emits.single _ _ _ fun a written => by rw [writeAddress_write a written]

theorem appendLeaf_emits (author : Hyperdocument.PrincipalRef) (operation : Hyperdocument.OperationId)
    (document : Hyperdocument.DocumentId) {progress next : Progress} {leaf : Hyperdocument.ElementId}
    {body : Hyperdocument.ElementBody}
    (accepted : ContentResource.appendLeaf author operation document progress leaf body = .ok next) :
    Emits (fun a => a.1 = .elements) progress next := by
  unfold ContentResource.appendLeaf at accepted
  split at accepted
  · cases accepted
    exact Emits.refl _ _
  · split at accepted
    · cases accepted
    · split at accepted
      · obtain ⟨middle, first, rest⟩ := ContentResource.bind_eq_ok accepted
        exact (rewriteElement_emits first).trans
          ((allocate_emits rest).mono fun a same => by rw [same])
      · cases accepted

theorem editElementStep_emits (operation : Hyperdocument.OperationId)
    (document : Hyperdocument.DocumentId) {progress next : Progress} {edit : ContentResource.EditElement}
    (accepted : ContentResource.editElementStep operation document progress edit = .ok next) :
    Emits (fun a => a.1 = .elements) progress next := by
  unfold ContentResource.editElementStep at accepted
  obtain ⟨⟨record, children⟩, _, rest⟩ := ContentResource.bind_eq_ok accepted
  cases operation_ : edit.op with
  | splice index child =>
      simp only [operation_] at rest
      split at rest
      · split at rest
        · cases rest
        · split at rest
          · cases rest
          · split at rest
            · cases rest
            · split at rest
              · obtain ⟨middle, first, last⟩ := ContentResource.bind_eq_ok rest
                exact (rewriteElement_emits first).trans (reparent_emits last)
              · cases rest
      · cases rest
  | move child index =>
      simp only [operation_] at rest
      split at rest
      · split at rest
        · exact rewriteElement_emits rest
        · cases rest
      · cases rest
  | remove child =>
      simp only [operation_] at rest
      split at rest
      · obtain ⟨middle, first, last⟩ := ContentResource.bind_eq_ok rest
        exact (rewriteElement_emits first).trans (reparent_emits last)
      · cases rest

theorem retireLink_emits {document : Hyperdocument.DocumentId} {operation : Hyperdocument.OperationId}
    {progress next : Progress} {link : Hyperdocument.LinkId}
    (accepted : ContentResource.retireLink document operation progress link = .ok next) :
    Emits (fun a => a.1 = .links) progress next := by
  unfold ContentResource.retireLink at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
      exact Emits.single _ _ _ fun a written => by rw [writeAddress_write a written]
    · cases accepted

theorem markLinkStep_emits {author : Hyperdocument.PrincipalRef} {operation : Hyperdocument.OperationId}
    {document : Hyperdocument.DocumentId} {progress next : Progress} {spec : ContentResource.MarkSpec}
    (accepted : ContentResource.markLinkStep author operation document progress spec = .ok next) :
    Emits (fun a => a.1 = .links) progress next := by
  cases spec with
  | link link target =>
      exact (allocate_emits accepted).mono fun a same => by rw [same]
  | _ =>
      simp only [ContentResource.markLinkStep] at accepted
      cases accepted
      exact Emits.refl _ _

theorem retireMarkLink_emits {document : Hyperdocument.DocumentId} {operation : Hyperdocument.OperationId}
    {progress next : Progress} {kind : Hyperdocument.MarkKind}
    (accepted : ContentResource.retireMarkLink document operation progress kind = .ok next) :
    Emits (fun a => a.1 = .links) progress next := by
  cases kind with
  | link link =>
      simp only [ContentResource.retireMarkLink] at accepted
      split at accepted
      · cases accepted
        exact Emits.refl _ _
      · exact retireLink_emits accepted
  | _ =>
      simp only [ContentResource.retireMarkLink] at accepted
      cases accepted
      exact Emits.refl _ _

/-! ## Fields of addresses. -/

def FieldOk (F : Finset CellField) (a : CAddr) : Prop :=
  ResourceObservationAdmission.contentFieldAt a ∈ F ∧ a.1 ≠ .blinding

theorem fieldOk_space {F : Finset CellField} {a : CAddr} {space : Hyperdocument.Namespace}
    (located : a.1 = space) (notAtoms : space ≠ .atoms) (notBlinding : space ≠ .blinding)
    (member : ResourceObservationAdmission.contentField space ∈ F) : FieldOk F a := by
  obtain ⟨s, k⟩ := a
  simp only at located
  subst located
  refine ⟨?_, notBlinding⟩
  cases s <;> first | exact absurd rfl notAtoms | exact member

theorem fieldOk_atom {F : Finset CellField} {a : CAddr} {atom : Hyperdocument.AtomId}
    (located : a = ⟨.atoms, atom⟩)
    (member : ResourceObservationAdmission.atomField atom.digest.value ∈ F) : FieldOk F a := by
  subst located
  exact ⟨member, fun same => Hyperdocument.Namespace.noConfusion same⟩

theorem fieldOk_at {F : Finset CellField} {a : CAddr} {space : Hyperdocument.Namespace}
    {key : Hyperdocument.Key space} (same : a = ⟨space, key⟩) (notAtoms : space ≠ .atoms)
    (notBlinding : space ≠ .blinding)
    (member : ResourceObservationAdmission.contentField space ∈ F) : FieldOk F a :=
  fieldOk_space (by subst same; rfl) notAtoms notBlinding member

/-! ## Every accepted action writes inside its declared frame. -/

theorem step_emits (author : Hyperdocument.PrincipalRef) (operation : Hyperdocument.OperationId)
    (document : Hyperdocument.DocumentId) (context : ContentResource.Context)
    (progress next : Progress) (action : ContentResource.Action)
    (accepted : ContentResource.step author operation document context progress action = .ok next) :
    Emits (FieldOk (contentActionFrame action)) progress next := by
  cases action with
  | createDocument root schema =>
      simp only [ContentResource.step] at accepted
      obtain ⟨middle, first, rest⟩ := ContentResource.bind_eq_ok accepted
      exact ((allocate_emits first).mono fun a same =>
          fieldOk_at same (by decide) (by decide) (by simp [contentActionFrame,
            ResourceObservationAdmission.contentField])).trans
        ((allocate_emits rest).mono fun a same =>
          fieldOk_at same (by decide) (by decide) (by simp [contentActionFrame,
            ResourceObservationAdmission.contentField]))
  | createAtom atom kind payload =>
      simp only [ContentResource.step] at accepted
      split at accepted
      · obtain ⟨middle, first, rest⟩ := ContentResource.bind_eq_ok accepted
        exact ((allocate_emits first).mono fun a same =>
            fieldOk_atom same (by simp [contentActionFrame])).trans
          ((appendLeaf_emits author operation document rest).mono fun a located =>
            fieldOk_space located (by decide) (by decide) (by simp [contentActionFrame,
              ResourceObservationAdmission.contentField]))
      · cases accepted
  | editAtom edit =>
      simp only [ContentResource.step] at accepted
      split at accepted
      · unfold ContentResource.replaceAtom at accepted
        split at accepted
        · cases accepted
        · split at accepted
          · cases accepted
          · cases accepted
            exact Emits.single _ _ _ fun a written =>
              fieldOk_atom (writeAddress_write a written) (by simp [contentActionFrame])
      · cases accepted
  | rewrapAtom atom before wrapping =>
      simp only [ContentResource.step, ContentResource.rewrapAtom] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · cases shape : before.kind with
          | text => simp [shape] at accepted
          | inlineObject schema => simp [shape] at accepted
          | sealedObject schema fragment =>
              simp only [shape] at accepted
              cases accepted
              exact Emits.single _ _ _ fun a written =>
                fieldOk_atom (writeAddress_write a written) (by simp [contentActionFrame])
  | link link source target relation =>
      simp only [ContentResource.step] at accepted
      split at accepted
      · exact (allocate_emits accepted).mono fun a same =>
          fieldOk_at same (by decide) (by decide) (by simp [contentActionFrame,
            ResourceObservationAdmission.contentField])
      · cases accepted
  | createRun runId atoms =>
      simp only [ContentResource.step] at accepted
      split at accepted
      · exact (allocate_emits accepted).mono fun a same =>
          fieldOk_at same (by decide) (by decide) (by simp [contentActionFrame,
            ResourceObservationAdmission.contentField])
      · cases accepted
  | annotate annotationId atom revision body =>
      simp only [ContentResource.step] at accepted
      split at accepted
      · exact (allocate_emits accepted).mono fun a same =>
          fieldOk_at same (by decide) (by decide) (by simp [contentActionFrame,
            ResourceObservationAdmission.contentField])
      · cases accepted
  | rewrapAnnotation annotation before wrapping =>
      simp only [ContentResource.step, ContentResource.rewrapAnnotation] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · cases shape : before.body with
          | inline bytes => simp [shape] at accepted
          | reference source => simp [shape] at accepted
          | sealed fragment =>
              simp only [shape] at accepted
              cases accepted
              exact Emits.single _ _ _ fun a written =>
                fieldOk_at (writeAddress_write a written) (by decide) (by decide)
                  (by simp [contentActionFrame, ResourceObservationAdmission.contentField])
  | transclude transclusion link request =>
      cases covered : context.sourceRead request.source with
      | none => simp [ContentResource.step, covered] at accepted
      | some read =>
          simp only [ContentResource.step, covered] at accepted
          obtain ⟨first, firstOk, rest⟩ := ContentResource.bind_eq_ok accepted
          obtain ⟨second, secondOk, last⟩ := ContentResource.bind_eq_ok rest
          exact (((allocate_emits firstOk).mono fun a same =>
              fieldOk_at same (by decide) (by decide) (by simp [contentActionFrame,
                ResourceObservationAdmission.contentField])).trans
            ((allocate_emits secondOk).mono fun a same =>
              fieldOk_at same (by decide) (by decide) (by simp [contentActionFrame,
                ResourceObservationAdmission.contentField]))).trans
            ((appendLeaf_emits author operation document last).mono fun a located =>
              fieldOk_space located (by decide) (by decide) (by simp [contentActionFrame,
                ResourceObservationAdmission.contentField]))
  | editElement edit =>
      exact (editElementStep_emits operation document accepted).mono fun a located =>
        fieldOk_space located (by decide) (by decide) (by simp [contentActionFrame,
          ResourceObservationAdmission.contentField])
  | createContainer element =>
      simp only [ContentResource.step] at accepted
      split at accepted
      · cases accepted
      · exact (appendLeaf_emits author operation document accepted).mono fun a located =>
          fieldOk_space located (by decide) (by decide) (by simp [contentActionFrame,
            ResourceObservationAdmission.contentField])
  | unlink link =>
      simp only [ContentResource.step] at accepted
      exact (retireLink_emits accepted).mono fun a located =>
        fieldOk_space located (by decide) (by decide) (by simp [contentActionFrame,
          ResourceObservationAdmission.contentField])
  | mark mark request =>
      simp only [ContentResource.step] at accepted
      obtain ⟨_, _, middle, first, rest⟩ := ContentResource.markStep_ok accepted
      exact ((allocate_emits first).mono fun a same =>
          fieldOk_at same (by decide) (by decide) (by simp [contentActionFrame,
            ResourceObservationAdmission.contentField])).trans
        ((markLinkStep_emits rest).mono fun a located =>
          fieldOk_space located (by decide) (by decide) (by simp [contentActionFrame,
            ResourceObservationAdmission.contentField]))
  | unmark mark =>
      simp only [ContentResource.step] at accepted
      obtain ⟨before, _, _, _, _, rest⟩ := ContentResource.unmarkStep_ok accepted
      exact (Emits.single (P := FieldOk (contentActionFrame (.unmark mark))) progress _ _
          fun a written => fieldOk_at (writeAddress_write a written) (by decide)
            (by decide) (by simp [contentActionFrame, ResourceObservationAdmission.contentField])).trans
        ((retireMarkLink_emits rest).mono fun a located =>
          fieldOk_space located (by decide) (by decide) (by simp [contentActionFrame,
            ResourceObservationAdmission.contentField]))
  | insertRun runId anchor atoms =>
      simp only [ContentResource.step] at accepted
      obtain ⟨before, cut, _, _, _, _, _, rfl⟩ := ContentResource.insertRunStep_ok accepted
      exact Emits.single _ _ _ fun a written =>
        fieldOk_at (writeAddress_write a written) (by decide) (by decide)
          (by simp [contentActionFrame, ResourceObservationAdmission.contentField])

/-! ## Over the whole command. -/

theorem contentActionFrame_subset {action : ContentResource.Action}
    {actions : List ContentResource.Action} (member : action ∈ actions) :
    contentActionFrame action ⊆ actions.foldr (fun action acc => contentActionFrame action ∪ acc) ∅ := by
  induction actions with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Finset.subset_union_left
      · exact (ih member).trans Finset.subset_union_right

theorem run_emits (author : Hyperdocument.PrincipalRef) (operation : Hyperdocument.OperationId)
    (document : Hyperdocument.DocumentId) (context : ContentResource.Context)
    (pre : ContentResource.ContentStore) (command : ContentResource.Command) (next : Progress)
    (accepted : ContentResource.run author operation document context pre command = .ok next) :
    Emits (FieldOk (contentFrame command)) (pre, []) next := by
  suffices general : ∀ (actions : List ContentResource.Action) (progress : Progress),
      (∀ action ∈ actions, action ∈ command.actions) →
      actions.foldlM (ContentResource.step author operation document context) progress = .ok next →
        Emits (FieldOk (contentFrame command)) progress next from
    general command.actions (pre, []) (fun _ member => member) accepted
  intro actions
  induction actions with
  | nil =>
      intro progress _ done
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at done
      rw [done]
      exact Emits.refl _ _
  | cons action rest ih =>
      intro progress within done
      simp only [List.foldlM_cons, bind, Except.bind] at done
      cases stepped : ContentResource.step author operation document context progress action with
      | error reason => simp [stepped] at done
      | ok middle =>
          simp only [stepped] at done
          refine ((step_emits author operation document context progress middle action stepped).mono
            fun a ok => ⟨contentActionFrame_subset (within action List.mem_cons_self) ok.1, ok.2⟩).trans
            (ih middle (fun a member => within a (List.mem_cons_of_mem _ member)) done)

/-! ## Store-substrate replay. -/

theorem store_run_validFrom {L : Layout.{0, 0, 0}} :
    ∀ (ps : List (Store.Op L)) (s : Store L), Patch.ValidFrom s ps →
      (storeSubstrate L).run s ps = some (Patch.run s ps)
  | [], _, _ => rfl
  | p :: ps, s, valid => by
      obtain ⟨enabled, rest⟩ := valid
      have stepped : (storeSubstrate L).step p s = some (p.apply s) := by
        simp only [storeSubstrate]
        exact if_pos enabled
      simp only [Substrate.run, stepped]
      exact store_run_validFrom ps _ rest

set_option backward.isDefEq.respectTransparency false in
theorem store_footprint_mem {L : Layout.{0, 0, 0}} :
    ∀ (ps : List (Store.Op L)) (loc : Address L), loc ∈ (storeSubstrate L).footprint ps →
      ∃ op ∈ ps, op.writeAddress? = some loc
  | [], loc, member => by
      change loc ∈ (∅ : Finset (Address L)) at member
      simp at member
  | p :: ps, loc, member => by
      change loc ∈ (p.writeAddress?.toFinset ∪
        ((storeSubstrate L).footprint ps : Finset (Address L)) : Finset (Address L)) at member
      rw [Finset.mem_union] at member
      rcases member with member | member
      · exact ⟨p, List.mem_cons_self, Option.mem_toFinset.mp member⟩
      · obtain ⟨op, inside, written⟩ := store_footprint_mem ps loc member
        exact ⟨op, List.mem_cons_of_mem _ inside, written⟩

/-! ## `ContentComplete`. -/

theorem except_map_ok {α β ε : Type} {f : α → β} {x : Except ε α} {b : β}
    (mapped : Except.map f x = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases mapped
  | ok a => exact ⟨a, rfl, by simpa [Except.map] using mapped⟩
end Minidregg.Effects.Revival

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Effects
open Minidregg.Effects.Revival (contentFrame contentActionFrame ContentSubstrate)
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-- The source policy identity a transclusion records: the policy id, epoch and
revision the source cell's read leg is checked against at this height. -/
def sourcePolicy (snapshot : AuthoritySnapshot) (source : Nat) : Digest :=
  ContentResource.contentDigest "DREGG/CONTENT/DISCLOSURE-POLICY"
    ((StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)).encode
      (source, snapshot.authState.policyEpoch ⟨source⟩, snapshot.authState.policyRevision ⟨source⟩))

/-- What a content command's actions consume of their transaction: the height, and for each
cell the transaction reads observe-only, the observe capability that read carries and the
source's policy. -/
def contentContextOf (ctx : EffectCtx) : ContentResource.Context :=
  ⟨ctx.ambient.height, fun source =>
    (ctx.sourceRead source).map fun capability => ⟨capability, sourcePolicy ctx.snapshot source⟩⟩

/-- The content semantics: the source-owned lowering `ContentResource.run` (REUSED), its patch
the descriptor; an empty command refuses `emptyActions` as `prepareCell` does. -/
def contentSem (ctx : EffectCtx) (command : ContentResource.Command)
    (s : Store Hyperdocument.layout) : Except ContentResource.Reject (Patch Hyperdocument.layout) :=
  if command.actions.isEmpty then .error .emptyActions
  else (ContentResource.run ⟨ctx.subject, ctx.kind, ctx.capability⟩ ⟨ctx.operation ()⟩
      (ContentResource.documentOf ctx.target) (contentContextOf ctx) s command).map Prod.snd

/-- **The content-cell write, declared.** Wire code 1 of the target payload, the action
grammar's codec (`ContentResource.commandStream`), version `ContentResource.commandVersion`. -/
def contentSpec : Revival.EffectSpec EffectCtx ContentSubstrate ContentResource.Command
    ContentResource.Reject where
  opStream := ContentResource.commandStream
  refusalName r := reprStr r
  accepts kind := kind == .object
  version := ContentResource.commandVersion
  sem := contentSem
  rotate ctx s := HyperdocumentCell.contentBlinding.patch s ctx.ambient.height
  rotated := fun (loc : Address Hyperdocument.layout) => match loc.1 with
    | .blinding => true
    | _ => false
  field := ResourceObservationAdmission.contentFieldAt
  amount := fun _ _ => 0
  frame := contentFrame
  verb := fun kind _ => DeclaredResourceScalar.ordinaryVerb kind
  view _ command before after := ContentResource.project before after command
  commutes := ContentResource.Command.commutes

open Minidregg.Effects.Revival in
/-- **The content declaration is complete**: every admitted content command writes only its
declared fields and its descriptor (with the rotate) replays. -/
theorem contentSpec_complete : contentSpec.Complete := by
  intro ctx command s ps emitted
  change ContentResource.ContentStore at s
  change contentSem ctx command s = .ok ps at emitted
  unfold contentSem at emitted
  split at emitted
  · cases emitted
  · obtain ⟨progress, ran, rfl⟩ := except_map_ok emitted
    have executes := ContentResource.run_executes _ _ _ _ s command progress ran
    obtain ⟨ops, opsEq, opsOk⟩ := run_emits _ _ _ _ s command progress ran
    simp only [List.nil_append] at opsEq
    have contentOk : ∀ op ∈ progress.2, ∀ a, op.writeAddress? = some a →
        FieldOk (contentFrame command) a := by
      rw [opsEq]; exact opsOk
    have blindingKept : Patch.run s progress.2 ⟨.blinding, ()⟩ = s ⟨.blinding, ()⟩ := by
      apply Patch.run_frame
      intro member
      obtain ⟨op, inside, written⟩ := (Patch.mem_writeFootprint_iff _ _).1 member
      exact (contentOk op inside _ written).2 rfl
    refine ⟨?_, ?_⟩
    · intro loc member unrotated
      obtain ⟨op, inside, written⟩ := store_footprint_mem _ loc member
      rcases List.mem_append.mp inside with inside | inside
      · exact (contentOk op inside loc written).1
      · change op ∈ HyperdocumentCell.contentBlinding.patch s ctx.ambient.height at inside
        unfold StoreCodec.Blinding.patch at inside
        split at inside
        · rw [List.mem_singleton] at inside
          subst inside
          rw [writeAddress_write loc written] at unrotated
          exact absurd unrotated (by decide)
        · simp at inside
    · change ((storeSubstrate Hyperdocument.layout).run s
          (progress.2 ++ HyperdocumentCell.contentBlinding.patch s ctx.ambient.height)).isSome = true
      rw [store_run_validFrom (L := Hyperdocument.layout) _ _
        ((Patch.validFrom_append _ _ _).2 ⟨executes.1, ?_⟩)]
      · rfl
      · change Patch.ValidFrom (Patch.run s progress.2)
          (HyperdocumentCell.contentBlinding.patch s ctx.ambient.height)
        unfold StoreCodec.Blinding.patch
        split
        · rename_i value present
          refine ⟨⟨rfl, ?_⟩, trivial⟩
          change Patch.run s progress.2 ⟨.blinding, ()⟩ = some value
          rw [blindingKept]
          exact present
        · trivial

/-- A content command is never authorized as an observation. -/
theorem contentSpec_writes (kind : ResourceKind) (command : ContentResource.Command) :
    observes (contentSpec.verb kind command) = false := by
  cases kind <;> rfl

namespace JointSlots

theorem contentProject_unjoint (before after : ContentResource.ContentStore) (command : ContentResource.Command) :
    Unjoint (ContentResource.project before after command) := by
  intro p hp
  simp only [ContentResource.project, List.mem_cons, List.not_mem_nil, or_false] at hp
  -- One case per content slot, however many the projection has (K-CONTENT
  -- added five); every key starts with `content/`.
  repeat' (first | (rcases hp with rfl | hp) | subst hp)
  all_goals (dsimp only; decide)

end JointSlots

#assert_axioms contentSpec_complete contentSpec_writes JointSlots.contentProject_unjoint

end Minidregg.Kernel.DeclaredResourceController
