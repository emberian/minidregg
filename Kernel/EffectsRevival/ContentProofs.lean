/-
# `Kernel/EffectsRevival/ContentProofs.lean` — `ContentComplete`, PROVED

The content declaration's own obligation (`Kernel/EffectsRevival/Statements.lean`, audited):
every content command the source lowering admits writes only fields in its declared frame
(`contentActionFrame`, action by action), never the blinding, and its emitted descriptor
followed by the kernel's blinding rotation replays.  The frame half is a syntactic
invariant over the lowering's progress (`Emits`), proved helper by helper and action by
action against `ContentResource.step`'s write sites; the replay half is
`ContentResource.run_executes` plus the rotation's guard, which holds because no content
write touches the blinding.
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

abbrev CAddr := Address Hyperdocument.layout

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

theorem contentComplete : ContentComplete := by
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
    simp [contentNarrowed, contentSpec, contentSem, sampleLinkCommand, ContentResource.run,
      ContentResource.step, ContentResource.allocate, Except.map, bind, Except.bind, pure,
      Except.pure]
    rfl
  have inFrame := (complete sampleCtx sampleLinkCommand (0 : ContentResource.ContentStore) _ emitted).1
  have written := inFrame ⟨.links, sampleLink⟩ (by
      change ⟨.links, sampleLink⟩ ∈ (Option.toFinset (some ⟨.links, sampleLink⟩) ∪
        ((storeSubstrate Hyperdocument.layout).footprint
          (contentNarrowed.rotate sampleCtx (0 : ContentResource.ContentStore))) : Finset CAddr)
      exact Finset.mem_union_left _ (Option.mem_toFinset.mpr rfl)) rfl
  simp [contentNarrowed, contentSpec, contentFrame, contentActionFrame, sampleLinkCommand,
    ResourceObservationAdmission.contentFieldAt, ResourceObservationAdmission.contentField] at written

/-! ## The live legacy census is false today. -/

/-- `Payload.content` still carries code 1: the census is refuted until the migration
deletes that constructor. -/
theorem hostLegacyCensusRefutedToday : HostLegacyCensusRefutedToday := fun census =>
  census (.content ⟨[]⟩) (by simp [payloadTag, DeclaredResourceController.payloadStream])

/-! ## `ContentAgreement contentSpec`: the deployed content arm IS the declaration. -/

theorem store_run_iff {L : Layout.{0, 0, 0}} :
    ∀ (ps : List (Store.Op L)) (s s' : Store L),
      (storeSubstrate L).run s ps = some s' ↔ Patch.ValidFrom s ps ∧ Patch.run s ps = s'
  | [], s, s' => by
      show (some s = some s') ↔ (True ∧ s = s')
      exact ⟨fun h => ⟨trivial, Option.some.inj h⟩, fun h => h.2 ▸ rfl⟩
  | p :: ps, s, s' => by
      by_cases enabled : p.Enabled s
      · have stepped : (storeSubstrate L).step p s = some (p.apply s) := by
          simp only [storeSubstrate]; exact if_pos enabled
        simp only [Substrate.run, stepped, Patch.ValidFrom, Patch.run_cons, enabled, true_and]
        exact store_run_iff ps _ s'
      · have stepped : (storeSubstrate L).step p s = none := by
          simp only [storeSubstrate]; exact if_neg enabled
        simp [Substrate.run, stepped, Patch.ValidFrom, enabled]

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
      | .error reason => .error (.content reason)
      | .ok prepared => .ok (Patch.run prepared.post.logical
          (HyperdocumentCell.contentBlinding.patch pre.logical ctx.ambient.height)) := by
  simp [DeclaredResourceController.computeTarget, contentTarget, contentSpec, object, bind,
    Except.bind, pure, Except.pure]
  split
  · rename_i stale
    rcases fresh with same | commuting
    · exact absurd same stale.1
    · simp [contentSpec] at commuting
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
      intro object; simp [contentSpec, object] at rejected
    simp [DeclaredResourceController.computeTarget, contentTarget, notObject, bind, Except.bind]
  · intro version root accepted wrongVersion
    have object : ctx.kind = .object := by simpa [contentSpec] using accepted
    have wrongVersion' : version ≠ ContentResource.commandVersion := wrongVersion
    simp [DeclaredResourceController.computeTarget, contentTarget, object, wrongVersion', bind,
      Except.bind, pure, Except.pure]
  · intro root accepted commutes stale
    have object : ctx.kind = .object := by simpa [contentSpec] using accepted
    have commutes' : command.commutes = false := commutes
    simp [DeclaredResourceController.computeTarget, contentTarget, contentSpec, object, commutes',
      bind, Except.bind, pure, Except.pure]
    intro same
    exact absurd same stale
  · intro root accepted fresh
    have object : ctx.kind = .object := by simpa [contentSpec] using accepted
    rw [computeTarget_content_header ctx command pre observe epoch roster root object fresh]
    by_cases empty : command.actions.isEmpty
    · have refused : contentSpec.sem ctx command pre.logical = .error .emptyActions := by
        simp [contentSpec, contentSem, empty]
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
      · intro r computed
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
          simp [contentSpec, contentSem, empty, ran, Except.map]
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
        · intro r computed
          rw [prepared] at computed
          cases computed
          simp [EffectSpec.exec, refused]
        · intro ps emitted
          rw [refused] at emitted
          cases emitted
      | ok progress =>
        have emitted : contentSpec.sem ctx command pre.logical = .ok progress.2 := by
          simp [contentSpec, contentSem, empty, ran, Except.map]
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
          simp [DeclaredResourceController.targetPatch, contentTarget, ran, contentSpec]
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
        · intro r computed
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
  simp [contentSpec, contentSem, sampleLinkCommand, ContentResource.run,
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
    simp only [DeclaredResourceController.selectTarget, hostTarget, sampleHostCtx, hostCtxOf]
    have object : sampleCtx.kind = .object := rfl
    rw [if_pos object, if_pos blindedCell_law]
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
  exact ⟨sampleLinkCommand, sampleHostCtx, ⟨.content, cellOf blindedStore⟩, _, dispatched⟩

/-! ## The deployed payload decoder, read as a prefix. -/

theorem contentPrefixAgreement : ContentPrefixAgreement := by
  intro rest
  cases decoded : ContentResource.commandStream.decodePrefix rest with
  | none =>
    simp [payloadPrefix, readPrefix, DeclaredResourceController.payloadStream, decoded,
      contentHandler, contentHandlerOf, EffectSpec.comap, contentSpec, List.lookup]
  | some pair =>
    obtain ⟨command, suffix⟩ := pair
    simp [payloadPrefix, readPrefix, DeclaredResourceController.payloadStream, decoded, payloadTag,
      contentHandler, contentHandlerOf, EffectSpec.comap, contentSpec, List.lookup]

theorem contentPrefixAccepts : ContentPrefixAccepts :=
  ⟨⟨[]⟩, [], by
    have decoded := ContentResource.commandStream.decodePrefix_encode ⟨[]⟩ []
    simp only [List.append_nil] at decoded
    simp [payloadPrefix, DeclaredResourceController.payloadStream, payloadTag, decoded]⟩

theorem contentPrefixTeeth : ContentPrefixTeeth := by
  intro same
  have content : readPrefix [(3, contentHandler)] [3] = none := rfl
  have read : payloadPrefix [3] = some (3, [], []) := rfl
  rw [content, read] at same
  cases same

/-! ## Axiom pins. -/

#assert_axioms hostLegacyCensusRefutedToday

#assert_axioms contentComplete
#assert_axioms contentNarrowed_incomplete
#assert_axioms contentAgreement
#assert_axioms contentAccepted
#assert_axioms contentTeeth
#assert_axioms hostAccepted
#assert_axioms contentPrefixAgreement
#assert_axioms contentPrefixAccepts
#assert_axioms contentPrefixTeeth

end Minidregg.Effects.Revival
