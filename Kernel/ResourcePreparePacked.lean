/-
# `Kernel/ResourcePreparePacked.lean` — one target's preparation, read without its evidence

`prepareTarget` returns a `PreparedTarget`, whose fields are indexed by the target and carry the
equations each step established. What it answers (the packed post, or the refusal) is four reads
in order: the slot, the selection, the computation, and `afterTarget` (the patch validated at the
loaded store, the final-post law, the policy source, audience freshness). `prepareTarget_packed`
is that reading, for every target. A statement about what the receiver answers at two targets, or
against a dispatcher, is proved over `receive`, where the target enters only through the three
functions it is given.
-/
module

public import Kernel.ResourceTransaction
public import Theory.AssertAxioms

import all Init.Control.Except

@[expose] public section

namespace Minidregg.Kernel.DeclaredResourceController

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- The receiver's steps after a target's computation: its patch validated at the loaded store,
the run of that patch the computed post, the final-post law on the packed post, the policy
source, audience freshness. It is given the target's materializer, packing, cell id and audience
epoch, not the target: two targets that agree on those are followed alike. -/
def afterTarget (deployment : Deployment) (directory : Directory Nat Registry)
    (snapshot : AuthoritySnapshot) {L : Layout.{0, 0, 0}} (M : Materializer L Digest)
    (pack : Materialized M → PackedCell Registry) (id : Nat) (epoch : Option Nat)
    (before : PackedCell Registry) (pre : Materialized M) (patch : Patch L) (post : Store L) :
    Except Reject (PackedCell Registry) :=
  match Patch.firstDisabled? pre.logical patch with
  | some _ => .error .patchValidation
  | none =>
    if Patch.run pre.logical patch = post then
      if CanonicalCellRegistry.FinalPostLaw deployment id before
          (pack (materialize M (Patch.run pre.logical patch))) then
        match CanonicalCellRegistry.loadPolicySource snapshot.domain directory
            (snapshot.authState.policyAddress ⟨id⟩ (snapshot.authState.policyRevision ⟨id⟩)) with
        | none => .error .policyUnavailable
        | some source =>
          match ObjectAudience.checkFresh source.record.audience id epoch with
          | .error reason => .error (.audience reason)
          | .ok () => .ok (pack (materialize M (Patch.run pre.logical patch)))
      else .error .invalidPost
    else .error .invalidPost

/-- One target's four reads, in the receiver's order. -/
def receive {Cell Out : Type} (slot : CellSlot Registry)
    (select : PackedCell Registry → Option Cell) (compute : Cell → Except Reject Out)
    (after : PackedCell Registry → Cell → Out → Except Reject (PackedCell Registry)) :
    Except Reject (PackedCell Registry) :=
  match slot with
  | .absent => .error .missingTarget
  | .present before =>
    match select before with
    | none => .error .wrongRole
    | some pre =>
      match compute pre with
      | .error reason => .error reason
      | .ok post => after before pre post

theorem validate_rejected_of_disabled {target : Target} (pre : TargetCell target)
    (patch : Patch target.layout) (index : Nat)
    (disabled : Patch.firstDisabled? pre.logical patch = some index) :
    validate target.materializer pre pre.root patch = .rejected (.disabledOperation index) := by
  unfold validate
  rw [dif_pos rfl]
  split
  · rename_i enabled
    rw [disabled] at enabled
    cases enabled
  · rename_i index' reported
    rw [disabled] at reported
    cases reported
    rfl

/-- **What `prepareTarget` answers.** The packed post of one target's preparation, or its
refusal, is `receive` of the slot, the target's selection, its computation, and `afterTarget` at
its patch. -/
theorem prepareTarget_packed (deployment : Deployment) (directory : Directory Nat Registry)
    (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (target : Target) :
    (prepareTarget deployment directory snapshot semantics ambient command target).map
        (fun prepared => packTarget target prepared.candidate.post) =
      receive (directory.slots target.target) (selectTarget deployment target)
        (computeTarget snapshot semantics ambient command target)
        (fun before pre post => afterTarget deployment directory snapshot target.materializer
          (packTarget target) target.target target.audienceEpoch before pre
          (targetPatch snapshot semantics ambient command target pre) post) := by
  unfold prepareTarget
  split
  · rename_i absent
    rw [absent]
    rfl
  · rename_i before present
    conv => rhs; rw [present]
    split
    · rename_i refused
      simp only [receive, refused]
      rfl
    · rename_i pre selected
      split
      · rename_i reason computed
        simp only [receive, selected, computed]
        rfl
      · rename_i post computed
        cases disabled : Patch.firstDisabled? pre.logical
            (targetPatch snapshot semantics ambient command target pre) with
        | some index =>
          have rejected := validate_rejected_of_disabled pre
            (targetPatch snapshot semantics ambient command target pre) index disabled
          split
          · simp only [receive, selected, computed, afterTarget, disabled]
            rfl
          · rename_i validated accepted
            cases rejected.symm.trans accepted
        | none =>
          obtain ⟨validated, accepted⟩ := validate_accepts target.materializer pre pre.root
            (targetPatch snapshot semantics ambient command target pre) rfl
            ((Patch.firstDisabled?_eq_none_iff _ _).1 disabled)
          split
          · rename_i reason rejected
            cases accepted.symm.trans rejected
          · rename_i validated' accepted'
            dsimp only
            split
            · rename_i postExact
              have postExact' : Patch.run pre.logical
                  (targetPatch snapshot semantics ambient command target pre) = post := postExact
              split
              · rename_i postLaw
                have postLaw' : CanonicalCellRegistry.FinalPostLaw deployment target.target before
                    (packTarget target validated'.apply) := postLaw
                rw [validated'.apply_eq_materialize] at postLaw'
                cases source : CanonicalCellRegistry.loadPolicySource snapshot.domain directory
                    (snapshot.authState.policyAddress ⟨target.target⟩
                      (snapshot.authState.policyRevision ⟨target.target⟩)) with
                | none =>
                  simp only [receive, selected, computed, afterTarget, disabled, source]
                  rw [if_pos postExact', if_pos postLaw']
                  rfl
                | some loaded =>
                  simp only [requireSome, bind, Except.bind]
                  split
                  · rename_i reason stale
                    simp only [receive, selected, computed, afterTarget, disabled, source, stale]
                    rw [if_pos postExact', if_pos postLaw']
                    rfl
                  · rename_i fresh
                    simp only [receive, selected, computed, afterTarget, disabled, source, fresh]
                    rw [if_pos postExact', if_pos postLaw']
                    show Except.ok (packTarget target validated'.apply) = _
                    rw [validated'.apply_eq_materialize]
              · rename_i noLaw
                have noLaw' : ¬ CanonicalCellRegistry.FinalPostLaw deployment target.target before
                    (packTarget target (materialize target.materializer (Patch.run pre.logical
                      (targetPatch snapshot semantics ambient command target pre)))) := by
                  intro law
                  rw [← validated'.apply_eq_materialize] at law
                  exact noLaw law
                simp only [receive, selected, computed, afterTarget, disabled]
                rw [if_pos postExact', if_neg noLaw']
                rfl
            · rename_i notExact
              have notExact' : ¬ Patch.run pre.logical
                  (targetPatch snapshot semantics ambient command target pre) = post := notExact
              simp only [receive, selected, computed, afterTarget, disabled]
              rw [if_neg notExact']
              rfl

#assert_axioms prepareTarget_packed

end Minidregg.Kernel.DeclaredResourceController
