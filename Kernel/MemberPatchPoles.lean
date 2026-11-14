/-
# `Kernel/MemberPatchPoles.lean` — the member patch keystone's poles, on the kind definition

`MemberPatchKeystone` (`Kernel/NativeThinConsent.lean`) says a member patch that answers is the
receiver's patch wherever the receiver computes at all. Its poles, on the one registered WRITE
whose declaration states a member patch (the kind definition revision, code 5):

* `MemberPatchSatisfiable`: a kind-definition target whose computation is admitted, whose member
  patch answers, whose patch is not empty, and whose patch run on the loaded store is the
  receiver's post. The keystone's premises hold together and its conclusion is about a real write.
* `MemberPatchGhostRefuted`: the kind definition's semantics with the member patch
  `fun _ _ _ => some []` (a declaration that would show "no change" for every revision) fails
  `MemberExact`. `Effect.member_exact` is a field of the declaration, so that record is not an
  `Effect`: the law has teeth at the declaration, before any theorem about thin consent.

`ComputeTargetWorldArm` (proved: `computeTarget_world_arm`): the world actions' registered
computation is the deleted hand arm's expression.

`ScalarPreparedHeader` (proved: `scalarPreparedHeader`): every prepared scalar target passed the
four checks whose order moved when scalar actions were bound at code 0 (schema version, root,
ordinary role, some action), so none of those refusals has a preparation to charge.
`ScalarMemberGhostRefuted` (proved: `scalarMember_ghost_refuted`): wherever the scalar semantics
admits a write, the member patch that shows "no change" fails `MemberExact`; the admitted write
that inhabits the premise is executed (`Assurance/MemberPatchPoles.lean`).

The other two teeth do not need a sample and are proved beside the keystone
(`MemberPatchUnstatedRefused`, `MemberPatchCommutingRefused`).
-/
module

public import Kernel.NativeThinConsent
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

@[expose] public section

namespace Minidregg.Kernel.NativeThinConsent

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Effects
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController

set_option autoImplicit false

/-! ## Statements -/

/-- **Satisfiable.** Some kind-definition target is computed by the receiver, its member patch
answers at the loaded store, the shown patch is not empty, and the shown patch run on the
loaded store is the receiver's post. -/
def MemberPatchSatisfiable : Prop :=
  ∃ (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (id : Nat) (capability : CapabilityId) (version : Nat) (root : Digest)
    (definition : WorldKindCell.Definition)
    (pre : Materialized WorldKindCell.definitionMaterializer)
    (post : Store WorldKindCell.definitionLayout) (patch : Patch WorldKindCell.definitionLayout),
    computeTarget snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .kindDefinition definition, none, none, none⟩ pre =
      .ok post ∧
    memberPatch command
        ⟨kind, id, capability, version, root, .kindDefinition definition, none, none, none⟩
        pre.logical = .ok patch ∧
    patch ≠ [] ∧ Patch.run pre.logical patch = post

/-- **Teeth (the ghost).** The kind definition's semantics does not admit the member patch that
shows the empty patch for every revision. -/
def MemberPatchGhostRefuted : Prop :=
  ¬ MemberExact kindDefinitionSpec (fun _ _ _ => some [])

/-- **The bridge for world actions.** A world target's computation is the expression the hand
arm of `computeTarget` was before world actions were declared, its one refusal now the
declaration's by name (the kind definition's twin is `computeTarget_kindDefinition_arm`). -/
def ComputeTargetWorldArm : Prop :=
  ∀ (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (id : Nat) (capability : CapabilityId) (version : Nat) (root : Digest)
    (actions : List WorldKindInstance.Action) (observe : Option CapabilityId)
    (audienceEpoch : Option Nat) (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (pre : Materialized WorldKindCell.instanceMaterializer),
    computeTarget snapshot semantics ambient command
        ⟨kind, id, capability, version, root, .world actions, observe, audienceEpoch,
          audienceRoster⟩ pre =
      (if kind != .object then .error Reject.wrongRole
        else if version != 1 then .error Reject.unsupportedVersion
        else if root != pre.root then .error Reject.staleTarget
        else match WorldKindCell.preparePatch pre.logical actions with
          | none => .error (Reject.effect (.refused 4 "worldKind" .empty))
          | some patch =>
            if Patch.ValidFrom pre.logical patch then
              if (WorldKindProjection.footprint pre.logical (Patch.run pre.logical patch)).isNone
              then .error (Reject.effect (.refused 4 "worldKind" .empty))
              else .ok (Patch.run pre.logical patch)
            else .error (Reject.effect (.refused 4 "worldKind" .empty)) :
        Except Reject (Store WorldKindCell.instanceLayout))

/-! ## The sample: a fieldless kind at revision 1, revised to revision 2 -/

def sampleOld : WorldKindCell.Definition :=
  ⟨⟨9, 1, []⟩, StoreCodec.encode (WorldKindDescriptor.wire ⟨9, 1, []⟩) 0⟩

def sampleNext : WorldKindCell.Definition :=
  ⟨⟨9, 2, []⟩, StoreCodec.encode (WorldKindDescriptor.wire ⟨9, 2, []⟩) 0⟩

def sampleStore : Store WorldKindCell.definitionLayout :=
  (0 : Store WorldKindCell.definitionLayout).set WorldKindCell.definitionAddress (some sampleOld)

def samplePre : Materialized WorldKindCell.definitionMaterializer :=
  materialize WorldKindCell.definitionMaterializer sampleStore

def samplePatch : Patch WorldKindCell.definitionLayout := [.write () () sampleOld sampleNext]

/-- An authority snapshot over the empty authority cell. -/
def sampleSnapshot : AuthoritySnapshot :=
  CredentialAuthorityDomain.Snapshot.ofCell ⟨0⟩ 0 (fun _ => false)
    (materialize CredentialAuthorityCell.materializer 0)

def sampleAmbient : Ambient := { federation := ⟨0⟩, height := 0 }

def sampleCommand : Command := { subject := ⟨0⟩, nonce := 0, targets := [] }

theorem sampleNext_valid : sampleNext.Valid 9 := by
  refine ⟨rfl, ?_⟩
  have valid : sampleNext.descriptor.Valid :=
    ⟨List.nodup_nil, List.nodup_nil, fun _ member => absurd member List.not_mem_nil⟩
  unfold WorldKindCell.Definition.instantiate
  rw [dif_pos valid]
  have decoded : StoreCodec.decode (WorldKindDescriptor.wire sampleNext.descriptor)
      sampleNext.defaults = some 0 := StoreCodec.decode_encode _ 0
  rw [decoded]
  rfl

theorem sample_prepared :
    WorldKindCell.prepareDefinition sampleStore sampleNext = some samplePatch := by
  unfold WorldKindCell.prepareDefinition
  have stored : sampleStore WorldKindCell.definitionAddress = some sampleOld := by
    unfold sampleStore
    exact SparseMap.set_eq _ _ _
  rw [stored]
  show (if sampleNext.descriptor.kind = sampleOld.descriptor.kind ∧
      sampleNext.descriptor.revision = sampleOld.descriptor.revision + 1 ∧
      sampleNext.Valid sampleOld.descriptor.kind then some samplePatch else none) = some samplePatch
  rw [if_pos ⟨rfl, rfl, sampleNext_valid⟩]

/-! ## Proofs -/

theorem memberPatch_satisfiable : MemberPatchSatisfiable := by
  refine ⟨sampleSnapshot, ⟨0⟩, sampleAmbient, sampleCommand, .object, 9, ⟨0⟩, 1, samplePre.root,
    sampleNext, samplePre, Patch.run sampleStore samplePatch, samplePatch, ?_, ?_,
    List.cons_ne_nil _ _, rfl⟩
  · rw [computeTarget_kindDefinition_arm]
    have prepared : WorldKindCell.prepareDefinition samplePre.logical sampleNext = some samplePatch :=
      sample_prepared
    have atObject : ¬ ((ResourceKind.object != ResourceKind.object) = true) := by decide
    have atVersion : ¬ (((1 : Nat) != 1) = true) := by decide
    have atRoot : ¬ ((samplePre.root != samplePre.root) = true) := by simp
    rw [if_neg atObject, if_neg atVersion, if_neg atRoot, prepared]
    rfl
  · exact memberPatch_registered_of (code := kindDefinitionCode) (op := sampleNext)
      (kindDefinitionEffect.memberPatch_of rfl rfl sample_prepared)

set_option backward.isDefEq.respectTransparency false in
theorem computeTarget_world_arm : ComputeTargetWorldArm := by
  intro snapshot semantics ambient command kind id capability version root actions observe
    audienceEpoch audienceRoster pre
  show (worldEffect.compute 4 (targetCtx snapshot semantics ambient command kind id
    capability observe audienceEpoch audienceRoster) version root actions pre).mapError
      Reject.ofDispatch = _
  unfold Effect.compute
  rw [world_run]
  have ctxKind : (targetCtx snapshot semantics ambient command kind id capability observe
      audienceEpoch audienceRoster).kind = kind := rfl
  have accepts : worldEffect.spec.accepts kind = (kind == .object) := rfl
  have current : worldEffect.spec.version = 1 := rfl
  have pinned : worldEffect.spec.commutes actions = false := rfl
  rw [ctxKind, accepts, current, pinned]
  by_cases role : (kind == ResourceKind.object) = false
  · have refused : (kind != ResourceKind.object) = true := by simp [bne, role]
    rw [if_pos role, if_pos refused]
    rfl
  have accepted : ¬ (kind != ResourceKind.object) = true := by
    simpa [bne] using role
  rw [if_neg role, if_neg accepted]
  by_cases versioned : version ≠ 1
  · have refused : (version != 1) = true := bne_iff_ne.mpr versioned
    rw [if_pos versioned, if_pos refused]
    rfl
  have current' : ¬ (version != 1) = true := fun refused => versioned (bne_iff_ne.mp refused)
  rw [if_neg versioned, if_neg current']
  by_cases moved : false = false ∧ root ≠ pre.root
  · have refused : (root != pre.root) = true := bne_iff_ne.mpr moved.2
    rw [if_pos moved, if_pos refused]
    rfl
  have same : ¬ (root != pre.root) = true := fun refused => moved ⟨rfl, bne_iff_ne.mp refused⟩
  rw [if_neg moved, if_neg same]
  cases WorldKindCell.preparePatch pre.logical actions with
  | none => rfl
  | some patch =>
    dsimp only
    by_cases valid : Patch.ValidFrom pre.logical patch
    · rw [if_pos valid, if_pos valid]
      by_cases undecoded :
          (WorldKindProjection.footprint pre.logical (Patch.run pre.logical patch)).isNone = true
      · rw [if_pos undecoded, if_pos undecoded]
        rfl
      · rw [if_neg undecoded, if_neg undecoded]
        rfl
    · rw [if_neg valid, if_neg valid]
      rfl

/-! ## Scalar actions (code 0) -/

/-- **The scalar header's refusals are pre-admission.** Every prepared scalar target has schema
version 1, the loaded root for its signed root, an ordinary role and some action. So a scalar
target that fails any of the four (`unsupportedVersion`, `staleTarget`, `accountRequiresBook`,
`emptyActions`), in whatever order the computation names them, has no `PreparedTarget`, and so
no preparation of a command that holds it (`PreparedOn.targets`): the compute plan and the money
plan are fields of a preparation, and there is none to install. The four were fields of the
deleted arm's evidence too (`DeclaredResourceScalar.CellMode`: `versionExact`, `rootExact`,
`ordinary`, `actionsPresent`), so the same held before the binding. -/
def ScalarPreparedHeader : Prop :=
  ∀ (deployment : Deployment) (directory : CellRegistry.Directory Nat Registry)
    (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (id : Nat) (capability : CapabilityId) (version : Nat) (root : Digest)
    (actions : List DeclaredActionLowering.Action) (observe : Option CapabilityId)
    (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command
      ⟨kind, id, capability, version, root, .scalar actions, observe, audienceEpoch,
        audienceRoster⟩),
    version = 1 ∧ root = prepared.pre.root ∧ kind ≠ .account ∧ actions ≠ []

set_option backward.isDefEq.respectTransparency false in
theorem scalarPreparedHeader : ScalarPreparedHeader := by
  intro deployment directory snapshot semantics ambient command kind id capability version root
    actions observe audienceEpoch audienceRoster prepared
  have computed : (scalarEffect.compute 0 (targetCtx snapshot semantics ambient command kind id
      capability observe audienceEpoch audienceRoster) version root actions prepared.pre).mapError
        Reject.ofDispatch = .ok prepared.post := prepared.candidate.modeEvidence.down
  cases dispatched : scalarEffect.compute 0 (targetCtx snapshot semantics ambient command kind id
      capability observe audienceEpoch audienceRoster) version root actions prepared.pre with
  | error refusal => rw [dispatched] at computed; cases computed
  | ok post =>
    obtain ⟨_, versioned, ps, sem, _⟩ := scalarEffect.compute_ok dispatched
    obtain ⟨ordinary, present, _⟩ := scalarSem_ok sem
    exact ⟨versioned, scalarEffect.compute_pinned dispatched rfl, ordinary, present⟩

/-- A declared object cell 41 that declares field 2 and holds nothing else. -/
def scalarStore : Store EffectDeclaration.effectLayout :=
  Store.set 0 (EffectDeclaration.StateKey.fieldDeclared ⟨41⟩ ⟨2⟩).address (some 1)

/-- One write: field 2 is created holding 7. -/
def scalarWrite : List DeclaredActionLowering.Action := [.create (.objectField ⟨41⟩ ⟨2⟩) 7]

/-- **Teeth at the scalar declaration.** Wherever the scalar semantics admits a write, the
declaration with the member patch that shows "no change" fails `MemberExact`. The premise is
inhabited by execution (`Assurance/MemberPatchPoles.lean`, the sample write): the kernel's
`decide` does not reduce the core on a concrete store. -/
def ScalarMemberGhostRefuted : Prop :=
  ∀ (ctx : EffectCtx) (actions : List DeclaredActionLowering.Action)
    (store : Store EffectDeclaration.effectLayout) (ps : Patch EffectDeclaration.effectLayout),
    scalarSpec.sem ctx actions store = .ok ps →
    ¬ MemberExact scalarSpec (fun _ _ _ => some [])

/-- An admitted scalar write is never the empty patch: there is an action and every action
lowers to at least one guarded operation. -/
theorem scalarSem_writes {ctx : EffectCtx} {actions : List DeclaredActionLowering.Action}
    {store : Store EffectDeclaration.effectLayout} {ps : Patch EffectDeclaration.effectLayout}
    (admitted : scalarSpec.sem ctx actions store = .ok ps) : ps ≠ [] := by
  obtain ⟨_, present, core⟩ := scalarSem_ok admitted
  have value := (DeclaredResourceScalar.prepareStore_ok core).1
  subst value
  cases actions with
  | nil => exact absurd rfl present
  | cons action rest =>
    cases action <;>
      simp [DeclaredResourceScalar.actionsPatch, DeclaredActionLowering.Action.ops]

theorem scalarMember_ghost_refuted : ScalarMemberGhostRefuted := by
  intro ctx actions store ps admitted exact
  exact scalarSem_writes admitted (exact ctx actions store ps [] rfl admitted)

theorem memberPatch_ghost_refuted : MemberPatchGhostRefuted := by
  intro exact
  have sem : kindDefinitionSpec.sem
      (targetCtx sampleSnapshot ⟨0⟩ sampleAmbient sampleCommand .object 9 ⟨0⟩ none none none)
      sampleNext sampleStore = .ok samplePatch := by
    exact kindDefinitionSem_some sample_prepared _
  have same := exact _ sampleNext sampleStore samplePatch [] rfl sem
  cases same

#assert_axioms memberPatch_satisfiable memberPatch_ghost_refuted sampleNext_valid sample_prepared
#assert_axioms computeTarget_world_arm scalarPreparedHeader scalarMember_ghost_refuted

end Minidregg.Kernel.NativeThinConsent
