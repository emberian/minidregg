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

`MoneyPreparedUnchanged` (proved: `moneyPreparedUnchanged`): every prepared compute funding or
money consent target is an account at schema version 1 with the signed root and no audience
field, and its post is the loaded store. Its poles are executed
(`Assurance/MemberPatchPoles.lean`): an admitted sample of each, and each refusal by name.

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

/-- **A money consent's target is read, not written.** Every prepared compute funding or money
consent target is an account at schema version 1 whose root is the signed one, carries no
audience field, and its post is the store it was loaded with. -/
def MoneyPreparedUnchanged : Prop :=
  (∀ (deployment : Deployment) (directory : CellRegistry.Directory Nat Registry)
    (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (id : Nat) (capability : CapabilityId) (version : Nat) (root : Digest)
    (funding : ComputeFunding) (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command
      ⟨kind, id, capability, version, root, .computeFunding funding, observe, audienceEpoch,
        audienceRoster⟩),
    kind = .account ∧ version = 1 ∧ root = prepared.pre.root ∧ audienceEpoch = none ∧
      audienceRoster = none ∧ prepared.post = prepared.pre.logical) ∧
  (∀ (deployment : Deployment) (directory : CellRegistry.Directory Nat Registry)
    (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (id : Nat) (capability : CapabilityId) (version : Nat) (root : Digest)
    (consent : MoneyConsent) (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command
      ⟨kind, id, capability, version, root, .moneyConsent consent, observe, audienceEpoch,
        audienceRoster⟩),
    kind = .account ∧ version = 1 ∧ root = prepared.pre.root ∧ audienceEpoch = none ∧
      audienceRoster = none ∧ prepared.post = prepared.pre.logical)

set_option backward.isDefEq.respectTransparency false in
theorem moneyPreparedUnchanged : MoneyPreparedUnchanged := by
  constructor
  · intro deployment directory snapshot semantics ambient command kind id capability version root
      funding observe audienceEpoch audienceRoster prepared
    have computed : (computeFundingEffect.compute 6 (targetCtx snapshot semantics ambient command
        kind id capability observe audienceEpoch audienceRoster) version root funding
          prepared.pre).mapError Reject.ofDispatch = .ok prepared.post :=
      prepared.candidate.modeEvidence.down
    cases dispatched : computeFundingEffect.compute 6 (targetCtx snapshot semantics ambient command
        kind id capability observe audienceEpoch audienceRoster) version root funding
          prepared.pre with
    | error refusal => rw [dispatched] at computed; cases computed
    | ok post =>
      rw [dispatched] at computed
      have same : post = prepared.post := Except.ok.inj computed
      obtain ⟨accepted, versioned, ps, sem, ran⟩ := computeFundingEffect.compute_ok dispatched
      obtain ⟨empty, epoch, roster⟩ :=
        moneySem_ok (O := ComputeFunding) (op := funding) (store := prepared.pre.logical) sem
      subst empty
      have loaded : some prepared.pre.logical = some post := ran
      have role : (kind == ResourceKind.account) = true := accepted
      exact ⟨by simpa using role, versioned,
        computeFundingEffect.compute_pinned dispatched rfl, epoch, roster,
        same ▸ (Option.some.inj loaded).symm⟩
  · intro deployment directory snapshot semantics ambient command kind id capability version root
      consent observe audienceEpoch audienceRoster prepared
    have computed : (moneyConsentEffect.compute 8 (targetCtx snapshot semantics ambient command
        kind id capability observe audienceEpoch audienceRoster) version root consent
          prepared.pre).mapError Reject.ofDispatch = .ok prepared.post :=
      prepared.candidate.modeEvidence.down
    cases dispatched : moneyConsentEffect.compute 8 (targetCtx snapshot semantics ambient command
        kind id capability observe audienceEpoch audienceRoster) version root consent
          prepared.pre with
    | error refusal => rw [dispatched] at computed; cases computed
    | ok post =>
      rw [dispatched] at computed
      have same : post = prepared.post := Except.ok.inj computed
      obtain ⟨accepted, versioned, ps, sem, ran⟩ := moneyConsentEffect.compute_ok dispatched
      obtain ⟨empty, epoch, roster⟩ :=
        moneySem_ok (O := MoneyConsent) (op := consent) (store := prepared.pre.logical) sem
      subst empty
      have loaded : some prepared.pre.logical = some post := ran
      have role : (kind == ResourceKind.account) = true := accepted
      exact ⟨by simpa using role, versioned,
        moneyConsentEffect.compute_pinned dispatched rfl, epoch, roster,
        same ▸ (Option.some.inj loaded).symm⟩

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

/-! ## The stream append's birth (`Effect.born`)

The append is the one declaration that gives birth to a cell: the entry, beside the head its
patch writes. Three statements hold the field: it is exact for the append (a birth exactly when
the semantics admits), it cannot be stated for a refused operation (no declarable `born`
answers at a request the semantics refuses everywhere), and every prepared append target's
patch and birth are the same entry at the loaded head's next position. -/

/-- **Satisfiable and exact.** An append gives birth exactly when its semantics admits. -/
def AppendBornExact : Prop :=
  ∀ (ctx : EffectCtx) (request : StreamCell.Append) (store : Store StreamCell.headLayout),
    (appendEffect.born ctx request store).isSome = true ↔
      ∃ ps, appendEffect.spec.sem ctx request store = .ok ps

/-- A request whose topic is one byte over the bound. -/
def longTopic : StreamCell.Append := ⟨List.replicate (StreamCell.maxTopicBytes + 1) 0, [], none, none⟩

/-- **Teeth.** No declarable birth answers at a refused request: any `born` the law
`BornAdmitted` admits for the append's semantics is `none` at the over-long topic, at every
context and store. A ghost that always states a birth is not a declaration. -/
def BornGhostRefuted : Prop :=
  ∀ (born : EffectCtx → StreamCell.Append → Store StreamCell.headLayout →
      Option (Nat × CellRegistry.PackedCell Registry)),
    BornAdmitted appendSpec born →
      ∀ (ctx : EffectCtx) (store : Store StreamCell.headLayout), born ctx longTopic store = none

/-- **The prepared append.** Every prepared append target is an object at the append's schema
version whose loaded cell holds a head; its patch is the one guarded write of that head with
the entry at the head's next position, and its birth is that same entry's cell. The root is
not among the facts: an append pins none. -/
def AppendPreparedBirth : Prop :=
  ∀ (deployment : Deployment) (directory : CellRegistry.Directory Nat Registry)
    (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (id : Nat) (capability : CapabilityId) (version : Nat) (root : Digest)
    (request : StreamCell.Append) (observe : Option CapabilityId)
    (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command
      ⟨kind, id, capability, version, root, .append request, observe, audienceEpoch,
        audienceRoster⟩),
    kind = .object ∧ version = StreamCell.commandVersion ∧
    ∃ head, StreamCell.headOf prepared.pre.logical = some head ∧
      targetPatch snapshot semantics ambient command
          ⟨kind, id, capability, version, root, .append request, observe, audienceEpoch,
        audienceRoster⟩ prepared.pre =
        [StreamCell.headWriteOp head (StreamCell.appendEntry id head (appendRecord
          (targetCtx snapshot semantics ambient command kind id capability observe
        audienceEpoch audienceRoster) request))] ∧
      targetBirth snapshot semantics ambient command
          ⟨kind, id, capability, version, root, .append request, observe, audienceEpoch,
        audienceRoster⟩ prepared.pre =
        some (entryBirth (StreamCell.appendEntry id head (appendRecord
          (targetCtx snapshot semantics ambient command kind id capability observe
        audienceEpoch audienceRoster) request)))

theorem appendBornExact : AppendBornExact := by
  intro ctx request store
  refine Iff.trans ?_ (appendBorn_iff ctx request store)
  show ((appendedEntry ctx request store).map entryBirth).isSome = true ↔ _
  rw [Option.isSome_map]

theorem bornGhostRefuted : BornGhostRefuted := by
  intro born lawful ctx store
  cases stated : born ctx longTopic store with
  | none => rfl
  | some cell =>
    obtain ⟨ps, admitted⟩ := lawful ctx longTopic store (by rw [stated]; rfl)
    have refused := appendPlan_longTopic ctx longTopic store (by decide)
    have sem : appendSem ctx longTopic store = .ok ps := admitted
    unfold appendSem at sem
    rw [refused] at sem
    cases sem

set_option backward.isDefEq.respectTransparency false in
theorem appendPreparedBirth : AppendPreparedBirth := by
  intro deployment directory snapshot semantics ambient command kind id capability version root
    request observe audienceEpoch audienceRoster prepared
  have computed : (appendEffect.compute 2 (targetCtx snapshot semantics ambient command kind id
      capability observe audienceEpoch audienceRoster) version root request prepared.pre).mapError
        Reject.ofDispatch = .ok prepared.post := prepared.candidate.modeEvidence.down
  cases dispatched : appendEffect.compute 2 (targetCtx snapshot semantics ambient command kind id
      capability observe audienceEpoch audienceRoster) version root request prepared.pre with
  | error refusal => rw [dispatched] at computed; cases computed
  | ok post =>
    obtain ⟨accepted, versioned, ps, sem, _⟩ := appendEffect.compute_ok dispatched
    obtain ⟨head, loaded, planned, _⟩ := appendSem_ok
      (show appendSem (targetCtx snapshot semantics ambient command kind id capability observe
        audienceEpoch audienceRoster) request prepared.pre.logical = .ok ps from sem)
    have object : kind = .object := by
      cases kind
      · rfl
      · exact absurd (show false = true from accepted) Bool.false_ne_true
      · exact absurd (show false = true from accepted) Bool.false_ne_true
    exact ⟨object, versioned, head, loaded, append_patch planned, append_born planned⟩

#assert_axioms appendBornExact bornGhostRefuted appendPreparedBirth
#assert_axioms memberPatch_satisfiable memberPatch_ghost_refuted sampleNext_valid sample_prepared
#assert_axioms computeTarget_world_arm scalarPreparedHeader scalarMember_ghost_refuted moneyPreparedUnchanged

end Minidregg.Kernel.NativeThinConsent
