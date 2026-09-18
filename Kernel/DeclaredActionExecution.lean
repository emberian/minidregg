/-
# Kernel.DeclaredActionExecution -- accepted action batches to durable hyperedges

This module is the structural lowering from one accepted first-order action
batch to the existing canonical runtime carriers.  It introduces no semantic
interpreter: the typed leg contains the existing `AcceptedCellEffect`, the
hyperedge joint patch concatenates that leg's already validated writes, and
the durable intent projects the hyperedge's exact roots, nullifier, event, and
Lean-derived charge.

The single incidence is intentional.  The declaration itself is a multi-action
atomic batch under one exact authority target.  Cross-authority joint turns
remain the ordinary multi-incidence `TypedCellHyperedge` construction.
-/
import Compiler.DeclaredActionBytes
import Kernel.DeclaredHyperedgeWitness
import Kernel.DurableCommitProtocol

namespace Minidregg.Kernel.DeclaredActionExecution

open Minidregg.Compiler.DeclaredActionBytes
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.TypedCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## The exact single-incidence typed hyperedge -/

/-- A closed supplied-state adapter retained for this migration carrier and
its inhabitation witnesses. Receiving controllers must instead project
authority from their canonical authority page and retain its durable read
guard; this constant function is not that deployment refinement. -/
def projection (authState : AuthState) :
    AuthorizationProjection DeclaredTurn.effectSchema.{0, 0} where
  project := fun _ => authState

def leg {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    Leg portal authState pre where
  Nullifier := Nat
  family := family target context pre
  kind := kind
  request := context.request declaration
  declaration := declaration
  outcome := ()
  accepted := accepted.cellEffect

def typedDeclaration {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    TypedCellHyperedge.Declaration DeclaredTurn.effectSchema.{0, 0} M portal
      (projection authState) Unit where
  pre := pre
  apex := accepted.cellEffect.prepared.postRoot
  legs := fun _ => leg accepted
  composition := { fieldMode := .canonical, order := [()] }

/-- Read the actual supplied leg's accepted pre/post balances over the account
support of that leg's validated footprint. Neither a captured declaration nor
a caller-supplied posting vector can hide another leg's balance changes. -/
def resourceLaw {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (_accepted : Accepted portal authState context pre declaration) :
    ResourceLaw DeclaredTurn.effectSchema.{0, 0} M portal Digest Int where
  stateDelta := fun before after fields _ resource =>
    ∑ account ∈ balanceAccounts fields,
      (balance after.fields account resource - balance before.fields account resource)

/-- The same validated footprint covers all balances omitted from the law's
finite account sum, including on an arbitrary supplied semantic leg. -/
theorem balance_frame_outside_support
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (leg : Leg portal authState pre) (account : ResourceId .account)
    (resource : Digest) (outside : account ∉ balanceAccounts leg.patch.fieldFootprint) :
    balance leg.post.logical.fields account resource =
      balance pre.logical.fields account resource := by
  have unnamed : .accountBalance account resource ∉ leg.patch.fieldFootprint :=
    fun member => outside (mem_balanceAccounts member)
  have frame := leg.accepted.field_frame (.accountBalance account resource) unnamed
  exact congrArg (fun value : Option Int => value.getD 0) frame

theorem typedShape {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    (typedDeclaration accepted).ShapeValid where
  orderComplete := by
    constructor
    · simp [typedDeclaration]
    · intro incidence
      cases incidence
      simp [typedDeclaration]
  resourcesDisjoint := by
    intro left right different
    cases left
    cases right
    exact absurd rfl different
  fieldsValid := trivial

theorem jointPatch_validated {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    Nonempty (ValidatedPatch M pre (typedDeclaration accepted).jointPatch) := by
  have witness : ∃ validated :
      ValidatedPatch M pre (typedDeclaration accepted).jointPatch,
      validate M pre (typedDeclaration accepted).jointPatch =
        ValidationOutcome.accepted validated := by
    unfold validate
    rw [dif_pos (show (typedDeclaration accepted).jointPatch.expectedPreRoot =
      pre.root from rfl)]
    rw [dif_pos (show (typedDeclaration accepted).jointPatch.fieldFootprint =
      (typedDeclaration accepted).jointPatch.namedFields from rfl)]
    rw [dif_pos (show (typedDeclaration accepted).jointPatch.resourceFootprint =
      (typedDeclaration accepted).jointPatch.namedResources from rfl)]
    exact ⟨_, rfl⟩
  exact ⟨witness.choose⟩

def typedValidated {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    ValidatedPatch M pre (typedDeclaration accepted).jointPatch :=
  Classical.choice (jointPatch_validated accepted)

theorem typedPost_eq {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    (typedValidated accepted).apply = accepted.cellEffect.validated.apply := by
  apply Materialized.ext
  simp [ValidatedPatch.apply, typedDeclaration,
    TypedCellHyperedge.Declaration.jointPatch,
    TypedCellHyperedge.Declaration.legPatch, Leg.patch,
    leg, family, Declaration.patch]

/-- One batch becomes an actual generic typed commit and hence an actual
`Kernel.Hyperedge`, not merely a compatibility certificate. -/
def typedCommit {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    TypedCellHyperedge.Commit (resourceLaw accepted)
      (typedDeclaration accepted) where
  shape := typedShape accepted
  validated := typedValidated accepted
  apexExact := by
    exact congrArg Materialized.root (typedPost_eq accepted)
  fieldsPreserved := by
    intro incidence field _present
    cases incidence
    change (typedValidated accepted).apply.logical.fields field =
      accepted.cellEffect.validated.apply.logical.fields field
    rw [typedPost_eq]
  postconditions := by
    intro incidence
    cases incidence
    change declaration.patch.ResultAt pre.logical (typedValidated accepted).apply.logical
    rw [typedPost_eq accepted]
    exact accepted.cellEffect.postcondition
  jointDeltaExact := by
    funext resource
    conv_rhs => unfold TypedCellHyperedge.Declaration.aggregateDelta
    simp only [Fintype.sum_unique]
    change (typedDeclaration accepted).jointDelta (resourceLaw accepted)
      (typedValidated accepted).apply resource =
        (resourceLaw accepted).delta (leg accepted) resource
    rw [typedPost_eq accepted]
    simp [TypedCellHyperedge.Declaration.jointDelta,
      ResourceLaw.delta,
      typedDeclaration, TypedCellHyperedge.Declaration.jointPatch,
      TypedCellHyperedge.Declaration.legPatch, leg, Leg.patch, Leg.post,
      family, Declaration.patch]
  aggregateBalanced := by
    funext resource
    simpa [TypedCellHyperedge.Declaration.aggregateDelta, ResourceLaw.delta, resourceLaw,
      typedDeclaration, leg, Leg.patch, Leg.post, family] using
      accepted.conserves resource

theorem typed_authority_exact {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    ((typedCommit accepted).legAuthorization ()).evidence =
      accepted.cellEffect.authorization.evidence := rfl

theorem typed_resources_exact {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration)
    (resource : Digest) :
    (typedDeclaration accepted).aggregateDelta (resourceLaw accepted) resource = 0 :=
  congrFun (typedCommit accepted).aggregateBalanced resource

/-! ## Exact metering and durable intent -/

/-- Stable receipt bytes are the exact accepted declaration bytes plus its
authority target and canonical roots. -/
structure Event where
  codecVersion : Nat
  authorityKind : Nat
  authorityTarget : Nat
  declarationBytes : List UInt8
  effectDigest : Digest
  preRoot : Digest
  postRoot : Digest
  deriving DecidableEq, Repr

def event {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) : Event where
  codecVersion := declaration.schemaVersion
  authorityKind := resourceKindTag kind
  authorityTarget := target.value
  declarationBytes := (declarationCodec target).encode declaration
  effectDigest := DeclaredActionLowering.effectDigest declaration
  preRoot := pre.root
  postRoot := accepted.cellEffect.prepared.postRoot

def bounded {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    BoundedPreparedTurn (typedCommit accepted).prepared where
  quote :=
    { upper := exactCharge declaration
      exact := exactCharge declaration
      exact_le_upper := fun _ => Nat.le_refl _ }
  memoryTouches_exact := by
    change declaration.patch.fieldFootprint.card =
      (typedCommit accepted).prepared.delta.fieldFootprint.card +
        (typedCommit accepted).prepared.delta.resourceFootprint.card
    simp [typedCommit, typedDeclaration, TypedCellHyperedge.Declaration.jointPatch,
      TypedCellHyperedge.Declaration.legPatch, Leg.patch,
      leg, family, Declaration.patch]

def durableIntent {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (transactionId cellId : Digest)
    (accepted : Accepted portal authState context pre declaration)
    (available : Charge)
    (funding : ChargeReceipt available (bounded accepted).quote) :
    Intent Digest Digest (typedDeclaration accepted).JointNullifier Event :=
  Intent.ofTypedCellHyperedge transactionId cellId (typedCommit accepted)
    (bounded accepted) available funding (event accepted)

@[simp] theorem durable_exact_charge {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (transactionId cellId : Digest)
    (accepted : Accepted portal authState context pre declaration)
    (available : Charge)
    (funding : ChargeReceipt available (bounded accepted).quote) :
    (durableIntent transactionId cellId accepted available funding).exactCharge =
      exactCharge declaration := rfl

/-- Same-id replay cannot change the receipt bytes. -/
theorem changed_event_replay_rejected
    {TxId CellId Nullifier : Type} [DecidableEq TxId] [DecidableEq CellId]
    [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) (replacement : Event)
    (changed : replacement ≠ intent.event) :
    execute .complete (Snapshot.install before intent)
        { intent with event := replacement } =
      .rejected .transactionConflict := by
  have notSame : intent.sameCheck { intent with event := replacement } ≠ true := by
    intro same
    have payload := (Intent.sameCheck_eq_true_iff intent
      { intent with event := replacement }).mp same
    exact changed payload.2.2.2.symm
  simp [execute, Snapshot.install, Snapshot.lookupRecorded, notSame]

/-! ## Concrete non-vacuity and teeth over the deployed sparse effect cell -/

namespace Witness

open Minidregg.Kernel.DeclaredHyperedgeWitness
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.TypedAuthorizationWitness

def context : RequestContext where
  domain := ⟨1⟩
  semantics := ⟨2⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 0
  height := 9
  policyId := ⟨10⟩
  policyEpoch := 0

/-! ### Separately authorized object and account batches -/

def object : ResourceId .object := ⟨700⟩
def objectField : Digest := ⟨701⟩
def objectKey : EffectDeclaration.StateKey := .objectField object objectField

def multiDeclaration : Declaration object where
  schemaVersion := 1
  expectedPreRoot := effectCell.root
  nonce := 399
  actions :=
    [.create objectKey 3,
     .write objectKey (some 3) 4]

theorem multiValid : ValidAt effectCell multiDeclaration where
  rootExact := rfl
  guardsAndPost := by
    simp [Declaration.run, Declaration.admissionCheck, Action.admissionCheck,
      writableKeyCheck, Declaration.checkedWrites, multiDeclaration,
      Action.checkedWrites, runCheckedWrites, Declaration.fieldWrites,
      CheckedWrite.toFieldWrite, applyFieldWrites, FieldStore.assign,
      effectCell, emptyLogical, objectKey, object, objectField]
    rfl

def multiAuthorization : Authorized permissivePortal authState
    (context.request multiDeclaration) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def multiAccepted :
    Accepted permissivePortal authState context effectCell multiDeclaration :=
  accept multiAuthorization multiValid

theorem multiCompilerAccepts :
    compile object multiDeclaration.schemaVersion
        ((declarationCodec object).encode multiDeclaration) =
      .accepted
        { declaration := multiDeclaration
          schemaVersionExact := rfl
          actionsPresent := by decide
          actionsAdmitted := rfl } :=
  compile_encode_accepted multiDeclaration (by decide) rfl

theorem multiHyperedge_nonempty :
    Nonempty (TypedCellHyperedge.Commit (resourceLaw multiAccepted)
      (typedDeclaration multiAccepted)) :=
  ⟨typedCommit multiAccepted⟩

theorem multi_action_surface :
    multiDeclaration.actions =
      [.create objectKey 3,
       .write objectKey (some 3) 4] := rfl

/-! ### Funded transfer over the existing sparse schema -/

def preLogical : LogicalState DeclaredTurn.effectSchema where
  fields := (effectCell.logical.fields.write debitKey (14 : Int)).write creditKey (0 : Int)
  resources := effectCell.logical.resources

def preCell : Materialized effectMaterializer :=
  materialize effectMaterializer preLogical

def declaration : Declaration source where
  schemaVersion := 1
  expectedPreRoot := preCell.root
  nonce := 400
  actions := [.move source destination asset (some 14) (some 0) amount]

theorem valid : ValidAt preCell declaration where
  rootExact := rfl
  guardsAndPost := by
    simp [Declaration.run, Declaration.admissionCheck, Action.admissionCheck,
      amount, Declaration.checkedWrites, declaration,
      Action.checkedWrites, runCheckedWrites, Declaration.fieldWrites,
      CheckedWrite.toFieldWrite, preCell, preLogical,
      applyFieldWrites, FieldStore.assign, source, destination]
    constructor
    · change (show Option Int from preLogical.fields debitKey) = some 14
      unfold preLogical
      rw [FieldStore.write_other _ (by decide)]
      exact FieldStore.write_self _ _ _
    · rw [Function.update_of_ne (by decide)]
      change (show Option Int from preLogical.fields creditKey) = some 0
      unfold preLogical
      exact FieldStore.write_self _ _ _

def authorization : Authorized permissivePortal authState
    (context.request declaration) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def accepted : Accepted permissivePortal authState context preCell declaration :=
  accept authorization valid

theorem executable_admission_exact :
    admit preCell declaration authorization = some accepted :=
  admit_eq_some authorization valid

theorem compiler_accepts :
    compile source declaration.schemaVersion
        ((declarationCodec source).encode declaration) =
      .accepted
        { declaration := declaration
          schemaVersionExact := rfl
          actionsPresent := by decide
          actionsAdmitted := rfl } :=
  compile_encode_accepted declaration (by decide) rfl

theorem hyperedge_nonempty :
    Nonempty (TypedCellHyperedge.Commit (resourceLaw accepted)
      (typedDeclaration accepted)) :=
  ⟨typedCommit accepted⟩

theorem funded_move_debits_exact :
    balance accepted.cellEffect.prepared.post.logical.fields source asset -
      balance preCell.logical.fields source asset = -amount := by
  simpa [declaration, Declaration.postings, Action.postings, postingDelta,
    source, destination] using accepted.balance_delta source asset

/-! ### One joint turn with separately authorized object and account incidences -/

def jointObjectDeclaration : Declaration object :=
  { multiDeclaration with expectedPreRoot := preCell.root, nonce := 401 }

theorem jointObjectValid : ValidAt preCell jointObjectDeclaration where
  rootExact := rfl
  guardsAndPost := rfl

def jointObjectAuthorization : Authorized permissivePortal authState
    (context.request jointObjectDeclaration) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def jointObjectAccepted :
    Accepted permissivePortal authState context preCell jointObjectDeclaration :=
  accept jointObjectAuthorization jointObjectValid

def jointPost : Materialized effectMaterializer :=
  materialize effectMaterializer
    { fields := applyFieldWrites
        (jointObjectDeclaration.fieldWrites ++ declaration.fieldWrites)
        preCell.logical.fields
      resources := preCell.logical.resources }

/-- The object and account requests are distinct incidences over one canonical
pre-cell. Their footprints are disjoint, so joint installation realizes both
locally accepted posts without overwriting either incidence's changes. -/
def jointDeclaration :
    TypedCellHyperedge.Declaration DeclaredTurn.effectSchema.{0, 0}
      effectMaterializer permissivePortal (projection authState) Bool where
  pre := preCell
  apex := jointPost.root
  legs := fun
    | false => leg jointObjectAccepted
    | true => leg accepted
  composition := { fieldMode := .disjoint, order := [false, true] }

theorem jointShape : jointDeclaration.ShapeValid where
  orderComplete := by
    constructor
    · decide
    · intro incidence
      cases incidence <;> decide
  resourcesDisjoint := by
    intro left right different
    cases left <;> cases right <;> decide
  fieldsValid := by
    intro left right different
    cases left <;> cases right
    · exact False.elim (different rfl)
    · decide
    · decide
    · exact False.elim (different rfl)

theorem joint_validated :
    Nonempty (ValidatedPatch effectMaterializer preCell jointDeclaration.jointPatch) := by
  have witness : ∃ validated :
      ValidatedPatch effectMaterializer preCell jointDeclaration.jointPatch,
      validate effectMaterializer preCell jointDeclaration.jointPatch =
        ValidationOutcome.accepted validated := by
    unfold validate
    rw [dif_pos (show jointDeclaration.jointPatch.expectedPreRoot = preCell.root from rfl)]
    rw [dif_pos (show jointDeclaration.jointPatch.fieldFootprint =
      jointDeclaration.jointPatch.namedFields from rfl)]
    rw [dif_pos (show jointDeclaration.jointPatch.resourceFootprint =
      jointDeclaration.jointPatch.namedResources from rfl)]
    exact ⟨_, rfl⟩
  exact ⟨witness.choose⟩

def jointValidated :
    ValidatedPatch effectMaterializer preCell jointDeclaration.jointPatch :=
  Classical.choice joint_validated

theorem joint_account_support :
    balanceAccounts jointDeclaration.jointPatch.fieldFootprint = {source, destination} := by
  decide

theorem transfer_account_support :
    balanceAccounts declaration.patch.fieldFootprint = {source, destination} := by
  decide

theorem object_account_support :
    balanceAccounts jointObjectDeclaration.patch.fieldFootprint = ∅ := by
  decide

def jointCommit : TypedCellHyperedge.Commit (resourceLaw accepted) jointDeclaration where
  shape := jointShape
  validated := jointValidated
  apexExact := rfl
  fieldsPreserved := by
    intro incidence field present
    cases incidence
    · simp [jointDeclaration, TypedCellHyperedge.Declaration.legPatch,
        Leg.patch, leg, family, Declaration.patch, Declaration.fieldWrites,
        Declaration.checkedWrites, jointObjectDeclaration, multiDeclaration,
        Action.checkedWrites, CheckedWrite.toFieldWrite] at present
      subst field
      rfl
    · simp [jointDeclaration, TypedCellHyperedge.Declaration.legPatch,
        Leg.patch, leg, family, Declaration.patch, Declaration.fieldWrites,
        Declaration.checkedWrites, declaration,
        Action.checkedWrites, CheckedWrite.toFieldWrite] at present
      rcases present with rfl | rfl <;> rfl
  postconditions := by
    intro incidence
    cases incidence
    · change jointObjectDeclaration.patch.ResultAt preCell.logical jointValidated.apply.logical
      constructor
      · intro field present
        simp [Declaration.patch, Declaration.fieldWrites,
          Declaration.checkedWrites, jointObjectDeclaration, multiDeclaration,
          Action.checkedWrites, CheckedWrite.toFieldWrite] at present
        subst field
        rfl
      · intro resource
        exact resource.elim
    · change declaration.patch.ResultAt preCell.logical jointValidated.apply.logical
      constructor
      · intro field present
        simp [Declaration.patch, Declaration.fieldWrites,
          Declaration.checkedWrites, declaration,
          Action.checkedWrites, CheckedWrite.toFieldWrite] at present
        rcases present with rfl | rfl <;> rfl
      · intro resource
        exact resource.elim
  jointDeltaExact := by
    funext resource
    change
      (∑ account ∈ balanceAccounts jointDeclaration.jointPatch.fieldFootprint,
        (balance jointValidated.apply.logical.fields account resource -
          balance preCell.logical.fields account resource)) =
      (∑ account ∈ balanceAccounts declaration.patch.fieldFootprint,
        (balance accepted.cellEffect.prepared.post.logical.fields account resource -
          balance preCell.logical.fields account resource)) +
      (∑ account ∈ balanceAccounts jointObjectDeclaration.patch.fieldFootprint,
        (balance jointObjectAccepted.cellEffect.prepared.post.logical.fields account resource -
          balance preCell.logical.fields account resource))
    rw [joint_account_support, transfer_account_support, object_account_support]
    simp only [Finset.sum_empty, add_zero]
    apply Finset.sum_congr rfl
    intro account member
    rcases Finset.mem_insert.mp member with same | last
    · subst account
      rfl
    · have same := Finset.mem_singleton.mp last
      subst account
      rfl
  aggregateBalanced := by
    funext resource
    have objectBalanced :
        (resourceLaw accepted).delta (leg jointObjectAccepted) resource = 0 := by
      simpa [ResourceLaw.delta, resourceLaw, leg, Leg.patch, Leg.post, family] using
        jointObjectAccepted.conserves resource
    have accountBalanced :
        (resourceLaw accepted).delta (leg accepted) resource = 0 := by
      simpa [ResourceLaw.delta, resourceLaw, leg, Leg.patch, Leg.post, family] using
        accepted.conserves resource
    simpa [TypedCellHyperedge.Declaration.aggregateDelta, jointDeclaration,
      Fintype.sum_bool] using congrArg₂ (· + ·) accountBalanced objectBalanced

theorem joint_account_authority_exact :
    (jointCommit.legAuthorization true).evidence = authorization.evidence := rfl

theorem joint_object_authority_exact :
    (jointCommit.legAuthorization false).evidence = jointObjectAuthorization.evidence := rfl

theorem joint_object_post_exact :
    scalarAt jointCommit.prepared.post.logical.fields objectKey = some 4 := rfl

theorem joint_account_post_exact :
    (balance jointCommit.prepared.post.logical.fields source asset,
      balance jointCommit.prepared.post.logical.fields destination asset) = (7, 7) := rfl

/-- Combining these actions under the source account's one request is refused;
the admitted joint construction above retains both distinct authorities. -/
def wrongSingleTarget : Declaration source :=
  { declaration with actions := jointObjectDeclaration.actions ++ declaration.actions }

theorem wrong_single_target_refused : wrongSingleTarget.run preCell.logical.fields = none :=
  rfl

theorem wrong_single_target_compiler_refused :
    compile source wrongSingleTarget.schemaVersion
        ((declarationCodec source).encode wrongSingleTarget) =
      .rejected .inadmissibleAction :=
  compile_encode_inadmissible wrongSingleTarget (by decide)

theorem wrong_single_target_no_accepted :
    IsEmpty (Accepted permissivePortal authState context preCell wrongSingleTarget) :=
  no_accepted_of_inadmissible rfl

def available : Charge := exactCharge declaration

def funding : ChargeReceipt available (bounded accepted).quote where
  funded := fun _ => Nat.le_refl _

def intent : Intent Digest Digest (typedDeclaration accepted).JointNullifier Event :=
  durableIntent ⟨500⟩ ⟨600⟩ accepted available funding

def jointNullifierDecidableEq :
    DecidableEq (typedDeclaration accepted).JointNullifier := by
  rintro ⟨leftIncidence, left⟩ ⟨rightIncidence, right⟩
  cases leftIncidence
  cases rightIncidence
  change Nat at left right
  exact decidable_of_iff (left = right) (by
    constructor
    · intro same
      cases same
      rfl
    · intro same
      cases same
      rfl)

local instance : DecidableEq (typedDeclaration accepted).JointNullifier :=
  jointNullifierDecidableEq

def changedEvent : Event := { intent.event with declarationBytes := [1] }

theorem changedEvent_ne : changedEvent ≠ intent.event := by decide

theorem retry_idempotent
    (before : Snapshot Digest Digest
      (typedDeclaration accepted).JointNullifier Event) :
    execute .complete (Snapshot.install before intent) intent = .replayed intent :=
  execute_retry_after_install .complete before intent

theorem replay_byte_change_rejected
    (before : Snapshot Digest Digest
      (typedDeclaration accepted).JointNullifier Event) :
    execute .complete (Snapshot.install before intent)
        { intent with event := changedEvent } =
      .rejected .transactionConflict :=
  changed_event_replay_rejected before intent changedEvent changedEvent_ne

/-- Representation-level stale guards fail before any durable installation.
The general accepted-effect root equation and durable `RootWrite` retain this
same value; this witness shows the inequality is constructive. -/
def staleRequest : Request .account :=
  { context.request declaration with
    preStateRoot := ⟨preCell.root.value + 1⟩ }

theorem staleRequest_ne : staleRequest.preStateRoot ≠ preCell.root := by
  intro same
  have values := congrArg Digest.value same
  simp [staleRequest] at values

theorem no_effect_at_stale_request :
    IsEmpty (AcceptedCellEffect (portal := permissivePortal)
      (authState := authState) (family source context preCell) staleRequest preCell declaration ()) :=
  no_cellEffect_of_stale_root staleRequest staleRequest_ne

/-- Copying the correct effect digest and root into authority for a different
account cannot manufacture a generic accepted token. -/
def relabeledRequest : Request .account :=
  { context.request declaration with target := destination }

theorem no_effect_at_relabeled_request :
    IsEmpty (AcceptedCellEffect (portal := permissivePortal)
      (authState := authState) (family source context preCell)
      relabeledRequest preCell declaration ()) :=
  no_cellEffect_of_wrong_target (by decide)

end Witness

/-! ## Axiom audit for the actual-state law and separate-authority joint turn -/

/-- info: 'Minidregg.Kernel.DeclaredActionExecution.typed_resources_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typed_resources_exact
/-- info: 'Minidregg.Kernel.DeclaredActionExecution.balance_frame_outside_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms balance_frame_outside_support
/-- info: 'Minidregg.Kernel.DeclaredActionExecution.Witness.joint_account_post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.joint_account_post_exact
/-- info: 'Minidregg.Kernel.DeclaredActionExecution.Witness.joint_object_post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.joint_object_post_exact
/-- info: 'Minidregg.Kernel.DeclaredActionExecution.Witness.wrong_single_target_no_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.wrong_single_target_no_accepted

end

end Minidregg.Kernel.DeclaredActionExecution
