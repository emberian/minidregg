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
  family := family target
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

/-- The resource law is closed over this exact first-order declaration.  It
reads the declaration-derived full-width posting sum; no executor counter or
caller callback participates. -/
def resourceLaw {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (_accepted : Accepted portal authState context pre declaration) :
    ResourceLaw DeclaredTurn.effectSchema.{0, 0} M portal Digest Int where
  delta := fun _ resource => postingSum declaration.postings resource

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
    have cells : (typedValidated accepted).apply =
        accepted.cellEffect.validated.apply := by
      apply Materialized.ext
      simp [ValidatedPatch.apply, typedDeclaration,
        TypedCellHyperedge.Declaration.jointPatch,
        TypedCellHyperedge.Declaration.legPatch, Leg.patch,
        leg, family, Declaration.patch]
    exact congrArg Materialized.root cells
  aggregateBalanced := by
    funext resource
    simp [TypedCellHyperedge.Declaration.aggregateDelta, resourceLaw,
      Declaration.postingSum_zero]

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

/-! ### A genuine create -> write -> move batch -/

def object : ResourceId .object := ⟨700⟩
def objectField : Digest := ⟨701⟩
def objectKey : EffectDeclaration.StateKey := .objectField object objectField

def multiDeclaration : Declaration source where
  schemaVersion := 1
  expectedPreRoot := effectCell.root
  nonce := 399
  actions :=
    [.create objectKey 3,
     .write objectKey (some 3) 4,
     .move source destination asset none none amount]

theorem multiValid : ValidAt effectCell multiDeclaration where
  rootExact := rfl
  guardsAndPost := by
    simp [Declaration.run, Declaration.checkedWrites, multiDeclaration,
      Action.checkedWrites, runCheckedWrites, Declaration.fieldWrites,
      CheckedWrite.toFieldWrite, applyFieldWrites, FieldStore.assign,
      effectCell, emptyLogical, objectKey, object, objectField,
      source, destination]
    constructor
    · change (show Option Int from
          (0 : FieldStore DeclaredTurn.effectSchema.{0, 0}) objectKey) = none
      rfl
    constructor
    · change (show Option Int from
          (0 : FieldStore DeclaredTurn.effectSchema.{0, 0})
            (.accountBalance source asset)) = none
      rfl
    · rw [Function.update_of_ne (by decide)]
      rw [Function.update_of_ne (by decide)]
      change (show Option Int from
        (0 : FieldStore DeclaredTurn.effectSchema.{0, 0})
          (.accountBalance destination asset)) = none
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
    compile source multiDeclaration.schemaVersion
        ((declarationCodec source).encode multiDeclaration) =
      .accepted
        { declaration := multiDeclaration
          schemaVersionExact := rfl
          actionsPresent := by decide } :=
  compile_encode_accepted multiDeclaration (by decide)

theorem multiHyperedge_nonempty :
    Nonempty (TypedCellHyperedge.Commit (resourceLaw multiAccepted)
      (typedDeclaration multiAccepted)) :=
  ⟨typedCommit multiAccepted⟩

theorem multi_action_surface :
    multiDeclaration.actions =
      [.create objectKey 3,
       .write objectKey (some 3) 4,
       .move source destination asset none none amount] := rfl

/-! ### Exact legacy transfer slice -/

def declaration : Declaration source where
  schemaVersion := 1
  expectedPreRoot := preCell.root
  nonce := 400
  actions := [.move source destination asset (some 0) (some 0) amount]

theorem valid : ValidAt preCell declaration where
  rootExact := rfl
  guardsAndPost := by
    simp [Declaration.run, Declaration.checkedWrites, declaration,
      Action.checkedWrites, runCheckedWrites, Declaration.fieldWrites,
      CheckedWrite.toFieldWrite, preCell, preLogical,
      applyFieldWrites, FieldStore.assign, source, destination]
    constructor
    · change (show Option Int from preLogical.fields debitKey) = some 0
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

theorem compiler_accepts :
    compile source declaration.schemaVersion
        ((declarationCodec source).encode declaration) =
      .accepted
        { declaration := declaration
          schemaVersionExact := rfl
          actionsPresent := by decide } :=
  compile_encode_accepted declaration (by decide)

theorem hyperedge_nonempty :
    Nonempty (TypedCellHyperedge.Commit (resourceLaw accepted)
      (typedDeclaration accepted)) :=
  ⟨typedCommit accepted⟩

theorem legacy_move_exact :
    declaration.patch.fieldWrites =
      Minidregg.Kernel.DeclaredHyperedgeWitness.Migration.debitPatch.fieldWrites := by
  rfl

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
      (authState := authState) (family source) staleRequest preCell declaration ()) :=
  no_cellEffect_of_stale_root staleRequest staleRequest_ne

end Witness

end

end Minidregg.Kernel.DeclaredActionExecution
