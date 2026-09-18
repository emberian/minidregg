/-
# TypedCellHyperedgeCompositionWitness -- actual joint-state admission teeth

These witnesses preserve the old rule's premises as ordinary data and prove
that the strengthened commit rejects their actual final states. No live guard
is mutated. The coordinate example needs joint-delta equality even though all
local written values survive; the Book example needs field-outcome preservation
even though the local and joint totals all remain conserved.
-/
import Kernel.DeclaredActionExecution
import Kernel.CanonicalResourceEffect

namespace Minidregg.Kernel.TypedCellHyperedgeCompositionWitness

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.TypedCellHyperedge

set_option autoImplicit false

noncomputable section

namespace AccountCoordinates

open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.TypedAuthorizationWitness
open Minidregg.Kernel.DeclaredActionExecution
open Minidregg.Kernel.DeclaredActionExecution.Witness
open Minidregg.Kernel.DeclaredHyperedgeWitness (source destination asset amount)

def third : ResourceId .account := ⟨102⟩

def second : DeclaredActionLowering.Declaration source where
  schemaVersion := 1
  expectedPreRoot := preCell.root
  nonce := 404
  actions := [.move source third asset (some 14) none amount]

theorem secondValid : ValidAt preCell second where
  rootExact := rfl
  guardsAndPost := rfl

def secondAuthorization : Authorized permissivePortal authState
    (context.request second) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyRevisionExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def secondAccepted : Accepted permissivePortal authState context preCell second :=
  accept secondAuthorization secondValid

def overwrittenPost : Materialized effectMaterializer :=
  materialize effectMaterializer
    { fields := applyFieldWrites (declaration.fieldWrites ++ second.fieldWrites)
        preCell.logical.fields
      resources := preCell.logical.resources }

def overlapping :
    TypedCellHyperedge.Declaration DeclaredTurn.effectSchema.{0, 0}
      effectMaterializer permissivePortal (projection authState) Bool where
  pre := preCell
  apex := overwrittenPost.root
  legs := fun
    | false => leg accepted
    | true => leg secondAccepted
  composition := { fieldMode := .canonical, order := [false, true] }

theorem shape : overlapping.ShapeValid where
  orderComplete := by
    constructor
    · decide
    · intro incidence
      cases incidence <;> decide
  resourcesDisjoint := by
    intro left right _different
    cases left <;> cases right <;> decide
  fieldsValid := trivial

theorem local_aggregate_balanced : overlapping.aggregateDelta (resourceLaw accepted) = 0 := by
  funext resource
  have firstBalanced : (resourceLaw accepted).delta (leg accepted) resource = 0 := by
    simpa [ResourceLaw.delta, resourceLaw, leg, Leg.patch, Leg.post, family] using
      accepted.conserves resource
  have secondBalanced : (resourceLaw accepted).delta (leg secondAccepted) resource = 0 := by
    simpa [ResourceLaw.delta, resourceLaw, leg, Leg.patch, Leg.post, family] using
      secondAccepted.conserves resource
  simpa [TypedCellHyperedge.Declaration.aggregateDelta, overlapping, Fintype.sum_bool]
    using congrArg₂ (· + ·) secondBalanced firstBalanced

/-- These are exactly the old shape/apex/aggregate conditions, with the
verifier-minted joint validation retained as a typed value. -/
theorem old_rule_requirements_hold :
    overlapping.ShapeValid ∧
      overlapping.jointValidated.apply.root = overlapping.apex ∧
      overlapping.aggregateDelta (resourceLaw accepted) = 0 :=
  ⟨shape, rfl, local_aggregate_balanced⟩

theorem overwritten_balances
    (validated : ValidatedPatch effectMaterializer preCell overlapping.jointPatch) :
    (balance validated.apply.logical.fields source asset,
      balance validated.apply.logical.fields destination asset,
      balance validated.apply.logical.fields third asset) = (7, 7, 7) := rfl

/-- Preserving every local written value alone does not prevent the repeated
debit from being counted twice while being installed once. -/
theorem written_outcomes_survive : overlapping.FieldOutcomesPreserved overwrittenPost := by
  intro incidence field present
  cases incidence
  · simp [overlapping, TypedCellHyperedge.Declaration.legPatch,
      Leg.patch, leg, family, Declaration.patch, Declaration.fieldWrites,
      Declaration.checkedWrites, declaration,
      Action.checkedWrites, CheckedWrite.toFieldWrite] at present
    rcases present with rfl | rfl <;> rfl
  · simp [overlapping, TypedCellHyperedge.Declaration.legPatch,
      Leg.patch, leg, family, Declaration.patch, Declaration.fieldWrites,
      Declaration.checkedWrites, second,
      Action.checkedWrites, CheckedWrite.toFieldWrite] at present
    rcases present with rfl | rfl <;> rfl

theorem joint_delta_seven
    (validated : ValidatedPatch effectMaterializer preCell overlapping.jointPatch) :
    overlapping.jointDelta (resourceLaw accepted) validated.apply asset = 7 := by
  change overlapping.jointDelta (resourceLaw accepted) overwrittenPost asset = 7
  decide

theorem new_commit_refused : IsEmpty (Commit (resourceLaw accepted) overlapping) := by
  apply no_commit_of_nonzero_joint_resource _ _ asset
  intro validated
  have value : overlapping.jointDelta (resourceLaw accepted) validated.apply asset = 7 :=
    joint_delta_seven validated
  intro zero
  have impossible : (7 : Int) = 0 := value.symm.trans zero
  contradiction

end AccountCoordinates

namespace WholeBook

open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.TypedAuthorizationWitness

local instance : DecidableEq CanonicalResourceKernel.schema.Field :=
  inferInstanceAs (DecidableEq CanonicalResourceKernel.Field)
local instance : DecidableEq CanonicalResourceKernel.schema.Resource :=
  inferInstanceAs (DecidableEq Empty)

def fee : Operation := .fee 1 2 0 1
def payment : Operation := .transfer 1 0 0 2

def context : CanonicalResourceEffect.RequestContext where
  domain := ⟨1⟩
  semantics := ⟨2⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 0
  nonce := 800
  height := 9
  policyId := ⟨10⟩
  policyEpoch := 0
  policyRevision := 0

def projection : AuthorizationProjection CanonicalResourceKernel.schema where
  project := fun _ => authState

def authorization (operation : Operation) : Authorized permissivePortal authState
    (context.request witnessCell operation) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyRevisionExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def feeAccepted : CanonicalResourceKernel.Accepted witnessCell fee :=
  CanonicalResourceKernel.Accepted.ofAdmission
    { sourcePresent := by decide
      destinationPresent := by decide
      sourceSolvent := Or.inr (by decide)
      leaseWellFormed := trivial }

def paymentAccepted : CanonicalResourceKernel.Accepted witnessCell payment :=
  CanonicalResourceKernel.Accepted.ofAdmission
    { sourcePresent := by decide
      destinationPresent := by decide
      sourceSolvent := Or.inr (by decide)
      leaseWellFormed := trivial }

def feeLeg : Leg permissivePortal authState witnessCell :=
  CanonicalResourceEffect.toTypedLeg feeAccepted context (authorization fee)

def paymentLeg : Leg permissivePortal authState witnessCell :=
  CanonicalResourceEffect.toTypedLeg paymentAccepted context (authorization payment)

def overlapping : TypedCellHyperedge.Declaration CanonicalResourceKernel.schema
    CanonicalResourceKernel.materializer permissivePortal projection Bool where
  pre := witnessCell
  apex := paymentAccepted.post.root
  legs := fun
    | false => feeLeg
    | true => paymentLeg
  composition := { fieldMode := .canonical, order := [false, true] }

def law := CanonicalResourceEffect.typedResourceLaw
  CanonicalResourceKernel.materializer permissivePortal

theorem shape : overlapping.ShapeValid where
  orderComplete := by
    constructor
    · decide
    · intro incidence
      cases incidence <;> decide
  resourcesDisjoint := by
    intro left right _different
    cases left <;> cases right <;> decide
  fieldsValid := trivial

theorem post_is_last_book
    (validated : ValidatedPatch CanonicalResourceKernel.materializer witnessCell
      overlapping.jointPatch) :
    validated.apply = paymentAccepted.post := by
  apply Materialized.ext
  apply congrArg (fun fields : FieldStore CanonicalResourceKernel.schema =>
    ({ fields := fields, resources := witnessCell.logical.resources } :
      LogicalState CanonicalResourceKernel.schema))
  apply DFinsupp.ext
  intro field
  cases field
  rfl

theorem local_aggregate_balanced : overlapping.aggregateDelta law = 0 := by
  funext asset
  have feeBalanced : law.delta feeLeg asset = 0 :=
    CanonicalResourceEffect.typedResourceLaw_delta_toTypedLeg
      feeAccepted context (authorization fee) asset
  have paymentBalanced : law.delta paymentLeg asset = 0 :=
    CanonicalResourceEffect.typedResourceLaw_delta_toTypedLeg
      paymentAccepted context (authorization payment) asset
  simpa [TypedCellHyperedge.Declaration.aggregateDelta, overlapping, Fintype.sum_bool]
    using congrArg₂ (· + ·) paymentBalanced feeBalanced

/-- Even the strengthened actual joint-total check cannot detect the lost
fee: the later whole-book replacement remains a balanced payment. -/
theorem joint_delta_zero
    (validated : ValidatedPatch CanonicalResourceKernel.materializer witnessCell
      overlapping.jointPatch) :
    overlapping.jointDelta law validated.apply = 0 := by
  funext asset
  rw [post_is_last_book]
  change (logicalBook paymentAccepted.post.logical).totalAsset asset -
    (logicalBook witnessCell.logical).totalAsset asset = 0
  exact sub_eq_zero.mpr (paymentAccepted.conserves asset)

theorem old_rule_requirements_hold :
    overlapping.ShapeValid ∧
      overlapping.jointValidated.apply.root = overlapping.apex ∧
      overlapping.aggregateDelta law = 0 :=
  ⟨shape, congrArg Materialized.root (post_is_last_book _), local_aggregate_balanced⟩

theorem collector_fee_would_be_lost
    (validated : ValidatedPatch CanonicalResourceKernel.materializer witnessCell
      overlapping.jointPatch) :
    (logicalBook validated.apply.logical).balance 2 0 = 3 ∧
      (logicalBook feeLeg.post.logical).balance 2 0 = 4 := by
  rw [post_is_last_book]
  decide

theorem new_commit_refused : IsEmpty (Commit law overlapping) := by
  apply no_commit_of_lost_field law overlapping false .book
  · change .book ∈ ({.book} : Finset CanonicalResourceKernel.Field)
    exact Finset.mem_singleton_self _
  · intro validated same
    have observed := congrArg
      (fun value : Option Book => (value.getD Book.empty).balance 2 0) same
    change (logicalBook validated.apply.logical).balance 2 0 =
      (logicalBook feeLeg.post.logical).balance 2 0 at observed
    have actual : (logicalBook validated.apply.logical).balance 2 0 = 3 :=
      (collector_fee_would_be_lost validated).1
    have accepted : (logicalBook feeLeg.post.logical).balance 2 0 = 4 :=
      (collector_fee_would_be_lost validated).2
    have impossible : (3 : Int) = 4 := actual.symm.trans (observed.trans accepted)
    contradiction

/-- The intended sequential computation remains available in the canonical
source language: it derives one final book after both admitted operations. -/
def orderedBatch : Batch where
  registrations := []
  operations := [fee, payment]

def orderedAccepted : AcceptedBatch witnessCell orderedBatch :=
  AcceptedBatch.ofAdmission (by decide)

theorem ordered_batch_retains_both_effects :
    (logicalBook orderedAccepted.post.logical).balance 1 0 = 2 ∧
      (logicalBook orderedAccepted.post.logical).balance 2 0 = 4 ∧
      (logicalBook orderedAccepted.post.logical).balance 0 0 = -6 := by
  decide

end WholeBook

/-! ## Named source-statement audit pins -/

/-- info: 'Minidregg.Kernel.TypedCellHyperedgeCompositionWitness.AccountCoordinates.old_rule_requirements_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccountCoordinates.old_rule_requirements_hold

/-- info: 'Minidregg.Kernel.TypedCellHyperedgeCompositionWitness.AccountCoordinates.written_outcomes_survive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccountCoordinates.written_outcomes_survive

/-- info: 'Minidregg.Kernel.TypedCellHyperedgeCompositionWitness.AccountCoordinates.new_commit_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccountCoordinates.new_commit_refused

/-- info: 'Minidregg.Kernel.TypedCellHyperedgeCompositionWitness.WholeBook.old_rule_requirements_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WholeBook.old_rule_requirements_hold

/-- info: 'Minidregg.Kernel.TypedCellHyperedgeCompositionWitness.WholeBook.joint_delta_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WholeBook.joint_delta_zero

/-- info: 'Minidregg.Kernel.TypedCellHyperedgeCompositionWitness.WholeBook.new_commit_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WholeBook.new_commit_refused

/-- info: 'Minidregg.Kernel.TypedCellHyperedgeCompositionWitness.WholeBook.ordered_batch_retains_both_effects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WholeBook.ordered_batch_retains_both_effects

end
end Minidregg.Kernel.TypedCellHyperedgeCompositionWitness
