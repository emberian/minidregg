/-
# Kernel.DeclaredHyperedgeCost -- exact resource effects for flat joint turns

This module meters the executable flat hyperedge without reintroducing a call
forest.  Its static upper bound belongs to the declaration; its exact charge is
a Lean function of the exact committed post.  The incidence and memory-touch
coordinates are pinned to the declaration's finite family and canonical patch
footprint.  Fees and storage leases are derived from an explicit tariff rather
than trusted executor counters.

`executeMetered` remains data-only.  It first runs the existing semantic
executor, then performs the finite Lean-owned funding check.  Semantic
rejection and budget failure expose neither the candidate post nor a budget
delta.  Network and side-effect coordinates reserve committed handler intent;
this module does not claim that physical I/O has occurred.
-/
import Kernel.DeclaredHyperedge
import Theory.ResourceCost

namespace Minidregg.Kernel.DeclaredHyperedgeCost

open Minidregg.Kernel.DeclaredHyperedge
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CellState
open Minidregg.Theory.ResourceCost

set_option autoImplicit false

local instance effectSchemaFieldDecidableEq :
    DecidableEq DeclaredTurn.effectSchema.Field := by
  change DecidableEq EffectDeclaration.StateKey
  infer_instance

local instance effectSchemaResourceDecidableEq :
    DecidableEq DeclaredTurn.effectSchema.Resource := by
  change DecidableEq Empty
  infer_instance

/-! ## Tariffs and declaration-indexed cost semantics -/

/-- Pricing is explicit protocol data.  Fee rates apply only to operational
lanes; `feeDebit` and `leaseByteBlocks` cannot recursively price themselves. -/
structure Tariff where
  unitFee : Lane -> Nat
  leaseEpochs : Nat

def Tariff.billable (tariff : Tariff) (charge : Charge) : Nat :=
  charge .incidences * tariff.unitFee .incidences +
  charge .turnBytes * tariff.unitFee .turnBytes +
  charge .memoryTouches * tariff.unitFee .memoryTouches +
  charge .witnessBytes * tariff.unitFee .witnessBytes +
  charge .proofWork * tariff.unitFee .proofWork +
  charge .storageBytes * tariff.unitFee .storageBytes +
  charge .networkBytes * tariff.unitFee .networkBytes +
  charge .sideEffectCount * tariff.unitFee .sideEffectCount

def Tariff.lease (tariff : Tariff) (charge : Charge) : Nat :=
  charge .storageBytes * tariff.leaseEpochs

variable {portal : Portal}
variable {materializer : Materializer DeclaredTurn.effectSchema Digest}
variable {Incidence : Type} [Fintype Incidence] [DecidableEq Incidence]

/-- The complete cost semantics for one flat declaration.  The upper vector is
available before execution.  The exact vector is derived from the actual
semantic post selected by `DeclaredHyperedge.execute`; it is never accepted as
a runtime receipt. -/
structure CostSemantics
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) where
  declarationBytes : Nat
  authorizationWitnessBytes : Incidence -> Nat
  tariff : Tariff
  upper : Charge
  exact : EffectDeclaration.Store -> Charge
  exact_le_upper : forall postStore, exact postStore <= upper
  incidences_exact : forall postStore,
    exact postStore .incidences = Fintype.card Incidence
  turnBytes_exact : forall postStore,
    exact postStore .turnBytes = declarationBytes
  memoryTouches_exact : forall postStore,
    exact postStore .memoryTouches = declaration.footprint.toFinset.card
  witnessBytes_exact : forall postStore,
    exact postStore .witnessBytes =
      Finset.univ.sum authorizationWitnessBytes
  feeDebit_exact : forall postStore,
    exact postStore .feeDebit = tariff.billable (exact postStore)
  lease_exact : forall postStore,
    exact postStore .leaseByteBlocks = tariff.lease (exact postStore)

def CostSemantics.quote
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    (semantics : CostSemantics projection declaration)
    (postStore : EffectDeclaration.Store) : Quote where
  upper := semantics.upper
  exact := semantics.exact postStore
  exact_le_upper := semantics.exact_le_upper postStore

/-- An admitted flat hyperedge and its canonical `PreparedTurn` carry the same
exact memory-touch charge. -/
def CostSemantics.boundedPrepared
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    (semantics : CostSemantics projection declaration)
    {postStore : EffectDeclaration.Store}
    (commit : CommittedHyperedge projection declaration postStore) :
    BoundedPreparedTurn commit.prepared where
  quote := semantics.quote postStore
  memoryTouches_exact := by
    change semantics.exact postStore .memoryTouches =
      declaration.footprint.toFinset.card + 0
    simpa using semantics.memoryTouches_exact postStore

theorem CostSemantics.prepared_incidence_exact
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    (semantics : CostSemantics projection declaration)
    {postStore : EffectDeclaration.Store}
    (commit : CommittedHyperedge projection declaration postStore) :
    (semantics.boundedPrepared commit).quote.exact .incidences =
      Fintype.card Incidence :=
  semantics.incidences_exact postStore

/-! ## Total cost-aware execution -/

/-- Cost-aware joint outcome.  Proof fields are erased by extraction; they
make funding or its failure part of the Lean acceptance object. -/
inductive Outcome
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    (semantics : CostSemantics projection declaration)
    (available : Charge) : Type _
  | committed (postStore : EffectDeclaration.Store)
      (funded : semantics.exact postStore <= available)
  | rejected (reason : DeclaredHyperedge.RejectReason)
  | overBudget (candidate : EffectDeclaration.Store)
      (insufficient : ¬ (semantics.exact candidate <= available))

/-- Pure metered execution.  A host can accelerate the calculations, but only
this definition determines which semantic constructor is accepted. -/
def executeMetered
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (semantics : CostSemantics projection declaration)
    (available : Charge) : Outcome semantics available :=
  match DeclaredHyperedge.execute projection declaration with
  | .rejected reason => .rejected reason
  | .committed postStore =>
      if checked : Charge.fundedCheck (semantics.exact postStore) available = true then
        .committed postStore
          ((Charge.fundedCheck_eq_true_iff
            (semantics.exact postStore) available).mp checked)
      else
        .overBudget postStore (by
          intro funded
          exact checked ((Charge.fundedCheck_eq_true_iff
            (semantics.exact postStore) available).mpr funded))

/-- Logical materialization.  The over-budget candidate is proof data for why
funding failed, but it is not the visible post-state. -/
def Outcome.materialized
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {semantics : CostSemantics projection declaration}
    {available : Charge} : Outcome semantics available ->
      Materialized materializer
  | .committed postStore _ =>
      materialize materializer (declaration.logicalOfStore postStore)
  | .rejected _ => declaration.pre
  | .overBudget _ _ => declaration.pre

/-- Remaining budget is derived by exact pointwise subtraction only for the
funded constructor. -/
def Outcome.remaining
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {semantics : CostSemantics projection declaration}
    {available : Charge} : Outcome semantics available -> Charge
  | .committed postStore _ =>
      fun lane => available lane - semantics.exact postStore lane
  | .rejected _ => available
  | .overBudget _ _ => available

/-- Forget only the budget decision.  An over-budget candidate was accepted by
the underlying semantic executor even though it is not exposed as a post. -/
def Outcome.semanticOutcome
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {semantics : CostSemantics projection declaration}
    {available : Charge} : Outcome semantics available ->
      DeclaredHyperedge.Outcome declaration
  | .committed postStore _ => .committed postStore
  | .rejected reason => .rejected reason
  | .overBudget candidate _ => .committed candidate

theorem executeMetered_semanticOutcome
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (semantics : CostSemantics projection declaration)
    (available : Charge) :
    (executeMetered projection declaration semantics available).semanticOutcome =
      DeclaredHyperedge.execute projection declaration := by
  cases executedEq : DeclaredHyperedge.execute projection declaration with
  | committed postStore =>
      simp only [executeMetered, executedEq]
      split <;> rfl
  | rejected reason =>
      simp only [executeMetered, executedEq]
      rfl

@[simp] theorem Outcome.rejected_atomic
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {semantics : CostSemantics projection declaration}
    {available : Charge} (reason : DeclaredHyperedge.RejectReason) :
    (Outcome.rejected (semantics := semantics) (available := available)
      reason).materialized = declaration.pre /\
    (Outcome.rejected (semantics := semantics) (available := available)
      reason).remaining = available :=
  ⟨rfl, rfl⟩

@[simp] theorem Outcome.overBudget_atomic
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {semantics : CostSemantics projection declaration}
    {available : Charge} (candidate : EffectDeclaration.Store)
    (insufficient : ¬ (semantics.exact candidate <= available)) :
    (Outcome.overBudget (semantics := semantics) (available := available)
      candidate insufficient).materialized = declaration.pre /\
    (Outcome.overBudget (semantics := semantics) (available := available)
      candidate insufficient).remaining = available :=
  ⟨rfl, rfl⟩

/-- A committed cost outcome debits exactly the semantic charge in every lane. -/
theorem Outcome.committed_exact_delta
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {semantics : CostSemantics projection declaration}
    {available : Charge} (postStore : EffectDeclaration.Store)
    (funded : semantics.exact postStore <= available) :
    semantics.exact postStore +
      (Outcome.committed (semantics := semantics) (available := available)
        postStore funded).remaining = available := by
  funext lane
  change semantics.exact postStore lane +
    (available lane - semantics.exact postStore lane) = available lane
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel (funded lane)

/-- Metered commitment cannot bypass joint-turn semantics: it implies the
existing exact hyperedge certification for the same post. -/
theorem executeMetered_committed_sound
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (semantics : CostSemantics projection declaration)
    (available : Charge) (postStore : EffectDeclaration.Store)
    (funded : semantics.exact postStore <= available)
    (committed : executeMetered projection declaration semantics available =
      .committed postStore funded) :
    Nonempty (CommittedHyperedge projection declaration postStore) := by
  have semantic := congrArg Outcome.semanticOutcome committed
  rw [executeMetered_semanticOutcome] at semantic
  change DeclaredHyperedge.execute projection declaration =
    .committed postStore at semantic
  exact execute_committed_hyperedge_sound projection declaration postStore semantic

/-- If the underlying semantics rejects, metering is exactly atomic regardless
of all fee, lease, proof, network, and side-effect coordinates. -/
theorem executeMetered_rejected_atomic
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (semantics : CostSemantics projection declaration)
    (available : Charge) (reason : DeclaredHyperedge.RejectReason)
    (rejected : DeclaredHyperedge.execute projection declaration =
      .rejected reason) :
    (executeMetered projection declaration semantics available).materialized =
        declaration.pre /\
    (executeMetered projection declaration semantics available).remaining =
        available := by
  simp [executeMetered, rejected]

end Minidregg.Kernel.DeclaredHyperedgeCost

/-- info: 'Minidregg.Kernel.DeclaredHyperedgeCost.CostSemantics.boundedPrepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredHyperedgeCost.CostSemantics.boundedPrepared
/-- info: 'Minidregg.Kernel.DeclaredHyperedgeCost.Outcome.committed_exact_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredHyperedgeCost.Outcome.committed_exact_delta
/-- info: 'Minidregg.Kernel.DeclaredHyperedgeCost.executeMetered_committed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredHyperedgeCost.executeMetered_committed_sound
