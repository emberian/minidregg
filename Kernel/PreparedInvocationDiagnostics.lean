/- Request-local diagnostic witnesses. Every row remains indexed by the
prepared invocation, tuple and incidence that produced it. No row is read
from a client, stored between requests, or reused for submission. -/
import Kernel.DeclaredResourceController

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel.MultiCellHyperedge
set_option autoImplicit false

variable {F : Type} [Field F]
variable {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
variable {ambient : Ambient} {durable : Durable} {command : Command}

/-- One resolved law and canonical witness, bound to the exact current step. -/
structure PreparedPolicyLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) where
  private mk ::
  committed : CommittedPolicy
  witness : CompiledPolicyWitness F
  resolved : (policyConfig prepared tuple incidence).registry.resolve
    (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision = some committed
  exact : witness = canonicalWitness profile.compilerProfile.compiler committed
    (step prepared tuple incidence).oldState (step prepared tuple incidence).newState

def preparePolicyLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    Option (PreparedPolicyLeg prepared tuple incidence) :=
  let wanted := (tuple.request incidence).2
  let context := step prepared tuple incidence
  match resolved : (policyConfigFromStep prepared context).registry.resolve wanted.policyId wanted.policyRevision with
  | none => none
  | some committed => some ⟨committed, canonicalWitness profile.compilerProfile.compiler committed
      context.oldState context.newState, resolved, rfl⟩

def PreparedPolicyLeg.range [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command}
    (leg : PreparedPolicyLeg prepared tuple incidence) : Option LawLeaf :=
  LawLeaf.ofRange profile.compilerProfile.compiler leg.committed.record.predicate
    leg.witness.oldState leg.witness.newState

def PreparedPolicyLeg.cast [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command}
    (leg : PreparedPolicyLeg prepared tuple incidence) : Option (Int × Int) :=
  castAlias F (intsOf leg.committed.record.predicate leg.witness.oldState leg.witness.newState)

def PreparedPolicyLeg.law [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command}
    (leg : PreparedPolicyLeg prepared tuple incidence) : Option LawLeaf :=
  LawLeaf.of leg.committed.record.predicate leg.witness.oldState leg.witness.newState

theorem preparePolicyLeg_range [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    ((preparePolicyLeg prepared tuple incidence).bind (·.range)) = rangeLeaf prepared tuple incidence := by
  unfold preparePolicyLeg rangeLeaf
  dsimp only
  simp only [policyConfigFromStep_exact]
  split <;> simp_all [PreparedPolicyLeg.range, canonicalWitness]

theorem preparePolicyLeg_cast [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    ((preparePolicyLeg prepared tuple incidence).bind (·.cast)) = castAliasLeg prepared tuple incidence := by
  unfold preparePolicyLeg castAliasLeg
  dsimp only
  simp only [policyConfigFromStep_exact]
  split <;> simp_all [PreparedPolicyLeg.cast, canonicalWitness]

theorem preparePolicyLeg_law [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    ((preparePolicyLeg prepared tuple incidence).bind (·.law)) = lawLeaf prepared tuple incidence := by
  unfold preparePolicyLeg lawLeaf
  dsimp only
  simp only [policyConfigFromStep_exact]
  split <;> simp_all [PreparedPolicyLeg.law, canonicalWitness]

abbrev PolicyLegs [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) :=
  List (Σ incidence : Incidence command, Option (PreparedPolicyLeg prepared tuple incidence))

def preparePolicyLegs [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) : PolicyLegs prepared tuple :=
  ((List.finRange command.targets.length).map some ++ [none]).map fun incidence =>
    ⟨incidence, preparePolicyLeg prepared tuple incidence⟩

def PolicyLegs.firstRange [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} (legs : PolicyLegs prepared tuple) : Option LawLeaf :=
  legs.findSome? fun leg => leg.2.bind (·.range)

def PolicyLegs.firstCast [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} (legs : PolicyLegs prepared tuple) : Option (Int × Int) :=
  legs.findSome? fun leg => leg.2.bind (·.cast)

def PolicyLegs.firstLaw [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} (legs : PolicyLegs prepared tuple) : Option LawLeaf :=
  legs.findSome? fun leg => leg.2.bind (·.law)

private theorem findSome_map {α β γ : Type} (f : α → β) (g : β → Option γ) (xs : List α) :
    (xs.map f).findSome? g = xs.findSome? (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.findSome?_cons]
    rw [ih]

theorem preparePolicyLegs_range [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) :
    (preparePolicyLegs prepared tuple).firstRange = firstRangeLeaf prepared tuple := by
  simp only [preparePolicyLegs, PolicyLegs.firstRange, findSome_map, preparePolicyLeg_range,
    firstRangeLeaf]

theorem preparePolicyLegs_cast [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) :
    (preparePolicyLegs prepared tuple).firstCast = firstCastAlias prepared tuple := by
  simp only [preparePolicyLegs, PolicyLegs.firstCast, findSome_map, preparePolicyLeg_cast,
    firstCastAlias]

theorem preparePolicyLegs_law [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) :
    (preparePolicyLegs prepared tuple).firstLaw = firstLawLeaf prepared tuple := by
  simp only [preparePolicyLegs, PolicyLegs.firstLaw, findSome_map, preparePolicyLeg_law,
    firstLawLeaf]
/-- Disclosure formatting is supplied by the receiving route for each exact
incidence. It cannot change the underlying range/cast decision or order. -/
def PolicyLegs.firstRangeWith {α : Type} [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} (legs : PolicyLegs prepared tuple)
    (render : Incidence command → LawLeaf → α) : Option α :=
  legs.findSome? fun leg => (leg.2.bind (·.range)).map (render leg.1)

def PolicyLegs.firstCastWith {α : Type} [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} (legs : PolicyLegs prepared tuple)
    (render : Incidence command → Int → Int → α) : Option α :=
  legs.findSome? fun leg => (leg.2.bind (·.cast)).map fun (x, y) => render leg.1 x y

/-- A narrowed law explanation needs its committed predicate and the same
witness states, rather than an already-disclosed raw failing leaf. -/
def PreparedPolicyLeg.lawWith {α : Type} [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command}
    (leg : PreparedPolicyLeg prepared tuple incidence)
    (render : CommittedPolicy → Minidregg.Pred.State → Minidregg.Pred.State → α) : Option α :=
  if Minidregg.Pred.eval leg.committed.record.predicate leg.witness.oldState leg.witness.newState
  then none else some (render leg.committed leg.witness.oldState leg.witness.newState)

def PolicyLegs.firstLawWith {α : Type} [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} (legs : PolicyLegs prepared tuple)
    (render : Incidence command → CommittedPolicy → Minidregg.Pred.State → Minidregg.Pred.State → α) : Option α :=
  legs.findSome? fun leg => leg.2.bind fun ready => ready.lawWith (render leg.1)

theorem preparePolicyLegs_rangeWith {α : Type} [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (render : Incidence command → LawLeaf → α) :
    (preparePolicyLegs prepared tuple).firstRangeWith render =
      ((List.finRange command.targets.length).map some ++ [none]).findSome?
        (fun i => (rangeLeaf prepared tuple i).map (render i)) := by
  simp only [preparePolicyLegs, PolicyLegs.firstRangeWith, findSome_map, preparePolicyLeg_range]

theorem preparePolicyLegs_castWith {α : Type} [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (render : Incidence command → Int → Int → α) :
    (preparePolicyLegs prepared tuple).firstCastWith render =
      ((List.finRange command.targets.length).map some ++ [none]).findSome?
        (fun i => (castAliasLeg prepared tuple i).map fun (x, y) => render i x y) := by
  simp only [preparePolicyLegs, PolicyLegs.firstCastWith, findSome_map, preparePolicyLeg_cast]

theorem preparePolicyLeg_lawWith {α : Type} [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command)
    (render : CommittedPolicy → Minidregg.Pred.State → Minidregg.Pred.State → α) :
    ((preparePolicyLeg prepared tuple incidence).bind (fun leg => leg.lawWith render)) =
      (do
        let wanted := (tuple.request incidence).2
        let context := step prepared tuple incidence
        let committed ← (policyConfig prepared tuple incidence).registry.resolve wanted.policyId wanted.policyRevision
        let witness := canonicalWitness (F := F) profile.compilerProfile.compiler committed
          context.oldState context.newState
        if Minidregg.Pred.eval committed.record.predicate witness.oldState witness.newState
        then none else some (render committed witness.oldState witness.newState)) := by
  unfold preparePolicyLeg
  dsimp only
  simp only [policyConfigFromStep_exact]
  split <;> simp_all [PreparedPolicyLeg.lawWith, canonicalWitness]

theorem preparePolicyLegs_lawWith {α : Type} [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared))
    (render : Incidence command → CommittedPolicy → Minidregg.Pred.State → Minidregg.Pred.State → α) :
    (preparePolicyLegs prepared tuple).firstLawWith render =
      ((List.finRange command.targets.length).map some ++ [none]).findSome? (fun i => do
        let wanted := (tuple.request i).2
        let context := step prepared tuple i
        let committed ← (policyConfig prepared tuple i).registry.resolve wanted.policyId wanted.policyRevision
        let witness := canonicalWitness (F := F) profile.compilerProfile.compiler committed
          context.oldState context.newState
        if Minidregg.Pred.eval committed.record.predicate witness.oldState witness.newState
        then none else some (render i committed witness.oldState witness.newState)) := by
  simp only [preparePolicyLegs, PolicyLegs.firstLawWith, findSome_map, preparePolicyLeg_lawWith]

#assert_axioms preparePolicyLegs_rangeWith
#assert_axioms preparePolicyLegs_castWith
#assert_axioms preparePolicyLegs_lawWith
#assert_axioms preparePolicyLegs_range
#assert_axioms preparePolicyLegs_cast
#assert_axioms preparePolicyLegs_law
end Minidregg.Kernel.DeclaredResourceController
