/- Request-local composed-law diagnostics. The retained step, law and witness
are bound to one prepared invocation/tuple/incidence. Public explanations are
always delegated to ComposedLawDiagnostics; effective ancestor leaves never
cross this boundary. Submission constructs its own current prepared image. -/
import Kernel.DeclaredResourceController

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

-- Config is an index here. Do not normalize the complete directory/portal
-- construction while elaborating the finite row's dependent projections.
attribute [local irreducible] policyConfigFromStep CanonicalRuntimeProfile.Profile.compilerProfile

variable {F : Type} [Field F]
variable {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
variable {ambient : Ambient} {ground : Ground deployment} {command : Command}

/-- Retain the finite step, not the universe-lifted portal config. Rebuilding
its config from this step neither reprojects the source nor resolves the law;
the resolved closure and all other retained values are exact derivatives. -/
structure PreparedPolicyLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) where
  private mk ::
  context : PolicyStepContext
  contextExact : context = step prepared tuple incidence
  law : ComposedPolicyAdmission.PreparedLaw (F := F)
    (policyConfigFromStep prepared incidence context)
  resolved : (policyConfigFromStep prepared incidence context).resolve? = some law
  predicate : Minidregg.Pred.Pred
  predicateExact : predicate = law.predicate
  witness : ComposedPolicyAdmission.Witness F
  witnessExact : witness = law.witness

def preparePolicyLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    Option (PreparedPolicyLeg prepared tuple incidence) :=
  let context := step prepared tuple incidence
  let config := policyConfigFromStep prepared incidence context
  match resolved : config.resolve? with
  | none => none
  | some law => some ⟨context, rfl, law, resolved, law.predicate, rfl, law.witness, rfl⟩

def PreparedPolicyLeg.range [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command}
    (leg : PreparedPolicyLeg prepared tuple incidence) : Option LawLeaf :=
  LawLeaf.ofRange profile.compilerProfile.compiler leg.predicate
    leg.witness.compiled.oldState leg.witness.compiled.newState

def PreparedPolicyLeg.cast [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command}
    (leg : PreparedPolicyLeg prepared tuple incidence) : Option (Int × Int) :=
  castAlias F (intsOf leg.predicate leg.witness.compiled.oldState leg.witness.compiled.newState)

def PreparedPolicyLeg.lawLeaf [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command}
    (leg : PreparedPolicyLeg prepared tuple incidence) : Option LawLeaf :=
  LawLeaf.of leg.predicate leg.witness.compiled.oldState leg.witness.compiled.newState

/-- The full closure decides whether a failure exists. Its detail is discarded;
only the target-local explanation under this exact incidence's grant is public. -/
def PreparedPolicyLeg.rangeRefusal [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command}
    (leg : PreparedPolicyLeg prepared tuple incidence) (fields : Option (Finset CellField)) : Option Refusal :=
  leg.range.map fun _ => ComposedLawDiagnostics.publicRefusal fields leg.law

def PreparedPolicyLeg.castRefusal [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command}
    (leg : PreparedPolicyLeg prepared tuple incidence) (fields : Option (Finset CellField)) : Option Refusal :=
  leg.cast.map fun _ => ComposedLawDiagnostics.publicRefusal fields leg.law

def PreparedPolicyLeg.lawRefusal [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command}
    (leg : PreparedPolicyLeg prepared tuple incidence) (fields : Option (Finset CellField)) : Option Refusal :=
  if Minidregg.Pred.eval leg.predicate leg.witness.compiled.oldState leg.witness.compiled.newState
  then none else some (ComposedLawDiagnostics.publicRefusal fields leg.law)

private theorem config_step [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    (policyConfig prepared tuple incidence).step = step prepared tuple incidence := by
  unfold policyConfig policyConfigFromStep PhysicalLawResolution.targetConfig
    PhysicalLawResolution.config
  rfl

theorem preparePolicyLeg_range [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    ((preparePolicyLeg prepared tuple incidence).bind (·.range)) = rangeLeaf prepared tuple incidence := by
  unfold preparePolicyLeg rangeLeaf
  dsimp only
  simp only [policyConfigFromStep_exact]
  split <;> simp_all [PreparedPolicyLeg.range, ComposedPolicyAdmission.PreparedLaw.witness,
    ResolvedLawCompilation.witness, config_step]

theorem preparePolicyLeg_cast [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    ((preparePolicyLeg prepared tuple incidence).bind (·.cast)) = castAliasLeg prepared tuple incidence := by
  unfold preparePolicyLeg castAliasLeg
  dsimp only
  simp only [policyConfigFromStep_exact]
  split <;> simp_all [PreparedPolicyLeg.cast, ComposedPolicyAdmission.PreparedLaw.witness,
    ResolvedLawCompilation.witness, config_step]

theorem preparePolicyLeg_law [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    ((preparePolicyLeg prepared tuple incidence).bind (·.lawLeaf)) = lawLeaf prepared tuple incidence := by
  unfold preparePolicyLeg lawLeaf
  dsimp only
  simp only [policyConfigFromStep_exact]
  split <;> simp_all [PreparedPolicyLeg.lawLeaf, ComposedPolicyAdmission.PreparedLaw.witness,
    ResolvedLawCompilation.witness, config_step]

abbrev PolicyLegs [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) :=
  List (Σ incidence : Incidence command, Option (PreparedPolicyLeg prepared tuple incidence))

def preparePolicyLegs [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) : PolicyLegs prepared tuple :=
  (ordinaryIncidences command).map fun incidence =>
    ⟨incidence, preparePolicyLeg prepared tuple incidence⟩

def PolicyLegs.firstRangeRefusal [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {tuple : PreparedTuple (plan prepared)} (legs : PolicyLegs prepared tuple)
    (fieldsOf : Incidence command → Option (Finset CellField)) : Option Refusal :=
  legs.findSome? fun leg => leg.2.bind fun ready => ready.rangeRefusal (fieldsOf leg.1)

def PolicyLegs.firstCastRefusal [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {tuple : PreparedTuple (plan prepared)} (legs : PolicyLegs prepared tuple)
    (fieldsOf : Incidence command → Option (Finset CellField)) : Option Refusal :=
  legs.findSome? fun leg => leg.2.bind fun ready => ready.castRefusal (fieldsOf leg.1)

def PolicyLegs.firstLawRefusal [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {tuple : PreparedTuple (plan prepared)} (legs : PolicyLegs prepared tuple)
    (fieldsOf : Incidence command → Option (Finset CellField)) : Option Refusal :=
  legs.findSome? fun leg => leg.2.bind fun ready => ready.lawRefusal (fieldsOf leg.1)

private theorem findSome_map {α β γ : Type} (f : α → β) (g : β → Option γ) (xs : List α) :
    (xs.map f).findSome? g = xs.findSome? (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.findSome?_cons]; rw [ih]

theorem preparePolicyLeg_rangeRefusal [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (i : Incidence command) (fields : Option (Finset CellField)) :
    ((preparePolicyLeg prepared tuple i).bind (fun leg => leg.rangeRefusal fields)) =
      (do let _ ← rangeLeaf prepared tuple i
          let law ← (policyConfig prepared tuple i).resolve?
          pure (ComposedLawDiagnostics.publicRefusal fields law)) := by
  unfold preparePolicyLeg rangeLeaf
  dsimp only
  simp only [policyConfigFromStep_exact]
  split <;> simp_all [PreparedPolicyLeg.rangeRefusal, PreparedPolicyLeg.range,
    ComposedPolicyAdmission.PreparedLaw.witness, ResolvedLawCompilation.witness,
    config_step, Option.map_eq_bind]
  all_goals rfl

theorem preparePolicyLeg_castRefusal [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (i : Incidence command) (fields : Option (Finset CellField)) :
    ((preparePolicyLeg prepared tuple i).bind (fun leg => leg.castRefusal fields)) =
      (do let _ ← castAliasLeg prepared tuple i
          let law ← (policyConfig prepared tuple i).resolve?
          pure (ComposedLawDiagnostics.publicRefusal fields law)) := by
  unfold preparePolicyLeg castAliasLeg
  dsimp only
  simp only [policyConfigFromStep_exact]
  split <;> simp_all [PreparedPolicyLeg.castRefusal, PreparedPolicyLeg.cast,
    ComposedPolicyAdmission.PreparedLaw.witness, ResolvedLawCompilation.witness,
    config_step, Option.map_eq_bind]
  all_goals rfl

theorem preparePolicyLeg_lawRefusal [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (i : Incidence command)
    (fieldsOf : Incidence command → Option (Finset CellField)) :
    ((preparePolicyLeg prepared tuple i).bind (fun leg => leg.lawRefusal (fieldsOf i))) =
      lawRefusal fieldsOf prepared tuple i := by
  unfold preparePolicyLeg lawRefusal
  dsimp only
  simp only [policyConfigFromStep_exact]
  split <;> simp_all [PreparedPolicyLeg.lawRefusal,
    ComposedPolicyAdmission.PreparedLaw.witness, ResolvedLawCompilation.witness, config_step]
  all_goals rfl

theorem preparePolicyLegs_rangeRefusal [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (fieldsOf : Incidence command → Option (Finset CellField)) :
    (preparePolicyLegs prepared tuple).firstRangeRefusal fieldsOf = firstRangeRefusal fieldsOf prepared tuple := by
  simp only [preparePolicyLegs, PolicyLegs.firstRangeRefusal, findSome_map,
    preparePolicyLeg_rangeRefusal, firstRangeRefusal]

theorem preparePolicyLegs_castRefusal [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (fieldsOf : Incidence command → Option (Finset CellField)) :
    (preparePolicyLegs prepared tuple).firstCastRefusal fieldsOf = firstCastRefusal fieldsOf prepared tuple := by
  simp only [preparePolicyLegs, PolicyLegs.firstCastRefusal, findSome_map,
    preparePolicyLeg_castRefusal, firstCastRefusal]

theorem preparePolicyLegs_lawRefusal [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (fieldsOf : Incidence command → Option (Finset CellField)) :
    (preparePolicyLegs prepared tuple).firstLawRefusal fieldsOf = firstLawRefusal fieldsOf prepared tuple := by
  simp only [preparePolicyLegs, PolicyLegs.firstLawRefusal, findSome_map,
    preparePolicyLeg_lawRefusal, firstLawRefusal]

#assert_axioms preparePolicyLeg_range
#assert_axioms preparePolicyLeg_cast
#assert_axioms preparePolicyLeg_law
#assert_axioms preparePolicyLegs_rangeRefusal
#assert_axioms preparePolicyLegs_castRefusal
#assert_axioms preparePolicyLegs_lawRefusal
end Minidregg.Kernel.DeclaredResourceController
