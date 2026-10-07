/- Source/graph correspondence for the new partial lazy edition. All running
and finished raw transitions preserve the concrete graph relation. Every
normally finished closed computation, through rawRun or runBounded at any
limits, has an independent source evaluation to the same ground observation.
This module does not yet inhabit Representation: administrative progress and
source-to-machine completeness remain separate substantive obligations. -/
import Theory.ObjectiveBendDemandInvariant
import Theory.AxiomPin
import Theory.ObjectiveBendStepCases
namespace Minidregg.Theory.ObjectiveBendDemandAdequacy
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandInvariant
set_option autoImplicit false

 theorem sourceSteps_trans {a b c : Term} (first : Steps a b) (second : Steps b c) : Steps a c := by
  induction first with
  | refl => exact second
  | next step _ ih => exact .next step (ih second)

 theorem source_value_noStep {term next : Term} (value : Value term) (step : Step term next) : False := by
  cases value <;> cases step

set_option maxHeartbeats 600000 in
/-- The independent reference semantics is deterministic for every partial
constructor. This includes fixed-point unfolding and field shadowing. -/
 theorem sourceStep_deterministic {term first second : Term}
    (left : Step term first) (right : Step term second) : first = second := by
  induction left generalizing second <;> cases right
  all_goals first
    | exact False.elim (source_value_noStep (Value.function _) (by assumption))
    | exact False.elim (source_value_noStep (Value.natural _) (by assumption))
    | exact False.elim (source_value_noStep (Value.record _) (by assumption))
    | exact False.elim (source_value_noStep (Value.specification _ _) (by assumption))
    | exact False.elim (source_value_noStep (Value.prototype _ _) (by assumption))
    | exact False.elim (source_value_noStep (Value.inject _ _) (by assumption))
    | exact False.elim (source_value_noStep (Value.boolean _) (by assumption))
    | grind [source_value_noStep]

 theorem source_value_steps_identity {term next : Term} (value : Value term) (steps : Steps term next) : term = next := by
  cases steps with
  | refl => rfl
  | next step _ => exact False.elim (source_value_noStep value step)

 theorem source_evaluates_unique {source first second : Term}
    (left : Evaluates source first) (right : Evaluates source second) : first = second := by
  obtain ⟨steps,value⟩ := left
  obtain ⟨otherSteps,otherValue⟩ := right
  induction steps generalizing second with
  | refl => exact source_value_steps_identity value otherSteps
  | next step rest ih =>
      cases otherSteps with
      | refl => exact False.elim (source_value_noStep otherValue step)
      | next otherStep otherRest =>
          have aligned := sourceStep_deterministic step otherStep
          cases aligned
          exact ih value otherRest otherValue

/-- A genuine source reduction cannot discard a terminating derivation.
Determinism aligns its first reduction with the independent evaluation trace. -/
 theorem sourceStep_evaluates_tail {source next value : Term}
    (step : Step source next) (evaluates : Evaluates source value) : Evaluates next value := by
  obtain ⟨steps,isValue⟩ := evaluates
  cases steps with
  | refl => exact False.elim (source_value_noStep isValue step)
  | next first rest =>
      have aligned := sourceStep_deterministic step first
      cases aligned
      exact ⟨rest,isValue⟩

 theorem sourceSteps_evaluates_tail {source next value : Term}
    (steps : Steps source next) (evaluates : Evaluates source value) : Evaluates next value := by
  induction steps with
  | refl => exact evaluates
  | next first rest ih => exact ih (sourceStep_evaluates_tail first evaluates)

/-- A finite independent CBN evaluation derivation. Cost counts demand
constructors, including values; it is a proof measure for partial programs,
not a total evaluator or a promise that Fix terminates. -/
inductive SourceDerivation : Term → Term → Nat → Prop where
  | value {term : Term} : Value term → SourceDerivation term term 1
  | applicationLambda {function body argument result : Term} {functionCost bodyCost : Nat} :
      SourceDerivation function (.lam body) functionCost →
      SourceDerivation (instantiate body argument) result bodyCost →
      SourceDerivation (.app function argument) result (functionCost+bodyCost+1)
  | applicationSpecification {function descriptor extension argument result : Term} {functionCost bodyCost : Nat} :
      SourceDerivation function (.specification descriptor extension) functionCost →
      SourceDerivation (.app extension argument) result bodyCost →
      SourceDerivation (.app function argument) result (functionCost+bodyCost+1)
  | mix {lower upper result : Term} {cost : Nat} :
      SourceDerivation (mixBody lower upper) result cost → SourceDerivation (.mix lower upper) result (cost+1)
  | fix {spec inherited result : Term} {cost : Nat} :
      SourceDerivation (.app (.app spec (.fix spec inherited)) inherited) result cost →
      SourceDerivation (.fix spec inherited) result (cost+1)
  | reflect {target spec inherited result : Term} {targetCost resultCost : Nat} :
      SourceDerivation target (.prototype spec inherited) targetCost →
      SourceDerivation spec result resultCost → SourceDerivation (.reflect target) result (targetCost+resultCost+1)
  | metadata {target descriptor extension result : Term} {targetCost resultCost : Nat} :
      SourceDerivation target (.specification descriptor extension) targetCost →
      SourceDerivation descriptor result resultCost → SourceDerivation (.metadata target) result (targetCost+resultCost+1)
  | project {target spec inherited result : Term} {targetCost resultCost : Nat} :
      SourceDerivation target (.prototype spec inherited) targetCost →
      SourceDerivation inherited result resultCost → SourceDerivation (.project target) result (targetCost+resultCost+1)
  | field {target body result : Term} {fields : List (String × Term)} {name : String} {targetCost resultCost : Nat} :
      SourceDerivation target (.record fields) targetCost →
      fields.find? (fun field => field.1 == name) = some (name,body) →
      SourceDerivation body result resultCost → SourceDerivation (.get target name) result (targetCost+resultCost+1)
  | extend {target : Term} {inherited fields : List (String × Term)} {targetCost : Nat} :
      SourceDerivation target (.record inherited) targetCost →
      SourceDerivation (.extend target fields) (.record (extendFields inherited fields)) (targetCost+1)
  | binary {primitive : Primitive} {left right leftValue rightValue result : Term} {leftCost rightCost : Nat} :
      SourceDerivation left leftValue leftCost → SourceDerivation right rightValue rightCost →
      primitiveResult primitive leftValue rightValue = some result →
      SourceDerivation (.binary primitive left right) result (leftCost+rightCost+1)
  | zero {condition zero body result : Term} {conditionCost resultCost : Nat} :
      SourceDerivation condition (.nat 0) conditionCost → SourceDerivation zero result resultCost →
      SourceDerivation (.ifZero condition zero body) result (conditionCost+resultCost+1)
  | successor {condition zero body result : Term} {number conditionCost resultCost : Nat} :
      SourceDerivation condition (.nat (number+1)) conditionCost →
      SourceDerivation (instantiate body (.nat number)) result resultCost →
      SourceDerivation (.ifZero condition zero body) result (conditionCost+resultCost+1)
  | case {scrutinee payload body result : Term} {arms : List (String × Term)} {tag : String}
      {scrutineeCost resultCost : Nat} :
      SourceDerivation scrutinee (.inject tag payload) scrutineeCost →
      arms.find? (fun arm => arm.1 == tag) = some (tag,body) →
      SourceDerivation (instantiate body payload) result resultCost →
      SourceDerivation (.case scrutinee arms) result (scrutineeCost+resultCost+1)
  | ifTrue {condition whenTrue whenFalse result : Term} {conditionCost resultCost : Nat} :
      SourceDerivation condition (.boolean true) conditionCost → SourceDerivation whenTrue result resultCost →
      SourceDerivation (.ifBool condition whenTrue whenFalse) result (conditionCost+resultCost+1)
  | ifFalse {condition whenTrue whenFalse result : Term} {conditionCost resultCost : Nat} :
      SourceDerivation condition (.boolean false) conditionCost → SourceDerivation whenFalse result resultCost →
      SourceDerivation (.ifBool condition whenTrue whenFalse) result (conditionCost+resultCost+1)
  | done {value result : Term} {cost : Nat} :
      SourceDerivation value result cost → SourceDerivation (.done value) result (cost+1)

 theorem sourceSteps_lift (context : Term → Term)
    (compatible : ∀ {first second}, Step first second → Step (context first) (context second))
    {first second : Term} (steps : Steps first second) : Steps (context first) (context second) := by
  induction steps with
  | refl => exact .refl _
  | next first rest ih => exact .next (compatible first) ih

 theorem primitiveResult_value {primitive : Primitive} {left right result : Term}
    (found : primitiveResult primitive left right = some result) : Value result := by
  cases primitive <;> cases left <;> cases right <;> simp [primitiveResult] at found
  all_goals subst result; first | exact .natural _ | exact .boolean _

/-- Every cost derivation is a genuine evaluation in the independent source
small-step semantics. The value/thunk rules do not force latent fields. -/
 theorem sourceDerivation_evaluates {source result : Term} {cost : Nat}
    (derivation : SourceDerivation source result cost) : Evaluates source result := by
  induction derivation with
  | value value => exact ⟨.refl _,value⟩
  | applicationLambda first second ihf ihb =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun f => .app f _) (fun step => Step.application _ step) ihf.1)
        (.next (Step.beta _ _) ihb.1),ihb.2⟩
  | applicationSpecification first second ihf ihb =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun f => .app f _) (fun step => Step.application _ step) ihf.1)
        (.next (Step.applySpecification _ _ _) ihb.1),ihb.2⟩
  | mix first ih => exact ⟨.next (Step.mix _ _) ih.1,ih.2⟩
  | fix first ih => exact ⟨.next (Step.fix _ _) ih.1,ih.2⟩
  | reflect first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift Term.reflect Step.reflectStep iht.1)
        (.next (Step.reflectPrototype _ _) ihr.1),ihr.2⟩
  | metadata first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift Term.metadata Step.metadataStep iht.1)
        (.next (Step.metadataSpecification _ _) ihr.1),ihr.2⟩
  | project first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift Term.project Step.projectStep iht.1)
        (.next (Step.projectPrototype _ _) ihr.1),ihr.2⟩
  | field first found second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun t => .get t _) (fun step => Step.target _ step) iht.1)
        (.next (Step.field _ _ _ found) ihr.1),ihr.2⟩
  | extend first iht =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun t => .extend t _) (fun step => Step.extendTarget _ step) iht.1)
        (.next (Step.extendRecord _ _) (.refl _)),Value.record _⟩
  | binary first second found ihl ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun l => .binary _ l _) (fun step => Step.binaryLeft _ _ step) ihl.1)
        (sourceSteps_trans (sourceSteps_lift (fun r => .binary _ _ r) (fun step => Step.binaryRight _ _ ihl.2 step) ihr.1)
          (.next (Step.primitive _ _ _ _ ihl.2 ihr.2 found) (.refl _))),primitiveResult_value found⟩
  | zero first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun c => .ifZero c _ _) (fun step => Step.condition _ _ step) iht.1)
        (.next (Step.zero _ _) ihr.1),ihr.2⟩
  | successor first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun c => .ifZero c _ _) (fun step => Step.condition _ _ step) iht.1)
        (.next (Step.successor _ _ _) ihr.1),ihr.2⟩
  | case first found second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun t => .case t _) (fun step => Step.caseTarget _ step) iht.1)
        (.next (Step.caseInject _ _ _ _ found) ihr.1),ihr.2⟩
  | ifTrue first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun c => .ifBool c _ _) (fun step => Step.ifCondition _ _ step) iht.1)
        (.next (Step.ifTrue _ _) ihr.1),ihr.2⟩
  | ifFalse first second iht ihr =>
      exact ⟨sourceSteps_trans (sourceSteps_lift (fun c => .ifBool c _ _) (fun step => Step.ifCondition _ _ step) iht.1)
        (.next (Step.ifFalse _ _) ihr.1),ihr.2⟩
  | done first ih => exact ⟨.next (Step.done _) ih.1,ih.2⟩

 theorem sourceDerivation_cost_positive {source result : Term} {cost : Nat}
    (derivation : SourceDerivation source result cost) : 0 < cost := by
  cases derivation <;> omega

 theorem sourceDerivation_value_inv {source result : Term} {cost : Nat}
    (value : Value source) (derivation : SourceDerivation source result cost) : result = source ∧ cost = 1 := by
  cases derivation <;> cases value <;> exact ⟨rfl,rfl⟩

/-- Pulling a cost derivation backwards through one real source reduction
strictly increases demand cost. Context reductions retain the latent terms. -/
 theorem sourceStep_derivation_prepend {source next result : Term} {cost : Nat}
    (step : Step source next) (derivation : SourceDerivation next result cost) :
    ∃ larger, SourceDerivation source result larger ∧ cost < larger := by
  induction step generalizing result cost with
  | beta body argument =>
      exact ⟨_,.applicationLambda (.value (.function body)) derivation,by omega⟩
  | mix lower upper => exact ⟨_,.mix derivation,by omega⟩
  | fix spec inherited => exact ⟨_,.fix derivation,by omega⟩
  | applySpecification descriptor extension argument =>
      exact ⟨_,.applicationSpecification (.value (.specification descriptor extension)) derivation,by omega⟩
  | reflectPrototype spec inherited =>
      exact ⟨_,.reflect (.value (.prototype spec inherited)) derivation,by omega⟩
  | metadataSpecification descriptor extension =>
      exact ⟨_,.metadata (.value (.specification descriptor extension)) derivation,by omega⟩
  | projectPrototype spec inherited =>
      exact ⟨_,.project (.value (.prototype spec inherited)) derivation,by omega⟩
  | field fields name body found =>
      exact ⟨_,.field (.value (.record fields)) found derivation,by omega⟩
  | extendRecord inherited fields =>
      obtain ⟨rfl,rfl⟩ := sourceDerivation_value_inv (.record _) derivation
      exact ⟨_,.extend (.value (.record inherited)),by omega⟩
  | primitive primitive left right result lv rv found =>
      obtain ⟨rfl,rfl⟩ := sourceDerivation_value_inv (primitiveResult_value found) derivation
      exact ⟨_,.binary (.value lv) (.value rv) found,by omega⟩
  | zero zero body => exact ⟨_,.zero (.value (.natural 0)) derivation,by omega⟩
  | successor number zero body => exact ⟨_,.successor (.value (.natural _)) derivation,by omega⟩
  | caseInject tag payload arms body found =>
      exact ⟨_,.case (.value (.inject tag payload)) found derivation,by omega⟩
  | ifTrue whenTrue whenFalse => exact ⟨_,.ifTrue (.value (.boolean true)) derivation,by omega⟩
  | ifFalse whenTrue whenFalse => exact ⟨_,.ifFalse (.value (.boolean false)) derivation,by omega⟩
  | done value => exact ⟨_,.done derivation,by omega⟩
  | caseTarget arms step ih =>
      cases derivation with
      | value value => cases value
      | case first found second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.case first' found second,by omega⟩
  | ifCondition whenTrue whenFalse step ih =>
      cases derivation with
      | value value => cases value
      | ifTrue first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.ifTrue first' second,by omega⟩
      | ifFalse first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.ifFalse first' second,by omega⟩
  | application argument step ih =>
      cases derivation with
      | value value => cases value
      | applicationLambda first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.applicationLambda first' second,by omega⟩
      | applicationSpecification first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.applicationSpecification first' second,by omega⟩
  | reflectStep step ih =>
      cases derivation with
      | value value => cases value
      | reflect first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.reflect first' second,by omega⟩
  | metadataStep step ih =>
      cases derivation with
      | value value => cases value
      | metadata first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.metadata first' second,by omega⟩
  | projectStep step ih =>
      cases derivation with
      | value value => cases value
      | project first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.project first' second,by omega⟩
  | target name step ih =>
      cases derivation with
      | value value => cases value
      | field first found second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.field first' found second,by omega⟩
  | extendTarget fields step ih =>
      cases derivation with
      | value value => cases value
      | extend first =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.extend first',by omega⟩
  | binaryLeft primitive right step ih =>
      cases derivation with
      | value value => cases value
      | binary first second found =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.binary first' second found,by omega⟩
  | binaryRight primitive left value step ih =>
      cases derivation with
      | value value => cases value
      | binary first second found =>
          obtain ⟨larger,second',greater⟩ := ih second
          exact ⟨_,.binary first second' found,by omega⟩
  | condition zero body step ih =>
      cases derivation with
      | value value => cases value
      | zero first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.zero first' second,by omega⟩
      | successor first second =>
          obtain ⟨larger,first',greater⟩ := ih first
          exact ⟨_,.successor first' second,by omega⟩

/-- Cost derivations characterize the given independent source semantics;
their existence does not restrict the partial source domain. -/
 theorem source_evaluates_derivation {source result : Term} (evaluates : Evaluates source result) :
    ∃ cost, SourceDerivation source result cost := by
  obtain ⟨steps,value⟩ := evaluates
  induction steps with
  | refl => exact ⟨1,.value value⟩
  | next first rest ih =>
      obtain ⟨cost,derivation⟩ := ih value
      obtain ⟨larger,previous,_⟩ := sourceStep_derivation_prepend first derivation
      exact ⟨larger,previous⟩

 theorem source_evaluates_iff_derivation {source result : Term} :
    Evaluates source result ↔ ∃ cost, SourceDerivation source result cost := by
  exact ⟨source_evaluates_derivation,fun ⟨_,derivation⟩ => sourceDerivation_evaluates derivation⟩

 theorem sourceDerivation_result_unique {source first second : Term} {firstCost secondCost : Nat}
    (left : SourceDerivation source first firstCost) (right : SourceDerivation source second secondCost) :
    first = second :=
  source_evaluates_unique (sourceDerivation_evaluates left) (sourceDerivation_evaluates right)

set_option maxHeartbeats 600000 in
/-- Demand cost is determined by the partial source computation, even when
there are multiple proofs of its evaluation. -/
 theorem sourceDerivation_cost_unique {source first second : Term} {firstCost secondCost : Nat}
    (left : SourceDerivation source first firstCost) (right : SourceDerivation source second secondCost) :
    firstCost = secondCost := by
  induction left generalizing second secondCost <;> cases right
  all_goals try rfl
  all_goals try (cases ‹Value _›)
  all_goals grind [sourceDerivation_result_unique]

/-- Every real source reduction consumes a positive part of the unique finite
demand budget. This is the semantic component of the lazy graph progress rank. -/
 theorem sourceStep_derivation_tail {source next result : Term} {cost : Nat}
    (step : Step source next) (derivation : SourceDerivation source result cost) :
    ∃ smaller, SourceDerivation next result smaller ∧ smaller < cost := by
  obtain ⟨smaller,tail⟩ := source_evaluates_derivation
    (sourceStep_evaluates_tail step (sourceDerivation_evaluates derivation))
  obtain ⟨larger,previous,greater⟩ := sourceStep_derivation_prepend step tail
  have aligned := sourceDerivation_cost_unique previous derivation
  exact ⟨smaller,tail,aligned ▸ greater⟩

 theorem sourceSteps_derivation_tail {source next result : Term} {cost : Nat}
    (steps : Steps source next) (derivation : SourceDerivation source result cost) :
    ∃ smaller, SourceDerivation next result smaller ∧ smaller ≤ cost := by
  induction steps generalizing cost with
  | refl => exact ⟨cost,derivation,Nat.le_refl _⟩
  | next first rest ih =>
      obtain ⟨middle,tail,less⟩ := sourceStep_derivation_tail first derivation
      obtain ⟨smaller,last,le⟩ := ih tail
      exact ⟨smaller,last,Nat.le_trans le (Nat.le_of_lt less)⟩

 theorem sourceSteps_derivation_strict {source next result : Term} {cost : Nat}
    (steps : Steps source next) (different : source ≠ next)
    (derivation : SourceDerivation source result cost) :
    ∃ smaller, SourceDerivation next result smaller ∧ smaller < cost := by
  cases steps with
  | refl => exact False.elim (different rfl)
  | next first rest =>
      obtain ⟨middle,tail,less⟩ := sourceStep_derivation_tail first derivation
      obtain ⟨smaller,last,le⟩ := sourceSteps_derivation_tail rest tail
      exact ⟨smaller,last,Nat.lt_of_le_of_lt le less⟩

 theorem scoped_rename_identity {n : Nat} {term : Term} (h : Scoped n term)
    (f : Nat → Nat) (hf : ∀ i, i < n → f i = i) : term.rename f = term := by
  induction h generalizing f with
  | bound hi => simp only [Term.rename,hf _ hi]
  | lam h ih =>
      simp only [Term.rename]
      congr 1
      apply ih (liftRename f)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [liftRename,hf i (Nat.lt_of_succ_lt_succ hi)]
  | app _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | mix _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | fix _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | specification _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | prototype _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | binary _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | reflect _ ih => simp only [Term.rename,ih f hf]
  | metadata _ ih => simp only [Term.rename,ih f hf]
  | project _ ih => simp only [Term.rename,ih f hf]
  | get _ ih => simp only [Term.rename,ih f hf]
  | natural _ => simp only [Term.rename]
  | boolean _ => simp only [Term.rename]
  | label _ => simp only [Term.rename]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.rename,ih₁ f hf]
      congr 1
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member f hf)
  | record _ ih =>
      simp only [Term.rename]
      congr 1
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member f hf)
  | inject _ ih => simp only [Term.rename,ih f hf]
  | perform _ ih => simp only [Term.rename,ih f hf]
  | done _ ih => simp only [Term.rename,ih f hf]
  | ifBool _ _ _ ih₁ ih₂ ih₃ => simp only [Term.rename,ih₁ f hf,ih₂ f hf,ih₃ f hf]
  | case _ _ ih₁ ih₂ =>
      simp only [Term.rename,ih₁ f hf]
      congr 1
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro original member
      refine Prod.ext rfl (ih₂ original member (liftRename f) ?_)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [liftRename,hf i (Nat.lt_of_succ_lt_succ hi)]
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.rename,ih₁ f hf,ih₂ f hf]
      congr 1
      apply ih₃ (liftRename f)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [liftRename,hf i (Nat.lt_of_succ_lt_succ hi)]

 theorem scoped_substitute_identity {n : Nat} {term : Term} (h : Scoped n term)
    (f : Nat → Term) (hf : ∀ i, i < n → f i = .bound i) : term.substitute f = term := by
  induction h generalizing f with
  | bound hi => simp only [Term.substitute,hf _ hi]
  | lam h ih =>
      simp only [Term.substitute]
      congr 1
      apply ih (liftSubstitution f)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [liftSubstitution,hf i (Nat.lt_of_succ_lt_succ hi),Term.rename]
  | app _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | mix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | fix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | specification _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | prototype _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | binary _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | reflect _ ih => simp only [Term.substitute,ih f hf]
  | metadata _ ih => simp only [Term.substitute,ih f hf]
  | project _ ih => simp only [Term.substitute,ih f hf]
  | get _ ih => simp only [Term.substitute,ih f hf]
  | natural _ => simp only [Term.substitute]
  | boolean _ => simp only [Term.substitute]
  | label _ => simp only [Term.substitute]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.substitute,ih₁ f hf]
      congr 1
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member f hf)
  | record _ ih =>
      simp only [Term.substitute]
      congr 1
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member f hf)
  | inject _ ih => simp only [Term.substitute,ih f hf]
  | perform _ ih => simp only [Term.substitute,ih f hf]
  | done _ ih => simp only [Term.substitute,ih f hf]
  | ifBool _ _ _ ih₁ ih₂ ih₃ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf,ih₃ f hf]
  | case _ _ ih₁ ih₂ =>
      simp only [Term.substitute,ih₁ f hf]
      congr 1
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro original member
      refine Prod.ext rfl (ih₂ original member (liftSubstitution f) ?_)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [liftSubstitution,hf i (Nat.lt_of_succ_lt_succ hi),Term.rename]
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
      congr 1
      apply ih₃ (liftSubstitution f)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [liftSubstitution,hf i (Nat.lt_of_succ_lt_succ hi),Term.rename]

 theorem scoped_substitution_congr {n : Nat} {term : Term} (h : Scoped n term)
    (first second : Nat → Term) (same : ∀ i, i < n → first i = second i) :
    term.substitute first = term.substitute second := by
  induction h generalizing first second with
  | bound hi => simp only [Term.substitute,same _ hi]
  | lam h ih =>
      simp only [Term.substitute]
      congr 1
      apply ih (liftSubstitution first) (liftSubstitution second)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp only [liftSubstitution,same i (Nat.lt_of_succ_lt_succ hi)]
  | app _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | mix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | fix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | specification _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | prototype _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | binary _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | reflect _ ih => simp only [Term.substitute,ih first second same]
  | metadata _ ih => simp only [Term.substitute,ih first second same]
  | project _ ih => simp only [Term.substitute,ih first second same]
  | get _ ih => simp only [Term.substitute,ih first second same]
  | natural _ | boolean _ | label _ => simp only [Term.substitute]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.substitute,ih₁ first second same]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member first second same)
  | record _ ih =>
      simp only [Term.substitute]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member first second same)
  | inject _ ih => simp only [Term.substitute,ih first second same]
  | perform _ ih => simp only [Term.substitute,ih first second same]
  | done _ ih => simp only [Term.substitute,ih first second same]
  | ifBool _ _ _ ih₁ ih₂ ih₃ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same,ih₃ first second same]
  | case _ _ ih₁ ih₂ =>
      simp only [Term.substitute,ih₁ first second same]
      congr 1
      apply List.map_congr_left
      intro original member
      refine Prod.ext rfl (ih₂ original member (liftSubstitution first) (liftSubstitution second) ?_)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp only [liftSubstitution,same i (Nat.lt_of_succ_lt_succ hi)]
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
      congr 1
      apply ih₃ (liftSubstitution first) (liftSubstitution second)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp only [liftSubstitution,same i (Nat.lt_of_succ_lt_succ hi)]

 theorem liftRename_comp (first second : Nat → Nat) :
    (fun i => liftRename second (liftRename first i)) = liftRename (fun i => second (first i)) := by
  funext i; cases i <;> rfl

 theorem liftRename_substitution_comp (rename : Nat → Nat) (substitution : Nat → Term) :
    (fun i => liftSubstitution substitution (liftRename rename i)) =
      liftSubstitution (fun i => substitution (rename i)) := by
  funext i; cases i <;> rfl

 theorem scoped_rename_comp {n : Nat} {term : Term} (h : Scoped n term)
    (first : Nat → Nat) (second : Nat → Nat) :
    (term.rename first).rename second = term.rename (fun i => second (first i)) := by
  induction h generalizing first second with
  | bound _ => simp only [Term.rename,Term.rename]
  | lam h ih =>
      simp only [Term.rename,Term.rename,ih,liftRename_comp]
  | app _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | mix _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | fix _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | specification _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | prototype _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | binary _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | reflect _ ih => simp only [Term.rename,Term.rename,ih first second]
  | metadata _ ih => simp only [Term.rename,Term.rename,ih first second]
  | project _ ih => simp only [Term.rename,Term.rename,ih first second]
  | get _ ih => simp only [Term.rename,Term.rename,ih first second]
  | natural _ | boolean _ | label _ => simp only [Term.rename,Term.rename]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.rename,Term.rename,List.map_map,ih₁ first second]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member first second)
  | record _ ih =>
      simp only [Term.rename,Term.rename,List.map_map]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member first second)
  | inject _ ih => simp only [Term.rename,ih first second]
  | perform _ ih => simp only [Term.rename,ih first second]
  | done _ ih => simp only [Term.rename,ih first second]
  | ifBool _ _ _ ih₁ ih₂ ih₃ => simp only [Term.rename,ih₁ first second,ih₂ first second,ih₃ first second]
  | case _ _ ih₁ ih₂ =>
      simp only [Term.rename,List.map_map,ih₁ first second]
      congr 1
      apply List.map_congr_left
      intro original member
      refine Prod.ext rfl ?_
      simp only [Function.comp_apply]
      rw [ih₂ original member,liftRename_comp]
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second,ih₃,liftRename_comp]

 theorem scoped_rename_substitute {n : Nat} {term : Term} (h : Scoped n term)
    (first : Nat → Nat) (second : Nat → Term) :
    (term.rename first).substitute second = term.substitute (fun i => second (first i)) := by
  induction h generalizing first second with
  | bound _ => simp only [Term.rename,Term.substitute]
  | lam h ih =>
      simp only [Term.rename,Term.substitute,ih,liftRename_substitution_comp]
  | app _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | mix _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | fix _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | specification _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | prototype _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | binary _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | reflect _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | metadata _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | project _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | get _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | natural _ | boolean _ | label _ => simp only [Term.rename,Term.substitute]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.rename,Term.substitute,List.map_map,ih₁ first second]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member first second)
  | record _ ih =>
      simp only [Term.rename,Term.substitute,List.map_map]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member first second)
  | inject _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | perform _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | done _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | ifBool _ _ _ ih₁ ih₂ ih₃ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second,ih₃ first second]
  | case _ _ ih₁ ih₂ =>
      simp only [Term.rename,Term.substitute,List.map_map,ih₁ first second]
      congr 1
      apply List.map_congr_left
      intro original member
      refine Prod.ext rfl ?_
      simp only [Function.comp_apply]
      rw [ih₂ original member,liftRename_substitution_comp]
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second,ih₃,liftRename_substitution_comp]

 theorem lifted_substitution_scoped {n m : Nat} {substitution : Nat → Term}
    (images : ∀ i, i < n → Scoped m (substitution i)) :
    ∀ i, i < n+1 → Scoped (m+1) (liftSubstitution substitution i) := by
  intro i hi
  cases i with
  | zero => exact .bound (Nat.zero_lt_succ _)
  | succ i => exact scoped_weaken (images i (Nat.lt_of_succ_lt_succ hi))

 theorem lifted_substitution_rename {n m : Nat} {substitution : Nat → Term}
    (images : ∀ i, i < n → Scoped m (substitution i)) (rename : Nat → Nat) :
    ∀ i, i < n+1 →
      (liftSubstitution substitution i).rename (liftRename rename) =
        liftSubstitution (fun j => (substitution j).rename rename) i := by
  intro i hi
  cases i with
  | zero => simp [liftSubstitution,Term.rename,liftRename]
  | succ i =>
      simp only [liftSubstitution]
      rw [scoped_rename_comp (images i (Nat.lt_of_succ_lt_succ hi)),
        scoped_rename_comp (images i (Nat.lt_of_succ_lt_succ hi))]
      rfl

 theorem scoped_substitute_rename {n m : Nat} {term : Term} (h : Scoped n term)
    (substitution : Nat → Term) (images : ∀ i, i < n → Scoped m (substitution i))
    (rename : Nat → Nat) :
    (term.substitute substitution).rename rename =
      term.substitute (fun i => (substitution i).rename rename) := by
  induction h generalizing m substitution rename with
  | bound hi => simp only [Term.substitute]
  | lam h ih =>
      simp only [Term.substitute,Term.rename]
      congr 1
      rw [ih _ (lifted_substitution_scoped images)]
      exact scoped_substitution_congr h _ _ (lifted_substitution_rename images rename)
  | app _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | mix _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | fix _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | specification _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | prototype _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | binary _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | reflect _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | metadata _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | project _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | get _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | natural _ | boolean _ | label _ => simp only [Term.substitute,Term.rename]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.substitute,Term.rename,List.map_map,ih₁ substitution images rename]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member substitution images rename)
  | record _ ih =>
      simp only [Term.substitute,Term.rename,List.map_map]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member substitution images rename)
  | inject _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | perform _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | done _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | ifBool _ _ _ ih₁ ih₂ ih₃ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename,ih₃ substitution images rename]
  | case _ hs ih₁ ih₂ =>
      simp only [Term.substitute,Term.rename,List.map_map,ih₁ substitution images rename]
      congr 1
      apply List.map_congr_left
      intro original member
      refine Prod.ext rfl ?_
      simp only [Function.comp_apply]
      rw [ih₂ original member _ (lifted_substitution_scoped images)]
      exact scoped_substitution_congr (hs original member) _ _ (lifted_substitution_rename images rename)
  | condition _ _ h ih₁ ih₂ ih₃ =>
      simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
      congr 1
      rw [ih₃ _ (lifted_substitution_scoped images)]
      exact scoped_substitution_congr h _ _ (lifted_substitution_rename images rename)

 theorem lifted_substitution_comp {n m k : Nat} {first second : Nat → Term}
    (images : ∀ i, i < n → Scoped m (first i))
    (nextImages : ∀ i, i < m → Scoped k (second i)) :
    ∀ i, i < n+1 → (liftSubstitution first i).substitute (liftSubstitution second) =
      liftSubstitution (fun j => (first j).substitute second) i := by
  intro i hi
  cases i with
  | zero => simp [liftSubstitution,Term.substitute]
  | succ i =>
      simp only [liftSubstitution]
      rw [scoped_rename_substitute (images i (Nat.lt_of_succ_lt_succ hi))]
      simpa only [liftSubstitution] using
        (scoped_substitute_rename (images i (Nat.lt_of_succ_lt_succ hi)) second nextImages Nat.succ).symm

 theorem scoped_substitute_comp {n m k : Nat} {term : Term} (h : Scoped n term)
    (first : Nat → Term) (images : ∀ i, i < n → Scoped m (first i))
    (second : Nat → Term) (nextImages : ∀ i, i < m → Scoped k (second i)) :
    (term.substitute first).substitute second =
      term.substitute (fun i => (first i).substitute second) := by
  induction h generalizing m k first second with
  | bound _ => simp only [Term.substitute]
  | lam h ih =>
      simp only [Term.substitute]
      congr 1
      rw [ih _ (lifted_substitution_scoped images) _ (lifted_substitution_scoped nextImages)]
      exact scoped_substitution_congr h _ _ (lifted_substitution_comp images nextImages)
  | app _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | mix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | fix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | specification _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | prototype _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | binary _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | reflect _ ih => simp only [Term.substitute,ih first images second nextImages]
  | metadata _ ih => simp only [Term.substitute,ih first images second nextImages]
  | project _ ih => simp only [Term.substitute,ih first images second nextImages]
  | get _ ih => simp only [Term.substitute,ih first images second nextImages]
  | natural _ | boolean _ | label _ => simp only [Term.substitute]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.substitute,List.map_map,ih₁ first images second nextImages]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member first images second nextImages)
  | record _ ih =>
      simp only [Term.substitute,List.map_map]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member first images second nextImages)
  | inject _ ih => simp only [Term.substitute,ih first images second nextImages]
  | perform _ ih => simp only [Term.substitute,ih first images second nextImages]
  | done _ ih => simp only [Term.substitute,ih first images second nextImages]
  | ifBool _ _ _ ih₁ ih₂ ih₃ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages,ih₃ first images second nextImages]
  | case _ hs ih₁ ih₂ =>
      simp only [Term.substitute,List.map_map,ih₁ first images second nextImages]
      congr 1
      apply List.map_congr_left
      intro original member
      refine Prod.ext rfl ?_
      simp only [Function.comp_apply]
      rw [ih₂ original member _ (lifted_substitution_scoped images) _ (lifted_substitution_scoped nextImages)]
      exact scoped_substitution_congr (hs original member) _ _ (lifted_substitution_comp images nextImages)
  | condition _ _ h ih₁ ih₂ ih₃ =>
      simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
      congr 1
      rw [ih₃ _ (lifted_substitution_scoped images) _ (lifted_substitution_scoped nextImages)]
      exact scoped_substitution_congr h _ _ (lifted_substitution_comp images nextImages)

/-- The assignment gives each address a finite source computation; it does NOT
recursively unfold its pointers. In particular a recursive address can denote a
source Fix while its origin denotes the one-step expansion of that same Fix. -/
abbrev AddressMeaning := Address → Term

def environmentSubstitution (meaning : AddressMeaning) (environment : Environment) (index : Nat) : Term :=
  match environment[index]? with
  | some address => meaning address
  | none => .bound index

def closeTerm (meaning : AddressMeaning) (environment : Environment) (term : Term) : Term :=
  match environment with
  | [] => term
  | _::_ => term.substitute (environmentSubstitution meaning environment)

def closeOrigin (meaning : AddressMeaning) (origin : Closure) : Term :=
  closeTerm meaning origin.environment origin.term

def valueMeaning (meaning : AddressMeaning) : RuntimeValue → Term
  | .closure body environment => closeTerm meaning environment (.lam body)
  | .natural value => .nat value
  | .boolean value => .boolean value
  | .label value => .label value
  | .record fields => .record (fields.map fun field => (field.1,meaning field.2))
  | .specification metadata extension => .specification (meaning metadata) (meaning extension)
  | .prototype specification target => .prototype (meaning specification) (meaning target)
  | .variant tag payload => .inject tag (meaning payload)

/- The evaluating phase retains its source meaning. A cache additionally has
an actual independent reference evaluation, rather than an arbitrary cached
scalar. Stable origins let the same relation survive the phase change. -/
/-- Each allocated graph name denotes a closed source computation. The
assignment remains finite syntax even when these computations contain Fix. -/
def MeaningsScoped (bound : Nat) (meaning : AddressMeaning) : Prop :=
  ∀ address, address < bound → Scoped 0 (meaning address)

 theorem environmentSubstitution_scoped {bound : Nat} {meaning : AddressMeaning}
    {environment : Environment} (names : MeaningsScoped bound meaning)
    (captures : EnvironmentValid bound environment) :
    ∀ index, index < environment.length → Scoped 0 (environmentSubstitution meaning environment index) := by
  intro index hi
  have found : environment[index]? = some environment[index] := getElem?_pos environment index hi
  simpa [environmentSubstitution,found] using names _ (captures _ (List.mem_of_getElem? found))

 theorem closeTerm_eq_substitution {meaning : AddressMeaning} {environment : Environment}
    {term : Term} (h : Scoped environment.length term) :
    closeTerm meaning environment term = term.substitute (environmentSubstitution meaning environment) := by
  cases environment with
  | nil =>
      exact (scoped_substitute_identity h _ (by intro i hi; simp at hi)).symm
  | cons _ _ => rfl

/-- Extending an allocated prefix cannot change the source meaning of a
lexical capture. The agreement is only required at actually allocated names. -/
 theorem closeTerm_meaning_congr {bound : Nat} {first second : AddressMeaning}
    {environment : Environment} {term : Term} (captures : EnvironmentValid bound environment)
    (scope : Scoped environment.length term) (same : ∀ address, address < bound → first address = second address) :
    closeTerm first environment term = closeTerm second environment term := by
  rw [closeTerm_eq_substitution scope,closeTerm_eq_substitution scope]
  apply scoped_substitution_congr scope
  intro index hi
  have found : environment[index]? = some environment[index] := getElem?_pos environment index hi
  simp only [environmentSubstitution,found]
  exact same _ (captures _ (List.mem_of_getElem? found))

/-- A call allocates a name for its lazy argument. This equation proves that
entering the captured body with that name is exactly independent source beta
substitution, even when the environment points into a cyclic heap. -/
 theorem closeTerm_beta {bound : Nat} {meaning extended : AddressMeaning}
    {captured : Environment} {body argument : Term}
    (names : MeaningsScoped bound meaning) (captures : EnvironmentValid bound captured)
    (bodyScope : Scoped (captured.length+1) body) (argumentScope : Scoped 0 argument)
    (same : ∀ address, address < bound → meaning address = extended address)
    (fresh : extended bound = argument) :
    instantiate (body.substitute (liftSubstitution (environmentSubstitution meaning captured))) argument =
      closeTerm extended (bound::captured) body := by
  let sigma := environmentSubstitution meaning captured
  let inst : Nat → Term := fun i => match i with | 0 => argument | n+1 => .bound n
  have images : ∀ i, i < captured.length → Scoped 0 (sigma i) :=
    environmentSubstitution_scoped names captures
  have nextImages : ∀ i, i < 1 → Scoped 0 (inst i) := by
    intro i hi
    have : i = 0 := by omega
    subst i
    exact argumentScope
  change (body.substitute (liftSubstitution sigma)).substitute inst = _
  rw [scoped_substitute_comp bodyScope _ (lifted_substitution_scoped images) inst nextImages]
  rw [closeTerm_eq_substitution (by simpa using bodyScope)]
  apply scoped_substitution_congr bodyScope
  intro i hi
  cases i with
  | zero => simp [liftSubstitution,Term.substitute,environmentSubstitution,fresh,inst]
  | succ i =>
      have lt : i < captured.length := by omega
      have closed := images i lt
      have renameSame := scoped_rename_identity closed Nat.succ (by intro j hj; omega)
      have substSame := scoped_substitute_identity closed inst (by intro j hj; omega)
      have found : captured[i]? = some captured[i] := getElem?_pos captured i lt
      simp only [liftSubstitution,renameSame,substSame,environmentSubstitution,List.getElem?_cons_succ,found]
      simpa only [sigma,environmentSubstitution,found] using same _ (captures _ (List.mem_of_getElem? found))

 theorem closeTerm_scoped {bound : Nat} {meaning : AddressMeaning} {environment : Environment}
    {term : Term} (names : MeaningsScoped bound meaning)
    (captures : EnvironmentValid bound environment) (hscope : Scoped environment.length term) :
    Scoped 0 (closeTerm meaning environment term) := by
  cases environment with
  | nil => exact hscope
  | cons address rest =>
      apply scoped_substitute hscope (environmentSubstitution meaning (address::rest)) 0
      intro index hi
      have found : (address::rest)[index]? = some (address::rest)[index] := getElem?_pos (address::rest) index hi
      have allocated := captures _ (List.mem_of_getElem? found)
      simpa [environmentSubstitution,found] using names _ allocated

 theorem valueMeaning_scoped {bound : Nat} {meaning : AddressMeaning} {value : RuntimeValue}
    (names : MeaningsScoped bound meaning) (valid : RuntimeValueValid bound value) :
    Scoped 0 (valueMeaning meaning value) := by
  cases value with
  | closure body environment => exact closeTerm_scoped names valid.2 (Scoped.lam valid.1)
  | natural n => exact .natural _
  | boolean n => exact .boolean _
  | label n => exact .label _
  | record fields =>
      apply Scoped.record
      intro field member
      obtain ⟨original,ho,rfl⟩ := List.mem_map.mp member
      exact names _ (valid original ho)
  | specification metadata extension => exact .specification (names _ valid.1) (names _ valid.2)
  | prototype specification target => exact .prototype (names _ valid.1) (names _ valid.2)
  | variant tag payload => exact .inject (names _ valid)

def CellRealizes (meaning : AddressMeaning) (address : Address) (cell : Cell) : Prop :=
  Steps (meaning address) (closeOrigin meaning (cellOrigin cell)) ∧
    match cell with
    | .cached _ value => Evaluates (meaning address) (valueMeaning meaning value)
    | _ => True

def HeapRealizes (meaning : AddressMeaning) (heap : Array Cell) : Prop :=
  ∀ (address : Nat) (cell : Cell), heap[address]? = some cell → CellRealizes meaning address cell

 theorem valueMeaning_congr {bound : Nat} {first second : AddressMeaning} {value : RuntimeValue}
    (valid : RuntimeValueValid bound value)
    (same : ∀ address, address < bound → first address = second address) :
    valueMeaning first value = valueMeaning second value := by
  cases value with
  | closure body environment => exact closeTerm_meaning_congr valid.2 (Scoped.lam valid.1) same
  | natural _ | boolean _ | label _ => rfl
  | record fields =>
      simp only [valueMeaning]
      congr 1
      apply List.map_congr_left
      intro field member
      exact Prod.ext rfl (same _ (valid field member))
  | specification metadata extension => simp only [valueMeaning,same _ valid.1,same _ valid.2]
  | prototype specification target => simp only [valueMeaning,same _ valid.1,same _ valid.2]
  | variant tag payload => simp only [valueMeaning,same _ valid]

 theorem cellRealizes_congr {bound address : Nat} {first second : AddressMeaning} {cell : Cell}
    (allocated : address < bound) (valid : CellValid bound cell)
    (same : ∀ address, address < bound → first address = second address) :
    CellRealizes first address cell ↔ CellRealizes second address cell := by
  cases cell with
  | suspended origin | evaluating origin =>
      simp only [CellRealizes,cellOrigin,closeOrigin,same _ allocated,
        closeTerm_meaning_congr valid.2 valid.1 same]
  | cached origin value =>
      simp only [CellRealizes,cellOrigin,closeOrigin,same _ allocated,
        closeTerm_meaning_congr valid.1.2 valid.1.1 same,valueMeaning_congr valid.2 same]

 theorem heapRealizes_congr {heap : Array Cell} {first second : AddressMeaning}
    (valid : HeapValid heap) (same : ∀ address, address < heap.size → first address = second address)
    (realizes : HeapRealizes first heap) : HeapRealizes second heap := by
  intro address cell found
  have allocated := (Array.getElem?_eq_some_iff.mp found).1
  exact (cellRealizes_congr allocated (valid address cell found) same).mp (realizes address cell found)

 theorem heapRealizes_push {heap : Array Cell} {meaning : AddressMeaning} {cell : Cell}
    (realizes : HeapRealizes meaning heap) (fresh : CellRealizes meaning heap.size cell) :
    HeapRealizes meaning (heap.push cell) := by
  intro address other found
  by_cases eq : address = heap.size
  · subst address
    simp at found
    subst other
    exact fresh
  · apply realizes address other
    simpa [Array.getElem?_push,eq] using found

def frameMeaning (meaning : AddressMeaning) (frame : Frame) (hole : Term) : Term :=
  match frame with
  | .argument term environment => .app hole (closeTerm meaning environment term)
  | .update _ => hole
  | .field name => .get hole name
  | .reflect => .reflect hole
  | .metadata => .metadata hole
  | .project => .project hole
  | .extend fields environment => .extend hole
      (fields.map fun field => (field.1,closeTerm meaning environment field.2))
  | .condition zero successorBody environment => .ifZero hole
      (closeTerm meaning environment zero)
      (successorBody.substitute (liftSubstitution (environmentSubstitution meaning environment)))
  | .binaryLeft primitive right environment => .binary primitive hole (closeTerm meaning environment right)
  | .binaryRight primitive left => .binary primitive (valueMeaning meaning left) hole
  | .case arms environment => .case hole
      (arms.map fun arm => (arm.1,arm.2.substitute (liftSubstitution (environmentSubstitution meaning environment))))
  | .ifBool whenTrue whenFalse environment => .ifBool hole
      (closeTerm meaning environment whenTrue) (closeTerm meaning environment whenFalse)

 theorem frameMeaning_congr {bound : Nat} {first second : AddressMeaning} {frame : Frame} {hole : Term}
    (valid : FrameValid bound frame)
    (same : ∀ address, address < bound → first address = second address) :
    frameMeaning first frame hole = frameMeaning second frame hole := by
  cases frame with
  | argument term environment | binaryLeft primitive term environment =>
      simp only [frameMeaning,closeTerm_meaning_congr valid.2 valid.1 same]
  | update _ | field _ | reflect | metadata | project => rfl
  | binaryRight primitive value => simp only [frameMeaning,valueMeaning_congr valid same]
  | extend fields environment =>
      simp only [frameMeaning]
      congr 1
      apply List.map_congr_left
      intro field member
      exact Prod.ext rfl (closeTerm_meaning_congr valid.1 (valid.2 field member) same)
  | condition zero body environment =>
      simp only [frameMeaning,closeTerm_meaning_congr valid.1 valid.2.1 same]
      congr 1
      apply scoped_substitution_congr valid.2.2
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
          have lt : i < environment.length := by omega
          have found : environment[i]? = some environment[i] := getElem?_pos environment i lt
          simp only [liftSubstitution,environmentSubstitution,found,same _ (valid.1 _ (List.mem_of_getElem? found))]
  | case arms environment =>
      simp only [frameMeaning]
      congr 1
      apply List.map_congr_left
      intro arm member
      refine Prod.ext rfl ?_
      apply scoped_substitution_congr (valid.2 arm member)
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
          have lt : i < environment.length := by omega
          have found : environment[i]? = some environment[i] := getElem?_pos environment i lt
          simp only [liftSubstitution,environmentSubstitution,found,same _ (valid.1 _ (List.mem_of_getElem? found))]
  | ifBool whenTrue whenFalse environment =>
      simp only [frameMeaning,closeTerm_meaning_congr valid.1 valid.2.1 same,
        closeTerm_meaning_congr valid.1 valid.2.2 same]

def stackMeaning (meaning : AddressMeaning) (stack : List Frame) (hole : Term) : Term :=
  stack.foldl (fun prior frame => frameMeaning meaning frame prior) hole

def controlMeaning (meaning : AddressMeaning) : Control → Option Term
  | .evaluate term environment => some (closeTerm meaning environment term)
  | .enter address => some (meaning address)
  | .returned value | .complete value => some (valueMeaning meaning value)
  | .blackhole _ | .refused _ => none
  -- A yielded program means its stuck source redex `perform plan`.
  | .yielded plan => some (.perform (meaning plan))

 theorem valueMeaning_value (meaning : AddressMeaning) (value : RuntimeValue) :
    Value (valueMeaning meaning value) := by
  cases value with
  | closure body environment =>
      cases environment <;> simp only [valueMeaning,closeTerm,Term.substitute]
      all_goals exact .function _
  | natural n => exact .natural _
  | boolean n => exact .boolean _
  | label n => exact .label _
  | record fields => exact .record _
  | specification _ _ => exact .specification _ _
  | prototype _ _ => exact .prototype _ _
  | variant _ _ => exact .inject _ _

/-- A dynamic demand focus reads the actual cell phase. The fixed source
address meaning remains in HeapRealizes and local update provenance; this
focus exposes already justified unfolding/cache reductions at pointer entry. -/
def enteredFocus (meaning : AddressMeaning) (heap : Array Cell) : Control → Option Term
  | .enter address => match heap[address]? with
      | some (.suspended origin) => some (closeOrigin meaning origin)
      | some (.cached _ value) => some (valueMeaning meaning value)
      | some (.evaluating _) | none => none
  | control => controlMeaning meaning control

 theorem enteredFocus_steps {meaning : AddressMeaning} {heap : Array Cell} {control : Control} {before after : Term}
    (heapRealizes : HeapRealizes meaning heap) (original : controlMeaning meaning control = some before)
    (entered : enteredFocus meaning heap control = some after) : Steps before after := by
  cases control with
  | enter address =>
      simp only [controlMeaning,Option.some.injEq] at original
      subst before
      cases found : heap[address]? with
      | none => simp [enteredFocus,found] at entered
      | some cell =>
          cases cell with
          | evaluating _ => simp [enteredFocus,found] at entered
          | suspended origin =>
              simp [enteredFocus,found] at entered
              subst after
              exact (heapRealizes address _ found).1
          | cached origin value =>
              simp [enteredFocus,found] at entered
              subst after
              exact (heapRealizes address _ found).2.1
  | evaluate _ _ | returned _ | complete _ | blackhole _ | refused _ | yielded _ =>
      have same : some before = some after := original.symm.trans entered
      have eq := Option.some.inj same
      subst after
      exact Steps.refl _

 theorem sourceSteps_frame (meaning : AddressMeaning) (frame : Frame)
    {before after : Term} (steps : Steps before after) :
    Steps (frameMeaning meaning frame before) (frameMeaning meaning frame after) := by
  induction steps with
  | refl => exact .refl _
  | next step steps ih =>
      apply Steps.next _ ih
      cases frame with
      | argument term environment => exact .application _ step
      | update _ => exact step
      | field name => exact .target _ step
      | reflect => exact .reflectStep step
      | metadata => exact .metadataStep step
      | project => exact .projectStep step
      | extend fields environment => exact .extendTarget _ step
      | condition zero successorBody environment => exact .condition _ _ step
      | binaryLeft primitive right environment => exact .binaryLeft _ _ step
      | binaryRight primitive left => exact .binaryRight _ _ (valueMeaning_value _ _) step
      | case arms environment => exact .caseTarget _ step
      | ifBool whenTrue whenFalse environment => exact .ifCondition _ _ step

/-- Every active update carries its own demand-segment source evaluation.
Erasing update frames would lose the LOCAL proof required when writing a cache:
a whole-program reduction alone cannot justify that heap-cell result. -/
def StackRealizes (meaning : AddressMeaning) (root focus : Term) : List Frame → Prop
  | [] => Steps root focus
  | .update address::rest =>
      Steps (meaning address) focus ∧ StackRealizes meaning root (meaning address) rest
  | frame::rest => StackRealizes meaning root (frameMeaning meaning frame focus) rest

 theorem stackRealizes_congr {bound : Nat} {first second : AddressMeaning} {root focus : Term}
    {stack : List Frame} (valid : ∀ frame ∈ stack, FrameValid bound frame)
    (same : ∀ address, address < bound → first address = second address)
    (realizes : StackRealizes first root focus stack) : StackRealizes second root focus stack := by
  induction stack generalizing focus with
  | nil => exact realizes
  | cons frame rest ih =>
      have hv := valid frame (List.mem_cons_self ..)
      have ht : ∀ frame ∈ rest, FrameValid bound frame := fun f member => valid f (List.mem_cons_of_mem _ member)
      cases frame with
      | update address =>
          exact ⟨by simpa only [StackRealizes,same _ hv] using realizes.1,
            by simpa only [same _ hv] using ih ht realizes.2⟩
      | argument _ _ | field _ | reflect | metadata | project | extend _ _ | condition _ _ _ | binaryLeft _ _ _ | binaryRight _ _ | case _ _ | ifBool _ _ _ =>
          simpa only [StackRealizes,frameMeaning_congr hv same] using ih ht realizes

 theorem stackRealizes_steps {meaning : AddressMeaning} {root before after : Term}
    {stack : List Frame} (realizes : StackRealizes meaning root before stack)
    (steps : Steps before after) : StackRealizes meaning root after stack := by
  induction stack generalizing before after with
  | nil => exact sourceSteps_trans realizes steps
  | cons frame rest ih =>
      cases frame with
      | update address => exact ⟨sourceSteps_trans realizes.1 steps,realizes.2⟩
      | argument _ _ | field _ | reflect | metadata | project | extend _ _ | condition _ _ _ | binaryLeft _ _ _ | binaryRight _ _ | case _ _ | ifBool _ _ _ =>
          exact ih realizes (sourceSteps_frame _ _ steps)

 theorem sourceSteps_stack (meaning : AddressMeaning) (stack : List Frame) {before after : Term}
    (steps : Steps before after) : Steps (stackMeaning meaning stack before) (stackMeaning meaning stack after) := by
  induction stack generalizing before after with
  | nil => exact steps
  | cons frame rest ih => exact ih (sourceSteps_frame meaning frame steps)

/-- Erasing operational update frames is sound AFTER retaining their local
provenance: each erased boundary contributes its actual demand derivation. -/
 theorem stackRealizes_erases {meaning : AddressMeaning} {root focus : Term} {stack : List Frame}
    (realizes : StackRealizes meaning root focus stack) : Steps root (stackMeaning meaning stack focus) := by
  induction stack generalizing focus with
  | nil => exact realizes
  | cons frame rest ih =>
      cases frame with
      | update address =>
          exact sourceSteps_trans (ih realizes.2) (sourceSteps_stack meaning rest realizes.1)
      | argument _ _ | field _ | reflect | metadata | project | extend _ _ | condition _ _ _ | binaryLeft _ _ _ | binaryRight _ _ | case _ _ | ifBool _ _ _ =>
          exact ih realizes

 theorem heapRealizes_set {meaning : AddressMeaning} {heap : Array Cell}
    {address : Nat} {cell : Cell} (realizes : HeapRealizes meaning heap)
    (valid : CellRealizes meaning address cell) : HeapRealizes meaning (heap.set! address cell) := by
  intro index other found
  by_cases bound : address < heap.size
  · by_cases same : index = address
    · subst index
      simp [Array.set!,bound] at found
      subst other
      exact valid
    · apply realizes index other
      simpa [Array.set!,same,Ne.symm same] using found
  · apply realizes index other
    simpa [Array.set!,Array.setIfInBounds,bound] using found

/-- The cache proof is recovered from the actual local update segment, not an
assumed evaluator oracle. This works for cyclic assignments and arbitrary
runtime closures/records as well as scalars. -/
 theorem cachedCell_realizes {meaning : AddressMeaning} {heap : Array Cell}
    {address : Nat} {origin : Closure} {root : Term} {rest : List Frame} {value : RuntimeValue}
    (heapRealizes : HeapRealizes meaning heap)
    (found : heap[address]? = some (.evaluating origin))
    (stackRealizes : StackRealizes meaning root (valueMeaning meaning value) (.update address::rest)) :
    CellRealizes meaning address (.cached origin value) :=
  ⟨(heapRealizes address _ found).1,stackRealizes.1,valueMeaning_value _ _⟩

/-- The concrete heap/continuation relation retains source meanings at shared
addresses and local provenance for every active update. Initialization,
running/finished transition preservation and ground soundness are proved
below; no source-evaluator oracle is a field of this relation. -/
def GraphRepresents (state : State) (source : Term) : Prop :=
  LexicalInvariant state ∧ BusyInvariant state ∧ FinalStackInvariant state ∧ ∃ meaning, MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
    ∃ residual, controlMeaning meaning state.control = some residual ∧
      StackRealizes meaning source residual state.stack

 theorem graph_initializes {source : Term} (closed : Scoped 0 source) :
    GraphRepresents (initial source) source := by
  refine ⟨initial_lexicalInvariant closed,initial_busyInvariant source,initial_finalStackInvariant source,fun _ => .bound 0,?_,?_,source,?_,?_⟩
  · intro address allocated; simp [initial] at allocated
  · intro address cell found; simp [initial] at found
  · rfl
  · exact .refl _

 theorem graph_complete_natural_sound {state : State} {source : Term} {number : Nat}
    (represented : GraphRepresents state source)
    (complete : state.control = .complete (.natural number)) :
    Evaluates source (.nat number) := by
  obtain ⟨_,_,final,meaning,_,_,residual,control,steps⟩ := represented
  have empty := final _ complete
  simp [complete,controlMeaning,valueMeaning] at control
  subst residual
  simpa [empty,StackRealizes] using And.intro steps (Value.natural number)

 theorem graph_complete_label_sound {state : State} {source : Term} {name : String}
    (represented : GraphRepresents state source)
    (complete : state.control = .complete (.label name)) :
    Evaluates source (.label name) := by
  obtain ⟨_,_,final,meaning,_,_,residual,control,steps⟩ := represented
  have empty := final _ complete
  simp [complete,controlMeaning,valueMeaning] at control
  subst residual
  simpa [empty,StackRealizes] using And.intro steps (Value.label name)

 theorem graph_complete_boolean_sound {state : State} {source : Term} {value : Bool}
    (represented : GraphRepresents state source)
    (complete : state.control = .complete (.boolean value)) :
    Evaluates source (.boolean value) := by
  obtain ⟨_,_,final,meaning,_,_,residual,control,steps⟩ := represented
  have empty := final _ complete
  simp [complete,controlMeaning,valueMeaning] at control
  subst residual
  simpa [empty,StackRealizes] using And.intro steps (Value.boolean value)

/-- Finished closures, records, specifications and prototypes have source
values through the same concrete heap graph assignment as scalars. The
existential retains the HeapRealizes proof; it is not an oracle or contextual
equivalence assertion about arbitrary external consumers. -/
 theorem graph_complete_value_sound {state : State} {source : Term} {value : RuntimeValue}
    (represented : GraphRepresents state source) (complete : state.control = .complete value) :
    ∃ meaning : AddressMeaning, MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
      Evaluates source (valueMeaning meaning value) := by
  obtain ⟨_,_,final,meaning,names,heap,focus,control,stack⟩ := represented
  have empty := final value complete
  simp [controlMeaning,complete] at control
  subst focus
  refine ⟨meaning,names,heap,?_,valueMeaning_value meaning value⟩
  simpa only [empty,StackRealizes] using stack

/-- The concrete graph assignment justifies both fixed lexical names and the
phase-sensitive source focus used for demand simulation. All erased update
boundaries are discharged from their retained local source derivations. -/
 theorem graph_enteredFocus_source {state : State} {source : Term}
    (represented : GraphRepresents state source) :
    ∃ meaning : AddressMeaning, MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
      ∀ focus, enteredFocus meaning state.heap state.control = some focus →
        Steps source (stackMeaning meaning state.stack focus) := by
  obtain ⟨_,_,_,meaning,names,heap,before,original,stack⟩ := represented
  refine ⟨meaning,names,heap,?_⟩
  intro focus entered
  exact sourceSteps_trans (stackRealizes_erases stack)
    (sourceSteps_stack meaning state.stack (enteredFocus_steps heap original entered))

/-- Every actual continuation frame demands its hole. A terminating whole
context therefore supplies a finite derivation for the demanded focus. -/
 theorem frame_derivation_demand {meaning : AddressMeaning} {frame : Frame} {focus result : Term} {cost : Nat}
    (derivation : SourceDerivation (frameMeaning meaning frame focus) result cost) :
    ∃ value demandCost, SourceDerivation focus value demandCost ∧ demandCost ≤ cost := by
  cases frame with
  | update address => exact ⟨result,cost,derivation,Nat.le_refl _⟩
  | argument term environment =>
      cases derivation with
      | value value => cases value
      | applicationLambda first second => exact ⟨_,_,first,by omega⟩
      | applicationSpecification first second => exact ⟨_,_,first,by omega⟩
  | field name =>
      cases derivation with
      | value value => cases value
      | field first found second => exact ⟨_,_,first,by omega⟩
  | reflect =>
      cases derivation with
      | value value => cases value
      | reflect first second => exact ⟨_,_,first,by omega⟩
  | metadata =>
      cases derivation with
      | value value => cases value
      | metadata first second => exact ⟨_,_,first,by omega⟩
  | project =>
      cases derivation with
      | value value => cases value
      | project first second => exact ⟨_,_,first,by omega⟩
  | extend fields environment =>
      cases derivation with
      | value value => cases value
      | extend first => exact ⟨_,_,first,by omega⟩
  | condition zero body environment =>
      cases derivation with
      | value value => cases value
      | zero first second => exact ⟨_,_,first,by omega⟩
      | successor first second => exact ⟨_,_,first,by omega⟩
  | binaryLeft primitive right environment =>
      cases derivation with
      | value value => cases value
      | binary first second found => exact ⟨_,_,first,by omega⟩
  | binaryRight primitive left =>
      cases derivation with
      | value value => cases value
      | binary first second found => exact ⟨_,_,second,by omega⟩
  | case arms environment =>
      cases derivation with
      | value value => cases value
      | case first found second => exact ⟨_,_,first,by omega⟩
  | ifBool whenTrue whenFalse environment =>
      cases derivation with
      | value value => cases value
      | ifTrue first second => exact ⟨_,_,first,by omega⟩
      | ifFalse first second => exact ⟨_,_,first,by omega⟩

 theorem stack_derivation_demand {meaning : AddressMeaning} {stack : List Frame} {focus result : Term} {cost : Nat}
    (derivation : SourceDerivation (stackMeaning meaning stack focus) result cost) :
    ∃ value demandCost, SourceDerivation focus value demandCost ∧ demandCost ≤ cost := by
  induction stack generalizing focus result cost with
  | nil => exact ⟨result,cost,derivation,Nat.le_refl _⟩
  | cons frame rest ih =>
      obtain ⟨middle,middleCost,middleDerivation,middleLe⟩ := ih derivation
      obtain ⟨value,demandCost,demand,demandLe⟩ := frame_derivation_demand middleDerivation
      exact ⟨value,demandCost,demand,Nat.le_trans demandLe middleLe⟩

/-- Termination of the independent source program gives a finite demand
budget at every represented phase-sensitive focus. The heap assignment is
constructed by the existing graph theorem, rather than an evaluation oracle. -/
 theorem graph_terminating_demand {state : State} {source result : Term}
    (represented : GraphRepresents state source) (terminates : Evaluates source result) :
    ∃ meaning : AddressMeaning, MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
      ∀ focus, enteredFocus meaning state.heap state.control = some focus →
        ∃ value cost, SourceDerivation focus value cost := by
  obtain ⟨meaning,names,heap,wholeSteps⟩ := graph_enteredFocus_source represented
  refine ⟨meaning,names,heap,?_⟩
  intro focus entered
  obtain ⟨wholeCost,whole⟩ := source_evaluates_derivation
    (sourceSteps_evaluates_tail (wholeSteps focus entered) terminates)
  obtain ⟨value,cost,demand,_⟩ := stack_derivation_demand whole
  exact ⟨value,cost,demand⟩

/-- The source contexts that start a lexical demand without allocating heap
cells. This enumerates actual syntax and actual machine frames. -/
inductive DemandContext where
  | argument (term : Term)
  | field (name : String)
  | reflect | metadata | project
  | extend (fields : List (String × Term))
  | condition (zero successorBody : Term)
  | binary (primitive : Primitive) (right : Term)
  | case (arms : List (String × Term))
  | ifBool (whenTrue whenFalse : Term)

def DemandContext.term : DemandContext → Term → Term
  | .argument arg, hole => .app hole arg
  | .field name, hole => .get hole name
  | .reflect, hole => .reflect hole
  | .metadata, hole => .metadata hole
  | .project, hole => .project hole
  | .extend fields, hole => .extend hole fields
  | .condition zero successorBody, hole => .ifZero hole zero successorBody
  | .binary primitive right, hole => .binary primitive hole right
  | .case arms, hole => .case hole arms
  | .ifBool whenTrue whenFalse, hole => .ifBool hole whenTrue whenFalse

def DemandContext.frame : DemandContext → Environment → Frame
  | .argument arg, environment => .argument arg environment
  | .field name, _ => .field name
  | .reflect, _ => .reflect
  | .metadata, _ => .metadata
  | .project, _ => .project
  | .extend fields, environment => .extend fields environment
  | .condition zero successorBody, environment => .condition zero successorBody environment
  | .binary primitive right, environment => .binaryLeft primitive right environment
  | .case arms, environment => .case arms environment
  | .ifBool whenTrue whenFalse, environment => .ifBool whenTrue whenFalse environment

 theorem demandContext_closes (context : DemandContext) (meaning : AddressMeaning)
    (environment : Environment) (hole : Term)
    (scope : Scoped environment.length (context.term hole)) :
    closeTerm meaning environment (context.term hole) =
      frameMeaning meaning (context.frame environment) (closeTerm meaning environment hole) := by
  cases environment with
  | cons address rest => cases context <;> simp [DemandContext.term,DemandContext.frame,closeTerm,Term.substitute,frameMeaning]
  | nil =>
      have lifted : liftSubstitution (environmentSubstitution meaning []) = Term.bound := by
        funext i
        cases i <;> simp [liftSubstitution,environmentSubstitution,Term.rename]
      cases context with
      | condition zero body =>
          have scopedBody : Scoped 1 body := (scoped_condition_iff ..).mp scope |>.2.2
          simp only [DemandContext.term,DemandContext.frame,closeTerm,frameMeaning,lifted,
            scoped_substitute_identity scopedBody Term.bound (by intros; rfl)]
      | extend fields => simp [DemandContext.term,DemandContext.frame,closeTerm,frameMeaning]
      | case arms =>
          have scopedArms : ∀ arm ∈ arms, Scoped 1 arm.2 := (scoped_case_iff ..).mp scope |>.2
          simp only [DemandContext.term,DemandContext.frame,closeTerm,frameMeaning,lifted]
          congr 1
          apply Eq.symm
          apply Eq.trans _ (List.map_id' _)
          apply List.map_congr_left
          intro arm member
          exact Prod.ext rfl (scoped_substitute_identity (scopedArms arm member) Term.bound (by intros; rfl))
      | argument _ | field _ | reflect | metadata | project | binary _ _ | ifBool _ _ => rfl

 theorem demandContext_dispatch {state : State} {context : DemandContext} {hole : Term} {environment : Environment}
    (evaluate : state.control = .evaluate (context.term hole) environment) :
    stepRaw state = {state with control := .evaluate hole environment,stack := context.frame environment::state.stack} := by
  cases context <;> simp [stepRaw,evaluate,DemandContext.term,DemandContext.frame]





inductive ImmediateValue where
  | closure (body : Term)
  | natural (number : Nat)
  | boolean (value : Bool)
  | label (name : String)

def ImmediateValue.term : ImmediateValue → Term
  | .closure body => .lam body
  | .natural number => .nat number
  | .boolean value => .boolean value
  | .label name => .label name

def ImmediateValue.runtime : ImmediateValue → Environment → RuntimeValue
  | .closure body, environment => .closure body environment
  | .natural number, _ => .natural number
  | .boolean value, _ => .boolean value
  | .label name, _ => .label name



inductive ObjectAccess where
  | reflect | metadata | project

def ObjectAccess.frame : ObjectAccess → Frame
  | .reflect => .reflect | .metadata => .metadata | .project => .project

def ObjectAccess.value : ObjectAccess → Address → Address → RuntimeValue
  | .reflect, first, second => .prototype first second
  | .metadata, first, second => .specification first second
  | .project, first, second => .prototype first second

def ObjectAccess.address : ObjectAccess → Address → Address → Address
  | .reflect, first, _ => first | .metadata, first, _ => first | .project, _, second => second





 theorem valueTerm_meaning {value : RuntimeValue} {term : Term} (found : valueTerm value = some term)
    (meaning : AddressMeaning) : valueMeaning meaning value = term := by
  cases value <;> simp [valueTerm] at found
  all_goals subst term; rfl

 theorem scalarValue_meaning {value : RuntimeValue} {term : Term} (found : scalarValue term = some value)
    (meaning : AddressMeaning) : valueMeaning meaning value = term := by
  cases term <;> simp [scalarValue] at found
  all_goals subst value; rfl









 theorem closeTerm_app (meaning : AddressMeaning) (environment : Environment) (function argument : Term) :
    closeTerm meaning environment (.app function argument) =
      .app (closeTerm meaning environment function) (closeTerm meaning environment argument) := by
  cases environment <;> simp [closeTerm,Term.substitute]

 theorem closeTerm_lambda {meaning : AddressMeaning} {environment : Environment} {body : Term}
    (scope : Scoped (environment.length+1) body) :
    closeTerm meaning environment (.lam body) =
      .lam (body.substitute (liftSubstitution (environmentSubstitution meaning environment))) := by
  rw [closeTerm_eq_substitution (Scoped.lam scope)]
  simp only [Term.substitute]

def extendMeaning (meaning : AddressMeaning) (address : Address) (term : Term) : AddressMeaning :=
  fun index => if index = address then term else meaning index

 theorem extendMeaning_prefix (meaning : AddressMeaning) (bound : Nat) (term : Term) :
    ∀ address, address < bound → meaning address = extendMeaning meaning bound term address := by
  intro address allocated
  simp [extendMeaning,Nat.ne_of_lt allocated]

/-- The shared allocation lemma records the actual suspended origin, its
closed source name and exact agreement at every old allocated address. -/
 theorem allocateClosure_realizes {heap : Array Cell} {meaning : AddressMeaning}
    {term : Term} {environment : Environment} (validHeap : HeapValid heap)
    (names : MeaningsScoped heap.size meaning) (realizes : HeapRealizes meaning heap)
    (scope : Scoped environment.length term) (captures : EnvironmentValid heap.size environment) :
    ∃ extended : AddressMeaning,
      MeaningsScoped (heap.push (.suspended ⟨term,environment⟩)).size extended ∧
      HeapRealizes extended (heap.push (.suspended ⟨term,environment⟩)) ∧
      (∀ address, address < heap.size → meaning address = extended address) ∧
      extended heap.size = closeTerm meaning environment term := by
  let source := closeTerm meaning environment term
  let extended := extendMeaning meaning heap.size source
  have same : ∀ address, address < heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended heap.size = source := by simp [extended,extendMeaning]
  have closed := closeTerm_scoped names captures scope
  refine ⟨extended,?_,?_,same,fresh⟩
  · intro address allocated
    by_cases eq : address = heap.size
    · subst address; simpa only [fresh] using closed
    · have old : address < heap.size := by simp only [Array.size_push] at allocated; omega
      simpa only [←same address old] using names address old
  · apply heapRealizes_push (heapRealizes_congr validHeap same realizes)
    refine ⟨?_,True.intro⟩
    have originEq := closeTerm_meaning_congr captures scope same
    simpa only [fresh,cellOrigin,closeOrigin,←originEq] using Steps.refl source

inductive PairObject where
  | specification | prototype

def PairObject.term : PairObject → Term → Term → Term
  | .specification, first, second => .specification first second
  | .prototype, first, second => .prototype first second

def PairObject.value : PairObject → Address → Address → RuntimeValue
  | .specification, first, second => .specification first second
  | .prototype, first, second => .prototype first second



def allocationLoop (environment : Environment) (fields : List (String × Term))
    (heap : Array Cell) (prior : List (String × Address)) : Array Cell × List (String × Address) :=
  fields.foldl (fun pair field =>
    (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2)) (heap,prior)

 theorem allocationLoop_accumulator (environment : Environment) (fields : List (String × Term))
    (heap : Array Cell) (prior : List (String × Address)) :
    allocationLoop environment fields heap prior =
      ((allocationLoop environment fields heap []).1,(allocationLoop environment fields heap []).2++prior) := by
  induction fields generalizing heap prior with
  | nil => simp [allocationLoop]
  | cons field fields ih =>
      change allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) ((field.1,heap.size)::prior) =
        ((allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).1,
         (allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).2++prior)
      rw [ih _ ((field.1,heap.size)::prior),ih _ [(field.1,heap.size)]]
      simp [List.append_assoc]

 theorem allocateFields_cons (heap : Array Cell) (environment : Environment) (field : String × Term)
    (fields : List (String × Term)) :
    allocateFields heap environment (field::fields) =
      ((allocateFields (heap.push (.suspended ⟨field.2,environment⟩)) environment fields).1,
       (field.1,heap.size)::(allocateFields (heap.push (.suspended ⟨field.2,environment⟩)) environment fields).2) := by
  change ((allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).1,
    (allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).2.reverse) = _
  rw [allocationLoop_accumulator]
  simp [allocateFields,allocationLoop,List.reverse_append]

/-- Arbitrary lazy record allocation: every generated field name denotes the
original captured computation, in field order, while all old graph meanings
and all source origins are retained. Fields may contain general Fix. -/
 theorem allocateFields_realizes {heap : Array Cell} {meaning : AddressMeaning} {environment : Environment}
    {fields : List (String × Term)} (valid : HeapValid heap) (names : MeaningsScoped heap.size meaning)
    (realizes : HeapRealizes meaning heap) (captures : EnvironmentValid heap.size environment)
    (scopes : ∀ field ∈ fields, Scoped environment.length field.2) :
    ∃ extended : AddressMeaning,
      MeaningsScoped (allocateFields heap environment fields).1.size extended ∧
      HeapRealizes extended (allocateFields heap environment fields).1 ∧
      (∀ address, address < heap.size → meaning address = extended address) ∧
      ((allocateFields heap environment fields).2.map fun field => (field.1,extended field.2)) =
        (fields.map fun field => (field.1,closeTerm meaning environment field.2)) := by
  induction fields generalizing heap meaning with
  | nil => exact ⟨meaning,names,realizes,by intros; rfl,rfl⟩
  | cons field fields ih =>
      have headScope := scopes field (List.mem_cons_self ..)
      have tailScopes : ∀ field ∈ fields, Scoped environment.length field.2 :=
        fun field member => scopes field (List.mem_cons_of_mem _ member)
      obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ := allocateClosure_realizes valid names realizes headScope captures
      have oneValid := heapValid_push valid
        (show CellValid (heap.size+1) (.suspended ⟨field.2,environment⟩) from
          ⟨headScope,environmentValid_mono captures (Nat.le_succ _)⟩)
      have capturesOne : EnvironmentValid (heap.push (.suspended ⟨field.2,environment⟩)).size environment :=
        environmentValid_mono captures (by simp)
      obtain ⟨two,twoNames,twoHeap,twoSame,twoFields⟩ := ih oneValid oneNames oneHeap capturesOne tailScopes
      have same : ∀ address, address < heap.size → meaning address = two address := by
        intro address allocated
        exact (oneSame address allocated).trans (twoSame address (by simpa using Nat.lt_succ_of_lt allocated))
      refine ⟨two,?_,?_,same,?_⟩
      · simpa only [allocateFields_cons] using twoNames
      · simpa only [allocateFields_cons] using twoHeap
      · rw [allocateFields_cons,List.map_cons,twoFields]
        have firstEq : two heap.size = closeTerm meaning environment field.2 := by
          rw [←twoSame heap.size (by simp),oneFresh]
        rw [firstEq,List.map_cons]
        congr 1
        apply List.map_congr_left
        intro f member
        exact Prod.ext rfl (closeTerm_meaning_congr captures (tailScopes f member) oneSame).symm

 theorem closeTerm_record (meaning : AddressMeaning) (environment : Environment) (fields : List (String × Term)) :
    closeTerm meaning environment (.record fields) =
      .record (fields.map fun field => (field.1,closeTerm meaning environment field.2)) := by
  cases environment <;> simp [closeTerm,Term.substitute]





 theorem closeTerm_mixBody {bound : Nat} {meaning : AddressMeaning} {environment : Environment} {lower upper : Term}
    (names : MeaningsScoped bound meaning) (captures : EnvironmentValid bound environment)
    (lowerScope : Scoped environment.length lower) (upperScope : Scoped environment.length upper) :
    closeTerm meaning environment (mixBody lower upper) =
      mixBody (closeTerm meaning environment lower) (closeTerm meaning environment upper) := by
  let sigma := environmentSubstitution meaning environment
  have images : ∀ i, i < environment.length → Scoped 0 (sigma i) := environmentSubstitution_scoped names captures
  have shifted : ∀ term, Scoped environment.length term →
      (term.rename (fun n => n+2)).substitute (liftSubstitution (liftSubstitution sigma)) = term.substitute sigma := by
    intro term scope
    rw [scoped_rename_substitute scope]
    apply scoped_substitution_congr scope
    intro i hi
    simp only [liftSubstitution,
      scoped_rename_identity (images i hi) Nat.succ (by intro j hj; omega)]
  have lowerClosed := closeTerm_scoped names captures lowerScope
  have upperClosed := closeTerm_scoped names captures upperScope
  rw [closeTerm_eq_substitution (scoped_mixBody lowerScope upperScope)]
  simp only [mixBody,Term.substitute]
  have liftedOne : liftSubstitution (liftSubstitution (environmentSubstitution meaning environment)) 1 = .bound 1 := by
    simp [liftSubstitution,Term.rename]
  have liftedZero : liftSubstitution (liftSubstitution (environmentSubstitution meaning environment)) 0 = .bound 0 := rfl
  simp only [liftedOne,liftedZero]
  change Term.lam (.lam (.app (.app ((upper.rename (fun n => n+2)).substitute (liftSubstitution (liftSubstitution sigma))) (.bound 1))
    (.app (.app ((lower.rename (fun n => n+2)).substitute (liftSubstitution (liftSubstitution sigma))) (.bound 1)) (.bound 0)))) = _
  rw [shifted upper upperScope,shifted lower lowerScope]
  rw [scoped_rename_identity lowerClosed (fun n => n+2) (by intro j hj; omega),
    scoped_rename_identity upperClosed (fun n => n+2) (by intro j hj; omega)]
  simp only [closeTerm_eq_substitution lowerScope,closeTerm_eq_substitution upperScope,sigma]









 theorem closeTerm_weaken {bound : Nat} {meaning extended : AddressMeaning}
    {environment : Environment} {term : Term}
    (captures : EnvironmentValid bound environment) (scope : Scoped environment.length term)
    (same : ∀ address, address < bound → meaning address = extended address) :
    closeTerm extended (bound::environment) (term.rename Nat.succ) = closeTerm meaning environment term := by
  have shifted := scoped_rename scope Nat.succ (environment.length+1) (by intro i hi; omega)
  rw [closeTerm_eq_substitution (by simpa using shifted),closeTerm_eq_substitution scope,
    scoped_rename_substitute scope]
  apply scoped_substitution_congr scope
  intro i hi
  have found : environment[i]? = some environment[i] := getElem?_pos environment i hi
  simp only [environmentSubstitution,List.getElem?_cons_succ,found]
  exact (same _ (captures _ (List.mem_of_getElem? found))).symm

 theorem closeTerm_fix (meaning : AddressMeaning) (environment : Environment) (spec inherited : Term) :
    closeTerm meaning environment (.fix spec inherited) =
      .fix (closeTerm meaning environment spec) (closeTerm meaning environment inherited) := by
  cases environment <;> simp only [closeTerm,Term.substitute]











/-- Running and finished controls have a source focus. Faults and blackholes
are retained operational outcomes and are deliberately not source values. -/
def ResultControl : Control → Prop
  | .evaluate _ _ | .enter _ | .returned _ | .complete _ => True
  -- A yield is not a pure result: it is a whole-program step taken only by a
  -- resume, so (like a fault) it never appears on a terminating pure trace.
  | .refused _ | .blackhole _ | .yielded _ => False

/-- Actual thunk birth provenance: ordinary captures precede their address;
the sole same-address capture is the exact body installed by tied Fix. Cached
RESULT edges may point forward; the permanent SOURCE origin obeys this law. -/
def OriginBorn (address : Address) (origin : Closure) : Prop :=
  EnvironmentValid address origin.environment ∨
    ∃ (spec inherited : Term) (captured : Environment),
      origin.environment = address::captured ∧ EnvironmentValid address captured ∧
      origin.term = .app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ)

def HeapOriginsBorn (heap : Array Cell) : Prop :=
  ∀ address cell, heap[address]? = some cell → OriginBorn address (cellOrigin cell)

/-- A tied Fix origin contains the permanent source name as a proper subterm.
Thus its unfolding cannot be a cost-neutral suspended pointer alias. -/
 theorem tiedOrigin_name_proper (meaning : AddressMeaning) (address : Address)
    (spec inherited : Term) (captured : Environment) :
    sizeOf (meaning address) < sizeOf (closeOrigin meaning
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),address::captured⟩) := by
  simp only [closeOrigin,closeTerm,Term.substitute,environmentSubstitution,List.getElem?_cons_zero]
  simp only [Term.app.sizeOf_spec]
  omega

/-- Every represented born thunk demand decreases either the source cost or
the lexical capture bound. Actual Fix sharing belongs to the strict-cost arm;
ordinary suspended aliases belong to the older-address arm. -/
 theorem originBorn_demand_descent {meaning : AddressMeaning} {address : Address} {origin : Closure}
    {result : Term} {cost : Nat} (born : OriginBorn address origin)
    (originSteps : Steps (meaning address) (closeOrigin meaning origin))
    (derivation : SourceDerivation (meaning address) result cost) :
    EnvironmentValid address origin.environment ∨
      ∃ smaller, SourceDerivation (closeOrigin meaning origin) result smaller ∧ smaller < cost := by
  rcases born with ordinary | ⟨spec,inherited,captured,environmentEq,captures,termEq⟩
  · exact Or.inl ordinary
  · right
    apply sourceSteps_derivation_strict originSteps _ derivation
    intro equal
    have proper := tiedOrigin_name_proper meaning address spec inherited captured
    have originEq : origin =
        ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),address::captured⟩ := by
      cases origin
      simp_all
    rw [← originEq,← equal] at proper
    exact Nat.lt_irrefl _ proper

 theorem heapOriginsBorn_sameSize {before after : Array Cell} (born : HeapOriginsBorn before)
    (preserved : PreservesOrigins before after) (size : before.size = after.size) : HeapOriginsBorn after := by
  intro address cell found
  have allocated : address < before.size := by rw [size]; exact (Array.getElem?_eq_some_iff.mp found).1
  have oldFound : before[address]? = some before[address] := Array.getElem?_eq_getElem allocated
  obtain ⟨new,nextFound,originEq⟩ := preserved.2 address _ oldFound
  have eq : new = cell := Option.some.inj (nextFound.symm.trans found)
  subst new
  rw [originEq]
  exact born address _ oldFound

 theorem heapOriginsBorn_set {heap : Array Cell} {address : Address} {old next : Cell}
    (born : HeapOriginsBorn heap) (found : heap[address]? = some old)
    (same : cellOrigin next = cellOrigin old) : HeapOriginsBorn (heap.set! address next) :=
  heapOriginsBorn_sameSize born (preservesOrigins_set found same) (by simp [Array.set!])

 theorem heapOriginsBorn_push {heap : Array Cell} {cell : Cell} (born : HeapOriginsBorn heap)
    (fresh : OriginBorn heap.size (cellOrigin cell)) : HeapOriginsBorn (heap.push cell) := by
  intro address other found
  by_cases eq : address = heap.size
  · subst address; simp at found; subst other; exact fresh
  · apply born address other
    simpa [Array.getElem?_push,eq] using found

 theorem heapOriginsBorn_suspend {heap : Array Cell} {term : Term} {environment : Environment}
    (born : HeapOriginsBorn heap) (captures : EnvironmentValid heap.size environment) :
    HeapOriginsBorn (heap.push (.suspended ⟨term,environment⟩)) :=
  heapOriginsBorn_push born (Or.inl captures)

 theorem heapOriginsBorn_fix {heap : Array Cell} {spec inherited : Term} {environment : Environment}
    (born : HeapOriginsBorn heap) (captures : EnvironmentValid heap.size environment) :
    HeapOriginsBorn (heap.push (.suspended
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),heap.size::environment⟩)) :=
  heapOriginsBorn_push born (Or.inr ⟨spec,inherited,environment,rfl,captures,rfl⟩)

 theorem allocateFields_originsBorn {heap : Array Cell} {environment : Environment} {fields : List (String × Term)}
    (born : HeapOriginsBorn heap) (captures : EnvironmentValid heap.size environment) :
    HeapOriginsBorn (allocateFields heap environment fields).1 := by
  induction fields generalizing heap with
  | nil => exact born
  | cons field fields ih =>
      rw [allocateFields_cons]
      exact ih (heapOriginsBorn_suspend born captures) (environmentValid_mono captures (by simp))

set_option maxHeartbeats 800000 in
/-- Birth provenance is preserved by EVERY real transition. It permits tied
Fix and sharing, while excluding arbitrary fabricated cyclic suspended aliases. -/
 theorem stepRaw_originsBorn {state : State} (lexical : LexicalInvariant state)
    (born : HeapOriginsBorn state.heap) : HeapOriginsBorn (stepRaw state).heap := by
  have headValid : ∀ frame rest, state.stack = frame::rest → FrameValid state.heap.size frame := by
    intro frame rest eq
    exact lexical.2.2 frame (eq ▸ List.mem_cons_self)
  have controlValid := lexical.2.1
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals try (have frameValid := headValid _ _ (by assumption))
  all_goals simp_all only [ControlValid,ClosureValid,FrameValid]
  all_goals try (have captures := controlValid.2)
  all_goals try (have frameCaptures := frameValid.2)
  all_goals try (have extensionCaptures := frameValid.1)
  all_goals solve
    | exact born
    | apply heapOriginsBorn_set born; assumption; rfl
    | apply heapOriginsBorn_suspend born; assumption
    | apply heapOriginsBorn_fix born; assumption
    | apply allocateFields_originsBorn born; assumption
    | apply heapOriginsBorn_suspend (heapOriginsBorn_suspend born (by assumption));
      exact environmentValid_mono (by assumption) (by simp)
    | apply heapOriginsBorn_push born; left; intro address member; simp [cellOrigin] at member
    | apply heapOriginsBorn_suspend born; intro address member; simp at member; subst member; assumption

 theorem initial_originsBorn (source : Term) : HeapOriginsBorn (initial source).heap := by
  intro address cell found
  simp [initial] at found

 theorem reachable_originsBorn {source : Term} {state : State} (closed : Scoped 0 source)
    (reachable : Reachable (initial source) state) : HeapOriginsBorn state.heap := by
  induction reachable with
  | start => exact initial_originsBorn source
  | next path ih => exact stepRaw_originsBorn (reachable_lexicalInvariant closed path) ih


/-- A graph representation at a specified permanent source assignment. This
interface retains address-name identity for reachability and update budgets. -/
def GraphRepresentsBy (meaning : AddressMeaning) (state : State) (source : Term) : Prop :=
  LexicalInvariant state ∧ BusyInvariant state ∧ FinalStackInvariant state ∧
    MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
    ∃ residual, controlMeaning meaning state.control = some residual ∧
      StackRealizes meaning source residual state.stack

def SourceNamesAgree (before : State) (meaning next : AddressMeaning) : Prop :=
  ∀ address, address < before.heap.size → meaning address = next address

 theorem graphBy_graph {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) : GraphRepresents state source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  exact ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩

 theorem graphBy_initializes {source : Term} (closed : Scoped 0 source) :
    GraphRepresentsBy (fun _ => .bound 0) (initial source) source := by
  refine ⟨initial_lexicalInvariant closed,initial_busyInvariant source,initial_finalStackInvariant source,?_,?_,source,rfl,Steps.refl _⟩
  · intro address allocated; simp [initial] at allocated
  · intro address cell found; simp [initial] at found


/-- The actual semantic transition consumes a continuation prefix and one
independent source reduction; remaining heap names retain their prefix. -/
def SourceDispatch (meaning next : AddressMeaning) (state : State) : Prop :=
  ∃ consumed before after,
    controlMeaning meaning state.control = some before ∧
    controlMeaning next (stepRaw state).control = some after ∧
    state.stack = consumed ++ (stepRaw state).stack ∧
    Step (stackMeaning meaning consumed before) after

 theorem graph_evaluate_context_names {meaning : AddressMeaning} {state : State} {source hole : Term} {context : DemandContext} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (context.term hole) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have scope : Scoped environment.length (context.term hole) := by
    have valid := lexical.2.1
    rw [evaluate] at valid
    exact valid.1
  simp [controlMeaning,evaluate] at control
  subst focus
  have dispatched := demandContext_dispatch evaluate
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment hole,?_,?_⟩
  · simpa only [dispatched] using names
  · simpa only [dispatched] using heap
  · simp only [dispatched,controlMeaning]
  · rw [demandContext_closes context meaning environment hole scope] at stack
    cases context <;> simpa only [dispatched,DemandContext.frame,StackRealizes] using stack

 theorem graph_evaluate_bound_names {meaning : AddressMeaning} {state : State} {source : Term} {environment : Environment} {index address : Nat}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.bound index) environment)
    (found : environment[index]? = some address) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have closes : closeTerm meaning environment (.bound index) = meaning address := by
    cases environment with
    | nil => simp at found
    | cons _ _ => simp [closeTerm,Term.substitute,environmentSubstitution,found]
  simp [controlMeaning,evaluate,closes] at control
  subst focus
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,meaning address,?_,?_⟩
  · simpa [stepRaw,evaluate,found] using names
  · simpa [stepRaw,evaluate,found] using heap
  · simp [stepRaw,evaluate,found,controlMeaning]
  · simpa [stepRaw,evaluate,found] using stack

 theorem graph_evaluate_immediate_names {meaning : AddressMeaning} {state : State} {source : Term} {immediate : ImmediateValue} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate immediate.term environment) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have denotes : valueMeaning meaning (immediate.runtime environment) = closeTerm meaning environment immediate.term := by
    cases immediate <;> cases environment <;> simp [ImmediateValue.term,ImmediateValue.runtime,valueMeaning,closeTerm,Term.substitute]
  simp [controlMeaning,evaluate] at control
  subst focus
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning meaning (immediate.runtime environment),?_,?_⟩
  · cases immediate <;> simpa [stepRaw,evaluate,ImmediateValue.term] using names
  · cases immediate <;> simpa [stepRaw,evaluate,ImmediateValue.term] using heap
  · cases immediate <;> simp [stepRaw,evaluate,ImmediateValue.term,ImmediateValue.runtime,controlMeaning]
  · rw [denotes]
    cases immediate <;> simpa [stepRaw,evaluate,ImmediateValue.term] using stack

 theorem graph_object_access_execution {meaning : AddressMeaning} {state : State} {source : Term} {access : ObjectAccess} {first second : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (access.value first second))
    (head : state.stack = access.frame::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source
      (frameMeaning meaning access.frame (valueMeaning meaning (access.value first second))) rest := by
    cases access <;> simpa [head,ObjectAccess.frame,StackRealizes] using stack
  have reduce : Step (frameMeaning meaning access.frame (valueMeaning meaning (access.value first second)))
      (meaning (access.address first second)) := by
    cases access with
    | reflect => exact Step.reflectPrototype _ _
    | metadata => exact Step.metadataSpecification _ _
    | project => exact Step.projectPrototype _ _
  have advanced := stackRealizes_steps before (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,meaning (access.address first second),?_,?_⟩
    · cases access <;> simpa [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value] using names
    · cases access <;> simpa [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value] using heap
    · cases access <;> simp [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value,ObjectAccess.address,controlMeaning]
    · cases access <;> simpa [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value] using advanced
  · refine ⟨[access.frame],valueMeaning meaning (access.value first second),meaning (access.address first second),?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · cases access <;> simp [stepRaw,returned,head,controlMeaning,ObjectAccess.frame,ObjectAccess.value,ObjectAccess.address]
    · cases access <;> simp [stepRaw,returned,head,controlMeaning,ObjectAccess.frame,ObjectAccess.value,ObjectAccess.address]
    · exact reduce

 theorem graph_object_access_names {meaning : AddressMeaning} {state : State} {source : Term} {access : ObjectAccess} {first second : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (access.value first second))
    (head : state.stack = access.frame::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_object_access_execution represented returned head
  exact ⟨next,same,current⟩

 theorem graph_specification_call_names {meaning : AddressMeaning} {state : State} {source argument : Term} {environment : Environment}
    {descriptor extension : Address} {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.specification descriptor extension))
    (head : state.stack = .argument argument environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source
      (.app (.specification (meaning descriptor) (meaning extension)) (closeTerm meaning environment argument)) rest := by
    simpa only [head,StackRealizes,frameMeaning,valueMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next (Step.applySpecification _ _ _) (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,meaning extension,?_,?_⟩
  · simpa [stepRaw,returned,head] using names
  · simpa [stepRaw,returned,head] using heap
  · simp [stepRaw,returned,head,controlMeaning]
  · simpa [stepRaw,returned,head,StackRealizes,frameMeaning] using advanced

 theorem graph_primitive_return_names {meaning : AddressMeaning} {state : State} {source result : Term} {primitive : Primitive}
    {left right next : RuntimeValue} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned right)
    (head : state.stack = .binaryRight primitive left::rest)
    (dispatch : (valueTerm left).bind (fun l => (valueTerm right).bind (primitiveResult primitive l)) = some result)
    (scalar : scalarValue result = some next) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  obtain ⟨leftTerm,leftFound,rightResult⟩ := Option.bind_eq_some_iff.mp dispatch
  obtain ⟨rightTerm,rightFound,primitiveFound⟩ := Option.bind_eq_some_iff.mp rightResult
  have reduce : Step (.binary primitive (valueMeaning meaning left) (valueMeaning meaning right)) (valueMeaning meaning next) := by
    have rule := Step.primitive primitive _ _ result (valueMeaning_value meaning left) (valueMeaning_value meaning right)
      (by simpa only [valueTerm_meaning leftFound meaning,valueTerm_meaning rightFound meaning] using primitiveFound)
    simpa only [scalarValue_meaning scalar meaning] using rule
  have before : StackRealizes meaning source (.binary primitive (valueMeaning meaning left) (valueMeaning meaning right)) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning meaning next,?_,?_⟩
  · simpa [stepRaw,returned,head,dispatch,scalar] using names
  · simpa [stepRaw,returned,head,dispatch,scalar] using heap
  · simp [stepRaw,returned,head,dispatch,scalar,controlMeaning]
  · simpa [stepRaw,returned,head,dispatch,scalar] using advanced

 theorem graph_enter_suspended_names {meaning : AddressMeaning} {state : State} {source : Term} {address : Nat} {origin : Closure}
    (represented : GraphRepresentsBy meaning state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.suspended origin)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,enter] at control
  subst focus
  have oldCell := heap address _ found
  have newCell : CellRealizes meaning address (.evaluating origin) := oldCell
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,
    closeOrigin meaning origin,?_,?_⟩
  · simpa [stepRaw,enter,found] using names
  · simpa [stepRaw,enter,found] using heapRealizes_set heap newCell
  · simp [stepRaw,enter,found,controlMeaning,closeOrigin]
  · simpa [stepRaw,enter,found,StackRealizes] using And.intro oldCell.1 stack

 theorem graph_cache_update_names {meaning : AddressMeaning} {state : State} {source : Term} {address : Nat}
    {rest : List Frame} {value : RuntimeValue}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned value)
    (update : state.stack = .update address::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  obtain ⟨origin,found⟩ := busy_update_exists busy update
  simp [controlMeaning,returned] at control
  subst focus
  have segments : StackRealizes meaning source (valueMeaning meaning value) (.update address::rest) :=
    update ▸ stack
  have cached := cachedCell_realizes heap found segments
  have consumers := stackRealizes_steps segments.2 segments.1
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,
    valueMeaning meaning value,?_,?_⟩
  · simpa [stepRaw,returned,update,found] using names
  · simpa [stepRaw,returned,update,found] using heapRealizes_set heap cached
  · simp [stepRaw,returned,update,found,controlMeaning]
  · simpa [stepRaw,returned,update,found] using consumers

 theorem graph_enter_cached_names {meaning : AddressMeaning} {state : State} {source : Term} {address : Nat}
    {origin : Closure} {value : RuntimeValue}
    (represented : GraphRepresentsBy meaning state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.cached origin value)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,enter] at control
  subst focus
  have cached := heap address _ found
  have consumed := stackRealizes_steps stack cached.2.1
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning meaning value,?_,?_⟩
  · simpa [stepRaw,enter,found] using names
  · simpa [stepRaw,enter,found] using heap
  · simp [stepRaw,enter,found,controlMeaning]
  · simpa [stepRaw,enter,found] using consumed

 theorem graph_evaluate_pair_names {meaning : AddressMeaning} {state : State} {source first second : Term} {environment : Environment}
    {kind : PairObject} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (kind.term first second) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨kind.term first second,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length first ∧ Scoped environment.length second := by
    cases kind <;> simpa [PairObject.term] using valid.1
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes lexical.1 names heap scopes.1 valid.2
  have oneValid := heapValid_push lexical.1
    (show CellValid (state.heap.size+1) (.suspended ⟨first,environment⟩) from
      ⟨scopes.1,environmentValid_mono valid.2 (Nat.le_succ _)⟩)
  have capturesOne : EnvironmentValid (state.heap.push (.suspended ⟨first,environment⟩)).size environment :=
    environmentValid_mono valid.2 (by simp)
  obtain ⟨two,twoNames,twoHeap,twoSame,twoFresh⟩ :=
    allocateClosure_realizes oneValid oneNames oneHeap scopes.2 capturesOne
  have same : ∀ address, address < state.heap.size → meaning address = two address := by
    intro address allocated
    exact (oneSame address allocated).trans (twoSame address (by simpa using Nat.lt_succ_of_lt allocated))
  have firstEq : two state.heap.size = closeTerm meaning environment first := by
    rw [←twoSame state.heap.size (by simp),oneFresh]
  have secondEq : two (state.heap.size+1) = closeTerm meaning environment second := by
    have closeEq := closeTerm_meaning_congr valid.2 scopes.2 oneSame
    simpa only [Array.size_push,←closeEq] using twoFresh
  have sourceEq : valueMeaning two (kind.value state.heap.size (state.heap.size+1)) =
      closeTerm meaning environment (kind.term first second) := by
    cases kind <;> cases environment <;> simp [PairObject.term,PairObject.value,valueMeaning,firstEq,secondEq,closeTerm,Term.substitute]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  refine ⟨two,same,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,
    valueMeaning two (kind.value state.heap.size (state.heap.size+1)),?_,?_⟩
  · cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using twoNames
  · cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using twoHeap
  · cases kind <;> simp [stepRaw,evaluate,PairObject.term,PairObject.value,controlMeaning]
  · rw [sourceEq]
    cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using consumers

 theorem graph_evaluate_record_names {meaning : AddressMeaning} {state : State} {source : Term} {fields : List (String × Term)} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.record fields) environment) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.record fields,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : ∀ field ∈ fields, Scoped environment.length field.2 := by simpa using valid.1
  obtain ⟨extended,newNames,newHeap,same,fieldsEq⟩ := allocateFields_realizes lexical.1 names heap valid.2 scopes
  have denotes : valueMeaning extended (.record (allocateFields state.heap environment fields).2) =
      closeTerm meaning environment (.record fields) := by simp only [valueMeaning,fieldsEq,closeTerm_record]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  refine ⟨extended,same,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,
    valueMeaning extended (.record (allocateFields state.heap environment fields).2),?_,?_⟩
  · simpa [stepRaw,evaluate] using newNames
  · simpa [stepRaw,evaluate] using newHeap
  · simp [stepRaw,evaluate,controlMeaning]
  · rw [denotes]
    simpa [stepRaw,evaluate] using consumers

 theorem graph_field_return_execution {meaning : AddressMeaning} {state : State} {source : Term} {fields : List (String × Address)}
    {name key : String} {address : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.record fields))
    (head : state.stack = .field name::rest)
    (found : fields.find? (fun field => field.1 == name) = some (key,address)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have keyEq : key = name := by simpa using List.find?_some found
  subst key
  have sourceFound : (fields.map fun field => (field.1,meaning field.2)).find? (fun field => field.1 == name) = some (name,meaning address) := by
    simp [List.find?_map,Function.comp_def,found]
  have reduce := Step.field _ name (meaning address) sourceFound
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source (.get (valueMeaning meaning (.record fields)) name) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,meaning address,?_,?_⟩
    · simpa [stepRaw,returned,head,found] using names
    · simpa [stepRaw,returned,head,found] using heap
    · simp [stepRaw,returned,head,found,controlMeaning]
    · simpa [stepRaw,returned,head,found] using advanced
  · refine ⟨[.field name],valueMeaning meaning (.record fields),meaning address,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · simp [stepRaw,returned,head,controlMeaning,found]
    · simp [stepRaw,returned,head,controlMeaning,found]
    · exact reduce

 theorem graph_field_return_names {meaning : AddressMeaning} {state : State} {source : Term} {fields : List (String × Address)}
    {name key : String} {address : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.record fields))
    (head : state.stack = .field name::rest)
    (found : fields.find? (fun field => field.1 == name) = some (key,address)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_field_return_execution represented returned head found
  exact ⟨next,same,current⟩

 theorem graph_evaluate_mix_execution {meaning : AddressMeaning} {state : State} {source lower upper : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.mix lower upper,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length lower ∧ Scoped environment.length upper := by simpa using valid.1
  have reduce : Step (closeTerm meaning environment (.mix lower upper)) (closeTerm meaning environment (mixBody lower upper)) := by
    rw [closeTerm_mixBody names valid.2 scopes.1 scopes.2]
    have rule := Step.mix (closeTerm meaning environment lower) (closeTerm meaning environment upper)
    cases environment <;> simpa [closeTerm,Term.substitute] using rule
  simp [controlMeaning,evaluate] at control
  subst focus
  have advanced := stackRealizes_steps stack (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment (mixBody lower upper),?_,?_⟩
    · simpa [stepRaw,evaluate] using names
    · simpa [stepRaw,evaluate] using heap
    · simp [stepRaw,evaluate,controlMeaning]
    · simpa [stepRaw,evaluate] using advanced
  · refine ⟨[],closeTerm meaning environment (.mix lower upper),closeTerm meaning environment (mixBody lower upper),?_,?_,?_,?_⟩
    · simp [controlMeaning,evaluate]
    · simp [stepRaw,evaluate,controlMeaning]
    · simp [stepRaw,evaluate,controlMeaning]
    · exact reduce

 theorem graph_evaluate_mix_names {meaning : AddressMeaning} {state : State} {source lower upper : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_evaluate_mix_execution represented evaluate
  exact ⟨next,same,current⟩

 theorem graph_condition_zero_execution {meaning : AddressMeaning} {state : State} {source zero body : Term} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.natural 0))
    (head : state.stack = .condition zero body environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned,valueMeaning] at control
  subst focus
  have before : StackRealizes meaning source
      (.ifZero (.nat 0) (closeTerm meaning environment zero)
        (body.substitute (liftSubstitution (environmentSubstitution meaning environment)))) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next (Step.zero _ _) (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment zero,?_,?_⟩
    · simpa [stepRaw,returned,head] using names
    · simpa [stepRaw,returned,head] using heap
    · simp [stepRaw,returned,head,controlMeaning]
    · simpa [stepRaw,returned,head] using advanced
  · refine ⟨[.condition zero body environment],.nat 0,closeTerm meaning environment zero,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · exact Step.zero _ _

 theorem graph_condition_zero_names {meaning : AddressMeaning} {state : State} {source zero body : Term} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.natural 0))
    (head : state.stack = .condition zero body environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_condition_zero_execution represented returned head
  exact ⟨next,same,current⟩

 theorem graph_condition_successor_execution {meaning : AddressMeaning} {state : State} {source zero body : Term} {environment : Environment}
    {number : Nat} {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.natural (number+1)))
    (head : state.stack = .condition zero body environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have frameValid : FrameValid state.heap.size (.condition zero body environment) :=
    lexical.2.2 _ (head ▸ List.mem_cons_self ..)
  have restValid : ∀ frame ∈ rest, FrameValid state.heap.size frame := by
    intro frame member
    apply lexical.2.2 frame
    rw [head]
    exact List.mem_cons_of_mem _ member
  let extended := extendMeaning meaning state.heap.size (.nat number)
  have same : ∀ address, address < state.heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended state.heap.size = .nat number := by simp [extended,extendMeaning]
  have newNames : MeaningsScoped (state.heap.size+1) extended := by
    intro address allocated
    by_cases eq : address = state.heap.size
    · subst address; rw [fresh]; exact .natural _
    · have old : address < state.heap.size := by omega
      simpa only [←same address old] using names address old
  have newCell : CellRealizes extended state.heap.size (.cached ⟨.nat number,[]⟩ (.natural number)) := by
    simp only [CellRealizes,cellOrigin,closeOrigin,closeTerm,valueMeaning,fresh]
    exact ⟨Steps.refl _,Steps.refl _,Value.natural _⟩
  have newHeap := heapRealizes_push (heapRealizes_congr lexical.1 same heap) newCell
  have reduce : Step
      (.ifZero (.nat (number+1)) (closeTerm meaning environment zero)
        (body.substitute (liftSubstitution (environmentSubstitution meaning environment))))
      (closeTerm extended (state.heap.size::environment) body) := by
    rw [←closeTerm_beta names frameValid.1 frameValid.2.2 (Scoped.natural number) same fresh]
    exact Step.successor _ _ _
  simp [controlMeaning,returned,valueMeaning] at control
  subst focus
  have before : StackRealizes meaning source
      (.ifZero (.nat (number+1)) (closeTerm meaning environment zero)
        (body.substitute (liftSubstitution (environmentSubstitution meaning environment)))) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have consumers := stackRealizes_congr restValid same before
  have advanced := stackRealizes_steps consumers (Steps.next reduce (Steps.refl _))
  refine ⟨extended,same,?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,closeTerm extended (state.heap.size::environment) body,?_,?_⟩
    · simpa [stepRaw,returned,head] using newNames
    · simpa [stepRaw,returned,head] using newHeap
    · simp [stepRaw,returned,head,controlMeaning]
    · simpa [stepRaw,returned,head] using advanced
  · refine ⟨[.condition zero body environment],.nat (number+1),closeTerm extended (state.heap.size::environment) body,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · exact reduce

 theorem graph_condition_successor_names {meaning : AddressMeaning} {state : State} {source zero body : Term} {environment : Environment}
    {number : Nat} {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.natural (number+1)))
    (head : state.stack = .condition zero body environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_condition_successor_execution represented returned head
  exact ⟨next,same,current⟩

 theorem graph_extend_record_names {meaning : AddressMeaning} {state : State} {source : Term} {inherited : List (String × Address)}
    {fields : List (String × Term)} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.record inherited))
    (head : state.stack = .extend fields environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have validFrame : FrameValid state.heap.size (.extend fields environment) :=
    lexical.2.2 _ (head ▸ List.mem_cons_self ..)
  have validInherited : RuntimeValueValid state.heap.size (.record inherited) := by
    simpa only [returned,ControlValid] using lexical.2.1
  have restValid : ∀ frame ∈ rest, FrameValid state.heap.size frame := by
    intro frame member
    apply lexical.2.2 frame
    rw [head]
    exact List.mem_cons_of_mem _ member
  obtain ⟨extended,newNames,newHeap,same,fieldsEq⟩ :=
    allocateFields_realizes lexical.1 names heap validFrame.1 validFrame.2
  let retained := inherited.filter (fun prior => !(fields.any fun field => field.1 == prior.1))
  let newValue := RuntimeValue.record ((allocateFields state.heap environment fields).2++retained)
  have inheritedEq : inherited.map (fun field => (field.1,extended field.2)) =
      inherited.map (fun field => (field.1,meaning field.2)) := by
    apply List.map_congr_left
    intro field member
    exact Prod.ext rfl (same _ (validInherited field member)).symm
  have denotes : valueMeaning extended newValue =
      .record (extendFields (inherited.map fun field => (field.1,meaning field.2))
        (fields.map fun field => (field.1,closeTerm meaning environment field.2))) := by
    simp only [newValue,valueMeaning,List.map_append,fieldsEq,extendFields]
    congr 2
    have filtered := List.filter_map (f := fun field : String × Address => (field.1,extended field.2))
      (p := fun prior => !((fields.map fun field => (field.1,closeTerm meaning environment field.2)).any fun field => field.1 == prior.1))
      (l := inherited)
    simpa [retained,List.any_map,Function.comp_def,inheritedEq] using filtered.symm
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source
      (.extend (valueMeaning meaning (.record inherited))
        (fields.map fun field => (field.1,closeTerm meaning environment field.2))) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have consumers := stackRealizes_congr restValid same before
  have reduce : Step
      (.extend (valueMeaning meaning (.record inherited))
        (fields.map fun field => (field.1,closeTerm meaning environment field.2))) (valueMeaning extended newValue) := by
    rw [denotes]
    exact Step.extendRecord _ _
  have advanced := stackRealizes_steps consumers (Steps.next reduce (Steps.refl _))
  refine ⟨extended,same,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning extended newValue,?_,?_⟩
  · simpa [stepRaw,returned,head] using newNames
  · simpa [stepRaw,returned,head] using newHeap
  · simp [stepRaw,returned,head,controlMeaning,newValue,retained]
  · simpa [stepRaw,returned,head] using advanced

 theorem graph_evaluate_fix_names {meaning : AddressMeaning} {state : State} {source spec inherited : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.fix spec inherited) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.fix spec inherited,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length spec ∧ Scoped environment.length inherited := by
    simpa using valid.1
  let fixSource := closeTerm meaning environment (.fix spec inherited)
  let extended := extendMeaning meaning state.heap.size fixSource
  have same : ∀ address, address < state.heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended state.heap.size = fixSource := by simp [extended,extendMeaning]
  have closed : Scoped 0 fixSource := closeTerm_scoped names valid.2 valid.1
  have newNames : MeaningsScoped (state.heap.size+1) extended := by
    intro address allocated
    by_cases eq : address = state.heap.size
    · subst address; simpa only [fresh] using closed
    · have old : address < state.heap.size := by omega
      simpa only [←same address old] using names address old
  have newHeap := heapRealizes_congr lexical.1 same heap
  let body := Term.app (Term.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ)
  have originEq : closeTerm extended (state.heap.size::environment) body =
      .app (.app (closeTerm meaning environment spec) fixSource) (closeTerm meaning environment inherited) := by
    simp only [body,closeTerm_app,closeTerm_weaken valid.2 scopes.1 same,
      closeTerm_weaken valid.2 scopes.2 same]
    simp [closeTerm,Term.substitute,environmentSubstitution,fresh]
  have newCell : CellRealizes extended state.heap.size (.suspended ⟨body,state.heap.size::environment⟩) := by
    refine ⟨?_,True.intro⟩
    simp only [cellOrigin,closeOrigin,fresh,originEq]
    simpa only [fixSource,closeTerm_fix] using
      Steps.next (Step.fix (closeTerm meaning environment spec) (closeTerm meaning environment inherited)) (Steps.refl _)
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  refine ⟨extended,same,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,fixSource,?_,?_⟩
  · simpa [stepRaw,evaluate] using newNames
  · simpa [stepRaw,evaluate,body] using heapRealizes_push newHeap newCell
  · simp [stepRaw,evaluate,controlMeaning,fresh]
  · simpa [stepRaw,evaluate,fixSource] using consumers

 theorem graph_closure_call_execution {meaning : AddressMeaning} {state : State} {source body argument : Term}
    {captured environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.closure body captured))
    (head : state.stack = .argument argument environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have closureValid : RuntimeValueValid state.heap.size (.closure body captured) := by
    simpa only [returned,ControlValid] using lexical.2.1
  have argumentValid : ClosureValid state.heap.size ⟨argument,environment⟩ := by
    have hv := lexical.2.2 (.argument argument environment) (head ▸ List.mem_cons_self ..)
    exact hv
  have restValid : ∀ frame ∈ rest, FrameValid state.heap.size frame := by
    intro frame member
    apply lexical.2.2 frame
    rw [head]
    exact List.mem_cons_of_mem _ member
  let argumentSource := closeTerm meaning environment argument
  let extended := extendMeaning meaning state.heap.size argumentSource
  have same : ∀ address, address < state.heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended state.heap.size = argumentSource := by simp [extended,extendMeaning]
  have argClosed : Scoped 0 argumentSource := closeTerm_scoped names argumentValid.2 argumentValid.1
  have newNames : MeaningsScoped (state.heap.size+1) extended := by
    intro address allocated
    by_cases eq : address = state.heap.size
    · subst address; simpa only [fresh] using argClosed
    · have old : address < state.heap.size := by omega
      simpa only [←same address old] using names address old
  have newHeap := heapRealizes_congr lexical.1 same heap
  have newCell : CellRealizes extended state.heap.size (.suspended ⟨argument,environment⟩) := by
    refine ⟨?_,True.intro⟩
    have argSame := closeTerm_meaning_congr argumentValid.2 argumentValid.1 same
    simpa only [fresh,cellOrigin,closeOrigin,←argSame] using Steps.refl argumentSource
  have beta : Step (.app (valueMeaning meaning (.closure body captured)) argumentSource)
      (closeTerm extended (state.heap.size::captured) body) := by
    simp only [valueMeaning,closeTerm_lambda closureValid.1]
    rw [←closeTerm_beta names closureValid.2 closureValid.1 argClosed same fresh]
    exact Step.beta _ _
  simp [returned,controlMeaning] at control
  subst focus
  have consumers : StackRealizes meaning source
      (.app (valueMeaning meaning (.closure body captured)) argumentSource) rest := by
    simpa only [head,StackRealizes,frameMeaning,argumentSource] using stack
  have newConsumers := stackRealizes_congr restValid same consumers
  have advanced := stackRealizes_steps newConsumers (Steps.next beta (Steps.refl _))
  refine ⟨extended,same,?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,
      closeTerm extended (state.heap.size::captured) body,?_,?_⟩
    · simpa [stepRaw,returned,head] using newNames
    · simpa [stepRaw,returned,head] using heapRealizes_push newHeap newCell
    · simp [stepRaw,returned,head,controlMeaning]
    · simpa [stepRaw,returned,head] using advanced
  · refine ⟨[.argument argument environment],valueMeaning meaning (.closure body captured),closeTerm extended (state.heap.size::captured) body,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · simp [stepRaw,returned,head,controlMeaning]
    · exact beta

 theorem graph_closure_call_names {meaning : AddressMeaning} {state : State} {source body argument : Term}
    {captured environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.closure body captured))
    (head : state.stack = .argument argument environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_closure_call_execution represented returned head
  exact ⟨next,same,current⟩

 theorem graph_evaluate_application_names {meaning : AddressMeaning} {state : State} {source function argument : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.app function argument) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,evaluate] at control
  subst focus
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment function,?_,?_⟩
  · simpa [stepRaw,evaluate] using names
  · simpa [stepRaw,evaluate] using heap
  · simp [stepRaw,evaluate,controlMeaning]
  · simpa [stepRaw,evaluate,StackRealizes,frameMeaning,closeTerm_app] using stack

 theorem graph_binary_left_return_names {meaning : AddressMeaning} {state : State} {source right : Term} {primitive : Primitive}
    {environment : Environment} {rest : List Frame} {value : RuntimeValue}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned value)
    (head : state.stack = .binaryLeft primitive right environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment right,?_,?_⟩
  · simpa [stepRaw,returned,head] using names
  · simpa [stepRaw,returned,head] using heap
  · simp [stepRaw,returned,head,controlMeaning]
  · simpa [stepRaw,returned,head,StackRealizes,frameMeaning] using stack

 theorem graph_complete_return_names {meaning : AddressMeaning} {state : State} {source : Term} {value : RuntimeValue}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned value)
    (empty : state.stack = []) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  refine ⟨meaning,(fun _ _ => rfl),stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning meaning value,?_,?_⟩
  · simpa [stepRaw,returned,empty] using names
  · simpa [stepRaw,returned,empty] using heap
  · simp [stepRaw,returned,empty,controlMeaning]
  · simpa [stepRaw,returned,empty] using stack

 theorem closeTerm_inject (meaning : AddressMeaning) (environment : Environment) (tag : String) (payload : Term) :
    closeTerm meaning environment (.inject tag payload) = .inject tag (closeTerm meaning environment payload) := by
  cases environment <;> simp [closeTerm,Term.substitute]

/-- Injection allocates exactly one lazy payload thunk; the returned variant
denotes the injected closed payload computation without forcing it. -/
 theorem graph_evaluate_inject_names {meaning : AddressMeaning} {state : State} {source payload : Term}
    {tag : String} {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.inject tag payload) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.inject tag payload,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scope : Scoped environment.length payload := by simpa using valid.1
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes lexical.1 names heap scope valid.2
  have sourceEq : valueMeaning one (.variant tag state.heap.size) =
      closeTerm meaning environment (.inject tag payload) := by
    simp [valueMeaning,oneFresh,closeTerm_inject]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 oneSame stack
  refine ⟨one,oneSame,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning one (.variant tag state.heap.size),?_,?_⟩
  · simpa [stepRaw,evaluate] using oneNames
  · simpa [stepRaw,evaluate] using oneHeap
  · simp [stepRaw,evaluate,controlMeaning]
  · rw [sourceEq]
    simpa [stepRaw,evaluate] using consumers

 theorem find_map_arms (arms : List (String × Term)) (f : Term → Term) (tag : String) :
    (arms.map fun arm => (arm.1,f arm.2)).find? (fun arm => arm.1 == tag) =
      (arms.find? (fun arm => arm.1 == tag)).map (fun arm => (arm.1,f arm.2)) := by
  rw [List.find?_map]
  rfl

 theorem find_arm_label {arms : List (String × Term)} {tag key : String} {body : Term}
    (found : arms.find? (fun arm => arm.1 == tag) = some (key,body)) : key = tag := by
  have holds := List.find?_some found
  simpa using holds

/-- A returned variant selects its first matching arm. The binder is a fresh
indirection cell to the shared payload address, and the transition is exactly
independent source case-of-injection reduction. -/
 theorem graph_case_return_execution {meaning : AddressMeaning} {state : State} {source body : Term}
    {arms : List (String × Term)} {environment : Environment} {tag key : String} {payload : Address}
    {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.variant tag payload))
    (head : state.stack = .case arms environment::rest)
    (found : arms.find? (fun arm => arm.1 == tag) = some (key,body)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have keyEq := find_arm_label found
  subst keyEq
  have frameValid : FrameValid state.heap.size (.case arms environment) :=
    lexical.2.2 _ (head ▸ List.mem_cons_self ..)
  have restValid : ∀ frame ∈ rest, FrameValid state.heap.size frame := by
    intro frame member
    apply lexical.2.2 frame
    rw [head]
    exact List.mem_cons_of_mem _ member
  have payloadValid : payload < state.heap.size := by
    simpa only [returned,ControlValid,RuntimeValueValid] using lexical.2.1
  have bodyScope : Scoped (environment.length+1) body :=
    frameValid.2 _ (List.mem_of_find?_eq_some found)
  have bindingCaptures : EnvironmentValid state.heap.size [payload] := by
    intro address member
    simp at member
    subst member
    exact payloadValid
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes (term := .bound 0) lexical.1 names heap (.bound (by simp)) bindingCaptures
  have freshEq : one state.heap.size = meaning payload := by
    rw [oneFresh]
    simp [closeTerm,Term.substitute,environmentSubstitution]
  let sigma := environmentSubstitution meaning environment
  let closedArms := arms.map fun arm => (arm.1,arm.2.substitute (liftSubstitution sigma))
  have closedFound : closedArms.find? (fun arm => arm.1 == key) =
      some (key,body.substitute (liftSubstitution sigma)) := by
    simp only [closedArms]
    rw [find_map_arms,found]
    rfl
  have reduce : Step (.case (.inject key (meaning payload)) closedArms)
      (closeTerm one (state.heap.size::environment) body) := by
    rw [←closeTerm_beta names frameValid.1 bodyScope (names payload payloadValid) oneSame freshEq]
    exact Step.caseInject _ _ _ _ closedFound
  simp [controlMeaning,returned,valueMeaning] at control
  subst focus
  have before : StackRealizes meaning source (.case (.inject key (meaning payload)) closedArms) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have consumers := stackRealizes_congr restValid oneSame before
  have advanced := stackRealizes_steps consumers (Steps.next reduce (Steps.refl _))
  refine ⟨one,oneSame,?_,?_⟩
  · refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,closeTerm one (state.heap.size::environment) body,?_,?_⟩
    · simpa [stepRaw,returned,head,found] using oneNames
    · simpa [stepRaw,returned,head,found] using oneHeap
    · simp [stepRaw,returned,head,found,controlMeaning]
    · simpa [stepRaw,returned,head,found] using advanced
  · refine ⟨[.case arms environment],.inject key (meaning payload),closeTerm one (state.heap.size::environment) body,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned,valueMeaning]
    · simp [stepRaw,returned,head,found,controlMeaning]
    · simp [stepRaw,returned,head,found]
    · simpa [stackMeaning,frameMeaning] using reduce

 theorem graph_case_return_names {meaning : AddressMeaning} {state : State} {source body : Term}
    {arms : List (String × Term)} {environment : Environment} {tag key : String} {payload : Address}
    {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.variant tag payload))
    (head : state.stack = .case arms environment::rest)
    (found : arms.find? (fun arm => arm.1 == tag) = some (key,body)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_case_return_execution represented returned head found
  exact ⟨next,same,current⟩

/-- A returned Boolean selects exactly one branch; the other stays latent. -/
 theorem graph_ifBool_return_execution {meaning : AddressMeaning} {state : State} {source whenTrue whenFalse : Term}
    {environment : Environment} {rest : List Frame} {value : Bool} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.boolean value))
    (head : state.stack = .ifBool whenTrue whenFalse environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned,valueMeaning] at control
  subst focus
  have before : StackRealizes meaning source
      (.ifBool (.boolean value) (closeTerm meaning environment whenTrue) (closeTerm meaning environment whenFalse)) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  cases value with
  | true =>
    have advanced := stackRealizes_steps before (Steps.next (Step.ifTrue _ _) (Steps.refl _))
    refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
    · refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
        stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment whenTrue,?_,?_⟩
      · simpa [stepRaw,returned,head] using names
      · simpa [stepRaw,returned,head] using heap
      · simp [stepRaw,returned,head,controlMeaning]
      · simpa [stepRaw,returned,head] using advanced
    · refine ⟨[.ifBool whenTrue whenFalse environment],.boolean true,closeTerm meaning environment whenTrue,?_,?_,?_,?_⟩
      · simp [controlMeaning,returned,valueMeaning]
      · simp [stepRaw,returned,head,controlMeaning]
      · simp [stepRaw,returned,head]
      · exact Step.ifTrue _ _
  | false =>
    have advanced := stackRealizes_steps before (Steps.next (Step.ifFalse _ _) (Steps.refl _))
    refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
    · refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
        stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment whenFalse,?_,?_⟩
      · simpa [stepRaw,returned,head] using names
      · simpa [stepRaw,returned,head] using heap
      · simp [stepRaw,returned,head,controlMeaning]
      · simpa [stepRaw,returned,head] using advanced
    · refine ⟨[.ifBool whenTrue whenFalse environment],.boolean false,closeTerm meaning environment whenFalse,?_,?_,?_,?_⟩
      · simp [controlMeaning,returned,valueMeaning]
      · simp [stepRaw,returned,head,controlMeaning]
      · simp [stepRaw,returned,head]
      · exact Step.ifFalse _ _

 theorem graph_ifBool_return_names {meaning : AddressMeaning} {state : State} {source whenTrue whenFalse : Term}
    {environment : Environment} {rest : List Frame} {value : Bool} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.boolean value))
    (head : state.stack = .ifBool whenTrue whenFalse environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_ifBool_return_execution represented returned head
  exact ⟨next,same,current⟩

 theorem closeTerm_perform (meaning : AddressMeaning) (environment : Environment) (plan : Term) :
    closeTerm meaning environment (.perform plan) = .perform (closeTerm meaning environment plan) := by
  cases environment <;> simp [closeTerm,Term.substitute]

 theorem closeTerm_done (meaning : AddressMeaning) (environment : Environment) (value : Term) :
    closeTerm meaning environment (.done value) = .done (closeTerm meaning environment value) := by
  cases environment <;> simp [closeTerm,Term.substitute]

/-- A perform outside every shared cell allocates its plan as one lazy cell and
yields; the yielded control still means the same source redex `perform plan`,
so no source step is claimed or needed. -/
 theorem graph_evaluate_perform_names {meaning : AddressMeaning} {state : State} {source plan : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.perform plan) environment)
    (direct : forcingShared state.stack = false) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.perform plan,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scope : Scoped environment.length plan := by simpa using valid.1
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes lexical.1 names heap scope valid.2
  have sourceEq : Term.perform (one state.heap.size) = closeTerm meaning environment (.perform plan) := by
    simp [oneFresh,closeTerm_perform]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 oneSame stack
  refine ⟨one,oneSame,stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,.perform (one state.heap.size),?_,?_⟩
  · simpa [stepRaw,evaluate,direct] using oneNames
  · simpa [stepRaw,evaluate,direct] using oneHeap
  · simp [stepRaw,evaluate,direct,controlMeaning]
  · rw [sourceEq]
    simpa [stepRaw,evaluate,direct] using consumers

/-- `done` is exactly the independent source reduction `done v → v`. -/
 theorem graph_evaluate_done_execution {meaning : AddressMeaning} {state : State} {source value : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.done value) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have reduce : Step (closeTerm meaning environment (.done value)) (closeTerm meaning environment value) := by
    rw [closeTerm_done]; exact Step.done _
  simp [controlMeaning,evaluate] at control
  subst focus
  have advanced := stackRealizes_steps stack (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  · refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,closeTerm meaning environment value,?_,?_⟩
    · simpa [stepRaw,evaluate] using names
    · simpa [stepRaw,evaluate] using heap
    · simp [stepRaw,evaluate,controlMeaning]
    · simpa [stepRaw,evaluate] using advanced
  · refine ⟨[],closeTerm meaning environment (.done value),closeTerm meaning environment value,?_,?_,?_,?_⟩
    · simp [controlMeaning,evaluate]
    · simp [stepRaw,evaluate,controlMeaning]
    · simp [stepRaw,evaluate,controlMeaning]
    · exact reduce

 theorem graph_evaluate_done_names {meaning : AddressMeaning} {state : State} {source value : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.done value) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  obtain ⟨next,same,current,_⟩ := graph_evaluate_done_execution represented evaluate
  exact ⟨next,same,current⟩

/-- EVERY running/finished raw transition retains a specified source name assignment on all already allocated addresses. New names are constructed from actual allocations. -/
 theorem graph_stepRaw_names {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source := by
  -- one named field per branch of `stepRaw`; the case split itself is `StepCases.apply`
  refine StepCases.apply (P := fun state => GraphRepresentsBy meaning state source → ResultControl (stepRaw state).control → ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (stepRaw state) source)
    { complete := fun state value control represented successful => by exact ⟨meaning,(fun _ _ => rfl),by simpa [stepRaw,control] using represented⟩
      yielded := fun state plan control represented successful => by exact ⟨meaning,(fun _ _ => rfl),by simpa [stepRaw,control] using represented⟩
      refused := fun state reason control represented successful => by simp [stepRaw,control,ResultControl] at successful
      blackhole := fun state address control represented successful => by simp [stepRaw,control,ResultControl] at successful
      enter := fun state address control represented successful => by
        cases found : state.heap[address]? with
        | none => simp [stepRaw,control,found,ResultControl] at successful
        | some cell =>
            cases cell with
            | suspended origin => exact graph_enter_suspended_names represented control found
            | cached origin value => exact graph_enter_cached_names represented control found
            | evaluating origin => simp [stepRaw,control,found,ResultControl] at successful
      evaluate_bound := fun state index environment control represented successful => by
        cases found : environment[index]? with
        | none => simp [stepRaw,control,found,ResultControl] at successful
        | some address => exact graph_evaluate_bound_names represented control found
      evaluate_lam := fun state body environment control represented successful => by exact graph_evaluate_immediate_names (immediate := .closure body) represented control
      evaluate_nat := fun state number environment control represented successful => by exact graph_evaluate_immediate_names (immediate := .natural number) represented control
      evaluate_boolean := fun state value environment control represented successful => by exact graph_evaluate_immediate_names (immediate := .boolean value) represented control
      evaluate_label := fun state name environment control represented successful => by exact graph_evaluate_immediate_names (immediate := .label name) represented control
      evaluate_app := fun state function argument environment control represented successful => by exact graph_evaluate_context_names (context := .argument argument) represented control
      evaluate_mix := fun state lower upper environment control represented successful => by exact graph_evaluate_mix_names represented control
      evaluate_fix := fun state spec inherited environment control represented successful => by exact graph_evaluate_fix_names represented control
      evaluate_specification := fun state descriptor extension environment control represented successful => by exact graph_evaluate_pair_names (kind := .specification) represented control
      evaluate_prototype := fun state spec target environment control represented successful => by exact graph_evaluate_pair_names (kind := .prototype) represented control
      evaluate_record := fun state fields environment control represented successful => by exact graph_evaluate_record_names represented control
      evaluate_reflect := fun state term environment control represented successful => by exact graph_evaluate_context_names (context := .reflect) represented control
      evaluate_metadata := fun state term environment control represented successful => by exact graph_evaluate_context_names (context := .metadata) represented control
      evaluate_project := fun state term environment control represented successful => by exact graph_evaluate_context_names (context := .project) represented control
      evaluate_get := fun state target name environment control represented successful => by exact graph_evaluate_context_names (context := .field name) represented control
      evaluate_extend := fun state inherited fields environment control represented successful => by exact graph_evaluate_context_names (context := .extend fields) represented control
      evaluate_ifZero := fun state value zero body environment control represented successful => by exact graph_evaluate_context_names (context := .condition zero body) represented control
      evaluate_binary := fun state primitive left right environment control represented successful => by exact graph_evaluate_context_names (context := .binary primitive right) represented control
      evaluate_inject := fun state tag payload environment control represented successful => by exact graph_evaluate_inject_names represented control
      evaluate_case := fun state scrutinee arms environment control represented successful => by exact graph_evaluate_context_names (context := .case arms) represented control
      evaluate_ifBool := fun state condition whenTrue whenFalse environment control represented successful => by exact graph_evaluate_context_names (context := .ifBool whenTrue whenFalse) represented control
      evaluate_perform := fun state plan environment control represented successful => by
        cases shared : forcingShared state.stack with
        | true => simp [stepRaw,control,shared,ResultControl] at successful
        | false => exact graph_evaluate_perform_names represented control shared
      evaluate_done := fun state value environment control represented successful => by exact graph_evaluate_done_names represented control
      return_nil := fun state value control frames represented successful => by exact graph_complete_return_names represented control frames
      return_update := fun state value address rest control frames represented successful => by exact graph_cache_update_names represented control frames
      return_argument := fun state value argument environment rest control frames represented successful => by
        cases value with
        | closure body captured => exact graph_closure_call_names represented control frames
        | specification descriptor extension => exact graph_specification_call_names represented control frames
        | natural _ | boolean _ | label _ | record _ | prototype _ _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_reflect := fun state value rest control frames represented successful => by
        cases value with
        | prototype spec target => exact graph_object_access_names (access := .reflect) represented control frames
        | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_metadata := fun state value rest control frames represented successful => by
        cases value with
        | specification descriptor extension => exact graph_object_access_names (access := .metadata) represented control frames
        | closure _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_project := fun state value rest control frames represented successful => by
        cases value with
        | prototype spec target => exact graph_object_access_names (access := .project) represented control frames
        | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_field := fun state value name rest control frames represented successful => by
        cases value with
        | record fields =>
            cases found : fields.find? (fun field => field.1 == name) with
            | none => simp [stepRaw,control,frames,found,ResultControl] at successful
            | some field =>
                obtain ⟨key,address⟩ := field
                exact graph_field_return_names represented control frames found
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_extend := fun state value fields environment rest control frames represented successful => by
        cases value with
        | record inherited => exact graph_extend_record_names represented control frames
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_condition := fun state value zero body environment rest control frames represented successful => by
        cases value with
        | natural number =>
            cases number with
            | zero => exact graph_condition_zero_names represented control frames
            | succ number => exact graph_condition_successor_names represented control frames
        | closure _ _ | specification _ _ | prototype _ _ | record _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_binaryLeft := fun state value primitive right environment rest control frames represented successful => by exact graph_binary_left_return_names represented control frames
      return_binaryRight := fun state value primitive left rest control frames represented successful => by
        cases dispatch : (valueTerm left).bind (fun l => (valueTerm value).bind (primitiveResult primitive l)) with
        | none => simp [stepRaw,control,frames,dispatch,ResultControl] at successful
        | some result =>
            cases scalar : scalarValue result with
            | none => simp [stepRaw,control,frames,dispatch,scalar,ResultControl] at successful
            | some next => exact graph_primitive_return_names represented control frames dispatch scalar
      return_case := fun state value arms environment rest control frames represented successful => by
        cases value with
        | variant tag payload =>
            cases found : arms.find? (fun arm => arm.1 == tag) with
            | none => simp [stepRaw,control,frames,found,ResultControl] at successful
            | some arm =>
                obtain ⟨key,body⟩ := arm
                exact graph_case_return_names represented control frames found
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_ifBool := fun state value whenTrue whenFalse environment rest control frames represented successful => by
        cases value with
        | boolean value => exact graph_ifBool_return_names represented control frames
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
    } state represented successful


/-- Every demand-starting context advances through the real dispatcher,
including fields, reflection, extension, conditionals and binary operands. -/
 theorem graph_evaluate_context {state : State} {source hole : Term} {context : DemandContext} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (context.term hole) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_context_names byNames evaluate
  exact graphBy_graph advanced

 theorem graph_evaluate_bound {state : State} {source : Term} {environment : Environment} {index address : Nat}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.bound index) environment)
    (found : environment[index]? = some address) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_bound_names byNames evaluate found
  exact graphBy_graph advanced

 theorem graph_evaluate_immediate {state : State} {source : Term} {immediate : ImmediateValue} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate immediate.term environment) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_immediate_names byNames evaluate
  exact graphBy_graph advanced

 theorem graph_object_access {state : State} {source : Term} {access : ObjectAccess} {first second : Address} {rest : List Frame}
    (represented : GraphRepresents state source)
    (returned : state.control = .returned (access.value first second))
    (head : state.stack = access.frame::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_object_access_names byNames returned head
  exact graphBy_graph advanced

 theorem graph_specification_call {state : State} {source argument : Term} {environment : Environment}
    {descriptor extension : Address} {rest : List Frame} (represented : GraphRepresents state source)
    (returned : state.control = .returned (.specification descriptor extension))
    (head : state.stack = .argument argument environment::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_specification_call_names byNames returned head
  exact graphBy_graph advanced

/-- Every successful primitive dispatch performs the independent source
primitive step. The premises are the actual dispatch branches, rather than a
semantic oracle; all four primitives and all scalar results are covered. -/
 theorem graph_primitive_return {state : State} {source result : Term} {primitive : Primitive}
    {left right next : RuntimeValue} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned right)
    (head : state.stack = .binaryRight primitive left::rest)
    (dispatch : (valueTerm left).bind (fun l => (valueTerm right).bind (primitiveResult primitive l)) = some result)
    (scalar : scalarValue result = some next) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_primitive_return_names byNames returned head dispatch scalar
  exact graphBy_graph advanced

/-- General suspended→evaluating transition preserves the complete graph
relation, installing local source provenance at its actual update frame. -/
 theorem graph_enter_suspended {state : State} {source : Term} {address : Nat} {origin : Closure}
    (represented : GraphRepresents state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.suspended origin)) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_enter_suspended_names byNames enter found
  exact graphBy_graph advanced

/-- General evaluating→cached transition preserves the graph relation, using
the LOCAL update-segment derivation to certify the cell and to advance its
consumers. Closure/record caches are covered, and cyclic origins are allowed. -/
 theorem graph_cache_update {state : State} {source : Term} {address : Nat}
    {rest : List Frame} {value : RuntimeValue}
    (represented : GraphRepresents state source) (returned : state.control = .returned value)
    (update : state.stack = .update address::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_cache_update_names byNames returned update
  exact graphBy_graph advanced

/-- A later demand reuses the memoized value, with independent source
reduction justified by the cache's graph relation. It covers all value shapes. -/
 theorem graph_enter_cached {state : State} {source : Term} {address : Nat}
    {origin : Closure} {value : RuntimeValue}
    (represented : GraphRepresents state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.cached origin value)) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_enter_cached_names byNames enter found
  exact graphBy_graph advanced

/-- Specifications and prototypes allocate two independently suspended
closures. Both names denote their lexical source computations; neither field
is forced by constructing the value. -/
 theorem graph_evaluate_pair {state : State} {source first second : Term} {environment : Environment}
    {kind : PairObject} (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (kind.term first second) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_pair_names byNames evaluate
  exact graphBy_graph advanced

 theorem graph_evaluate_record {state : State} {source : Term} {fields : List (String × Term)} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.record fields) environment) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_record_names byNames evaluate
  exact graphBy_graph advanced

 theorem graph_field_return {state : State} {source : Term} {fields : List (String × Address)}
    {name key : String} {address : Address} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned (.record fields))
    (head : state.stack = .field name::rest)
    (found : fields.find? (fun field => field.1 == name) = some (key,address)) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_field_return_names byNames returned head found
  exact graphBy_graph advanced

 theorem graph_evaluate_mix {state : State} {source lower upper : Term} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_mix_names byNames evaluate
  exact graphBy_graph advanced

 theorem graph_condition_zero {state : State} {source zero body : Term} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned (.natural 0))
    (head : state.stack = .condition zero body environment::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_condition_zero_names byNames returned head
  exact graphBy_graph advanced

 theorem graph_condition_successor {state : State} {source zero body : Term} {environment : Environment}
    {number : Nat} {rest : List Frame} (represented : GraphRepresents state source)
    (returned : state.control = .returned (.natural (number+1)))
    (head : state.stack = .condition zero body environment::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_condition_successor_names byNames returned head
  exact graphBy_graph advanced

 theorem graph_extend_record {state : State} {source : Term} {inherited : List (String × Address)}
    {fields : List (String × Term)} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned (.record inherited))
    (head : state.stack = .extend fields environment::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_extend_record_names byNames returned head
  exact graphBy_graph advanced

/-- Allocating any lexical Fix ties one stable address to the closed source
Fix and retains its one-step unfolding as the cell origin. This is a general
graph preservation theorem, including nonempty captured environments and
active surrounding update segments. -/
 theorem graph_evaluate_fix {state : State} {source spec inherited : Term} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.fix spec inherited) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_fix_names byNames evaluate
  exact graphBy_graph advanced

/-- General lazy closure beta through the actual allocator. The newly suspended
argument has a closed source name, existing heap names retain their meanings,
and each local update segment advances by the independent source beta rule. -/
 theorem graph_closure_call {state : State} {source body argument : Term}
    {captured environment : Environment} {rest : List Frame}
    (represented : GraphRepresents state source)
    (returned : state.control = .returned (.closure body captured))
    (head : state.stack = .argument argument environment::rest) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_closure_call_names byNames returned head
  exact graphBy_graph advanced

/-- Entering a source application installs the lexical argument continuation;
its semantic demand segment is the independently defined source application. -/
 theorem graph_evaluate_application {state : State} {source function argument : Term}
    {environment : Environment} (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.app function argument) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_evaluate_application_names byNames evaluate
  exact graphBy_graph advanced

/-- Binary evaluation switches from the left demand to the right one without
forcing any captured arguments of the returned left value. -/
 theorem graph_binary_left_return {state : State} {source right : Term} {primitive : Primitive}
    {environment : Environment} {rest : List Frame} {value : RuntimeValue}
    (represented : GraphRepresents state source) (returned : state.control = .returned value)
    (head : state.stack = .binaryLeft primitive right environment::rest) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_binary_left_return_names byNames returned head
  exact graphBy_graph advanced

 theorem graph_complete_return {state : State} {source : Term} {value : RuntimeValue}
    (represented : GraphRepresents state source) (returned : state.control = .returned value)
    (empty : state.stack = []) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have byNames : GraphRepresentsBy meaning state source :=
    ⟨lexical,busy,final,names,heap,focus,control,stack⟩
  obtain ⟨next,_,advanced⟩ := graph_complete_return_names byNames returned empty
  exact graphBy_graph advanced

set_option maxHeartbeats 800000 in
/-- All actual raw transition cases preserve the graph relation when the
successor is running or finished. No syntactic fragment, evaluator oracle or
implementation-selected coverage premise is used. Operational invariants for
fault/blackhole successors are proved independently in DemandInvariant. -/
 theorem graph_via_names {state : State} {source : Term}
    (represented : GraphRepresents state source) (successful : ResultControl (stepRaw state).control) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  obtain ⟨next,_,advanced⟩ := graph_stepRaw_names ⟨lexical,busy,final,names,heap,focus,control,stack⟩ successful
  exact graphBy_graph advanced

 theorem graph_stepRaw {state : State} {source : Term}
    (represented : GraphRepresents state source) (successful : ResultControl (stepRaw state).control) :
    GraphRepresents (stepRaw state) source := by
  -- one named field per branch of `stepRaw`; the case split itself is `StepCases.apply`
  refine StepCases.apply (P := fun state => GraphRepresents state source → ResultControl (stepRaw state).control → GraphRepresents (stepRaw state) source)
    { complete := fun state value control represented successful => by simpa [stepRaw,control] using represented
      yielded := fun state plan control represented successful => by simpa [stepRaw,control] using represented
      refused := fun state reason control represented successful => by simp [stepRaw,control,ResultControl] at successful
      blackhole := fun state address control represented successful => by simp [stepRaw,control,ResultControl] at successful
      enter := fun state address control represented successful => by
        cases found : state.heap[address]? with
        | none => simp [stepRaw,control,found,ResultControl] at successful
        | some cell =>
            cases cell with
            | suspended origin => exact graph_enter_suspended represented control found
            | cached origin value => exact graph_enter_cached represented control found
            | evaluating origin => simp [stepRaw,control,found,ResultControl] at successful
      evaluate_bound := fun state index environment control represented successful => by
        cases found : environment[index]? with
        | none => simp [stepRaw,control,found,ResultControl] at successful
        | some address => exact graph_evaluate_bound represented control found
      evaluate_lam := fun state body environment control represented successful => by exact graph_evaluate_immediate (immediate := .closure body) represented control
      evaluate_nat := fun state number environment control represented successful => by exact graph_evaluate_immediate (immediate := .natural number) represented control
      evaluate_boolean := fun state value environment control represented successful => by exact graph_evaluate_immediate (immediate := .boolean value) represented control
      evaluate_label := fun state name environment control represented successful => by exact graph_evaluate_immediate (immediate := .label name) represented control
      evaluate_app := fun state function argument environment control represented successful => by exact graph_evaluate_context (context := .argument argument) represented control
      evaluate_mix := fun state lower upper environment control represented successful => by exact graph_evaluate_mix represented control
      evaluate_fix := fun state spec inherited environment control represented successful => by exact graph_evaluate_fix represented control
      evaluate_specification := fun state descriptor extension environment control represented successful => by exact graph_evaluate_pair (kind := .specification) represented control
      evaluate_prototype := fun state spec target environment control represented successful => by exact graph_evaluate_pair (kind := .prototype) represented control
      evaluate_record := fun state fields environment control represented successful => by exact graph_evaluate_record represented control
      evaluate_reflect := fun state term environment control represented successful => by exact graph_evaluate_context (context := .reflect) represented control
      evaluate_metadata := fun state term environment control represented successful => by exact graph_evaluate_context (context := .metadata) represented control
      evaluate_project := fun state term environment control represented successful => by exact graph_evaluate_context (context := .project) represented control
      evaluate_get := fun state target name environment control represented successful => by exact graph_evaluate_context (context := .field name) represented control
      evaluate_extend := fun state inherited fields environment control represented successful => by exact graph_evaluate_context (context := .extend fields) represented control
      evaluate_ifZero := fun state value zero body environment control represented successful => by exact graph_evaluate_context (context := .condition zero body) represented control
      evaluate_binary := fun state primitive left right environment control represented successful => by exact graph_evaluate_context (context := .binary primitive right) represented control
      evaluate_inject := fun state _ _ environment control represented successful => by exact graph_via_names represented successful
      evaluate_case := fun state _ _ environment control represented successful => by exact graph_via_names represented successful
      evaluate_ifBool := fun state _ _ _ environment control represented successful => by exact graph_via_names represented successful
      evaluate_perform := fun state _ environment control represented successful => by exact graph_via_names represented successful
      evaluate_done := fun state _ environment control represented successful => by exact graph_via_names represented successful
      return_nil := fun state value control frames represented successful => by exact graph_complete_return represented control frames
      return_update := fun state value address rest control frames represented successful => by exact graph_cache_update represented control frames
      return_argument := fun state value argument environment rest control frames represented successful => by
        cases value with
        | closure body captured => exact graph_closure_call represented control frames
        | specification descriptor extension => exact graph_specification_call represented control frames
        | natural _ | boolean _ | label _ | record _ | prototype _ _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_reflect := fun state value rest control frames represented successful => by
        cases value with
        | prototype spec target => exact graph_object_access (access := .reflect) represented control frames
        | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_metadata := fun state value rest control frames represented successful => by
        cases value with
        | specification descriptor extension => exact graph_object_access (access := .metadata) represented control frames
        | closure _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_project := fun state value rest control frames represented successful => by
        cases value with
        | prototype spec target => exact graph_object_access (access := .project) represented control frames
        | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_field := fun state value name rest control frames represented successful => by
        cases value with
        | record fields =>
            cases found : fields.find? (fun field => field.1 == name) with
            | none => simp [stepRaw,control,frames,found,ResultControl] at successful
            | some field =>
                obtain ⟨key,address⟩ := field
                exact graph_field_return represented control frames found
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_extend := fun state value fields environment rest control frames represented successful => by
        cases value with
        | record inherited => exact graph_extend_record represented control frames
        | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_condition := fun state value zero body environment rest control frames represented successful => by
        cases value with
        | natural number =>
            cases number with
            | zero => exact graph_condition_zero represented control frames
            | succ number => exact graph_condition_successor represented control frames
        | closure _ _ | specification _ _ | prototype _ _ | record _ | boolean _ | label _ | variant _ _ =>
            simp [stepRaw,control,frames,ResultControl] at successful
      return_binaryLeft := fun state value primitive right environment rest control frames represented successful => by exact graph_binary_left_return represented control frames
      return_binaryRight := fun state value primitive left rest control frames represented successful => by
        cases dispatch : (valueTerm left).bind (fun l => (valueTerm value).bind (primitiveResult primitive l)) with
        | none => simp [stepRaw,control,frames,dispatch,ResultControl] at successful
        | some result =>
            cases scalar : scalarValue result with
            | none => simp [stepRaw,control,frames,dispatch,scalar,ResultControl] at successful
            | some next => exact graph_primitive_return represented control frames dispatch scalar
      return_case := fun state value _ _ rest control frames represented successful => by exact graph_via_names represented successful
      return_ifBool := fun state value _ _ _ rest control frames represented successful => by exact graph_via_names represented successful
    } state represented successful

/-- A concrete cyclic heap instance: its one address denotes the source Fix;
the saved origin captures that same address and denotes its independent source
unfolding. Neither this witness nor the lexical invariant forbids the cycle. -/
 theorem initial_fix_graph {spec inherited : Term}
    (hs : Scoped 0 spec) (hi : Scoped 0 inherited) :
    GraphRepresents (stepRaw (initial (.fix spec inherited))) (.fix spec inherited) := by
  have lexical := stepRaw_lexicalInvariant (initial_lexicalInvariant (Scoped.fix hs hi))
  let meaning : AddressMeaning := fun _ => .fix spec inherited
  have rs : spec.rename Nat.succ = spec := scoped_rename_identity hs _ (by intros; omega)
  have ri : inherited.rename Nat.succ = inherited := scoped_rename_identity hi _ (by intros; omega)
  have ss : spec.substitute (environmentSubstitution meaning [0]) = spec :=
    scoped_substitute_identity hs _ (by intros; omega)
  have si : inherited.substitute (environmentSubstitution meaning [0]) = inherited :=
    scoped_substitute_identity hi _ (by intros; omega)
  refine ⟨lexical,stepRaw_busyInvariant (initial_busyInvariant _),stepRaw_finalStackInvariant (initial_finalStackInvariant _),meaning,?_,?_,.fix spec inherited,?_,?_⟩
  · intro address allocated
    exact Scoped.fix hs hi
  · intro address cell found
    simp [initial,stepRaw] at found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have zero : address = 0 := by simpa using bound
    subst address
    simp at found
    subst cell
    constructor
    · simpa [closeOrigin,closeTerm,cellOrigin,Term.substitute,rs,ri,ss,si,
        environmentSubstitution,meaning] using Steps.next (Step.fix spec inherited) (Steps.refl _)
    · trivial
  · simp [initial,stepRaw,controlMeaning,meaning]
  · simp only [initial,stepRaw,StackRealizes]
    exact .refl _

/-- Finite raw execution is independent of capacity. Resource completeness
below computes a sufficient bound from this real transition trace; it does not
assert that a source computation terminates. -/
def rawRun : Nat → State → State
  | 0,state => state
  | ticks+1,state => rawRun ticks (stepRaw state)

/-- Pointer entry and bare variable lookup are administrative demand work.
The endpoint can be a genuine source constructor, returned/cache value, or an
explicit fault/blackhole; terminating this segment does not label a blackhole
as source divergence. -/
def DemandAdministrative (state : State) : Prop :=
  match state.control with
  | .enter _ | .evaluate (.bound _) _ => True
  | _ => False

def DemandAdministrationHalts (state : State) : Prop :=
  ∃ ticks, ¬ DemandAdministrative (rawRun ticks state)

def AdministrativeBudget (cost cap : Nat) : Prop :=
  ∀ (meaning : AddressMeaning) (state : State), HeapRealizes meaning state.heap → HeapOriginsBorn state.heap →
    (∀ (address : Address) (result : Term), state.control = .enter address → address+1 ≤ cap →
      SourceDerivation (meaning address) result cost → DemandAdministrationHalts state) ∧
    (∀ (term : Term) (environment : Environment) (result : Term), state.control = .evaluate term environment →
      EnvironmentValid cap environment → SourceDerivation (closeTerm meaning environment term) result cost →
      DemandAdministrationHalts state)

 theorem originBorn_capture_bound {address : Address} {origin : Closure}
    (born : OriginBorn address origin) : EnvironmentValid (address+1) origin.environment := by
  rcases born with ordinary | ⟨spec,inherited,captured,environmentEq,captures,termEq⟩
  · intro reference member; exact Nat.lt_trans (ordinary reference member) (Nat.lt_succ_self _)
  · rw [environmentEq]
    intro reference member
    rcases List.mem_cons.mp member with equal | old
    · subst reference; exact Nat.lt_succ_self _
    · exact Nat.lt_trans (captures reference old) (Nat.lt_succ_self _)

/-- Actual administrative demand segments are finite by lexicographic descent
on independent source cost and lexical birth address. This allows real tied
Fix and sharing; it assumes neither an acyclic heap nor finite unfolding. -/
 theorem administrative_budget_halts (cost cap : Nat) : AdministrativeBudget cost cap := by
  induction cost using Nat.strongRecOn generalizing cap with
  | ind cost costIH =>
      induction cap using Nat.strongRecOn with
      | ind cap capIH =>
          have allEnters : ∀ (meaning : AddressMeaning) (state : State), HeapRealizes meaning state.heap → HeapOriginsBorn state.heap →
              ∀ (address : Address) (result : Term), state.control = .enter address → address+1 ≤ cap →
              SourceDerivation (meaning address) result cost → DemandAdministrationHalts state := by
            intro meaning state heap born address result enter addressCap derivation
            cases found : state.heap[address]? with
            | none => exact ⟨1,by simp [rawRun,stepRaw,enter,found,DemandAdministrative]⟩
            | some cell =>
                cases cell with
                | evaluating origin => exact ⟨1,by simp [rawRun,stepRaw,enter,found,DemandAdministrative]⟩
                | cached origin value => exact ⟨1,by simp [rawRun,stepRaw,enter,found,DemandAdministrative]⟩
                | suspended origin =>
                    have old := heap address _ found
                    have originBorn := born address _ found
                    have nextHeap : HeapRealizes meaning (stepRaw state).heap := by
                      simpa [stepRaw,enter,found] using heapRealizes_set heap (show CellRealizes meaning address (.evaluating origin) from old)
                    have nextBorn : HeapOriginsBorn (stepRaw state).heap := by
                      simpa [stepRaw,enter,found] using heapOriginsBorn_set born found (show cellOrigin (.evaluating origin) = cellOrigin (.suspended origin) from rfl)
                    have nextControl : (stepRaw state).control = .evaluate origin.term origin.environment := by simp [stepRaw,enter,found]
                    have halted : DemandAdministrationHalts (stepRaw state) := by
                      rcases originBorn_demand_descent originBorn old.1 derivation with captures | ⟨smaller,tail,less⟩
                      · obtain ⟨smaller,tail,le⟩ := sourceSteps_derivation_tail old.1 derivation
                        by_cases less : smaller < cost
                        · exact (costIH smaller less address meaning (stepRaw state) nextHeap nextBorn).2
                            origin.term origin.environment result nextControl captures tail
                        · have equal : smaller = cost := by omega
                          subst smaller
                          exact (capIH address (Nat.lt_of_lt_of_le (Nat.lt_succ_self address) addressCap) meaning (stepRaw state) nextHeap nextBorn).2
                            origin.term origin.environment result nextControl captures tail
                      · exact (costIH smaller less (address+1) meaning (stepRaw state) nextHeap nextBorn).2
                          origin.term origin.environment result nextControl (originBorn_capture_bound originBorn) tail
                    obtain ⟨ticks,stop⟩ := halted
                    exact ⟨ticks+1,stop⟩
          intro meaning state heap born
          refine ⟨allEnters meaning state heap born,?_⟩
          intro term environment result evaluate captures derivation
          by_cases isBound : ∃ index, term = .bound index
          · obtain ⟨index,rfl⟩ := isBound
            cases found : environment[index]? with
            | none => exact ⟨1,by simp [rawRun,stepRaw,evaluate,found,DemandAdministrative]⟩
            | some address =>
                have addressCap : address+1 ≤ cap := by
                  have less := captures address (List.mem_of_getElem? found)
                  exact Nat.succ_le_of_lt less
                have demand : SourceDerivation (meaning address) result cost := by
                  cases environment with
                  | nil => simp at found
                  | cons reference references =>
                      simpa [closeTerm,Term.substitute,environmentSubstitution,found] using derivation
                have nextHeap : HeapRealizes meaning (stepRaw state).heap := by simpa [stepRaw,evaluate,found] using heap
                have nextBorn : HeapOriginsBorn (stepRaw state).heap := by simpa [stepRaw,evaluate,found] using born
                have nextControl : (stepRaw state).control = .enter address := by simp [stepRaw,evaluate,found]
                obtain ⟨ticks,stop⟩ := allEnters meaning (stepRaw state) nextHeap nextBorn
                  address result nextControl addressCap demand
                exact ⟨ticks+1,stop⟩
          · refine ⟨0,?_⟩
            cases term <;> simp_all [rawRun,DemandAdministrative]

def retainedState : Outcome → State
  | .finished _ state | .suspended _ state | .divergent _ state | .refused _ state
  | .yielded _ state => state

def TraceFits (limits : Limits) : Nat → State → Prop
  | 0,_ => True
  | ticks+1,state =>
      (stepRaw state).heap.size ≤ limits.heap ∧
      (stepRaw state).stack.length ≤ limits.stack ∧ TraceFits limits ticks (stepRaw state)

/-- Explicit maximum heap/stack bounds along the requested finite trace. Tick
bound is its length. A resource suspension requires larger bounds and keeps the
exact resumable state; this maximum is a semantic bound, not a native allocator. -/
def traceLimits : Nat → State → Limits
  | 0,_ => ⟨0,0⟩
  | ticks+1,state =>
      let next := stepRaw state
      let later := traceLimits ticks next
      ⟨max next.heap.size later.heap,max next.stack.length later.stack⟩

 theorem traceFits_mono {ticks : Nat} {state : State} {small large : Limits}
    (fits : TraceFits small ticks state) (heap : small.heap ≤ large.heap)
    (stack : small.stack ≤ large.stack) : TraceFits large ticks state := by
  induction ticks generalizing state with
  | zero => trivial
  | succ ticks ih =>
      exact ⟨Nat.le_trans fits.1 heap,Nat.le_trans fits.2.1 stack,ih fits.2.2⟩

 theorem traceFits_traceLimits (ticks : Nat) (state : State) :
    TraceFits (traceLimits ticks state) ticks state := by
  induction ticks generalizing state with
  | zero => trivial
  | succ ticks ih =>
      refine ⟨Nat.le_max_left _ _,Nat.le_max_left _ _,?_⟩
      exact traceFits_mono (ih (stepRaw state)) (Nat.le_max_right _ _) (Nat.le_max_right _ _)

 theorem rawRun_absorbs {state : State} (ticks : Nat) (absorbs : stepRaw state = state) :
    rawRun ticks state = state := by
  induction ticks with
  | zero => rfl
  | succ ticks ih => simpa only [rawRun,absorbs] using ih

 theorem rawRun_resultControl {ticks : Nat} {state : State}
    (successful : ResultControl (rawRun ticks state).control) : ResultControl state.control := by
  cases control : state.control with
  | evaluate _ _ | enter _ | returned _ | complete _ => trivial
  | refused reason | blackhole address | yielded _ =>
      have absorbing : stepRaw state = state := by simp [stepRaw,control]
      simp only [rawRun_absorbs ticks absorbing,control,ResultControl] at successful

/-- A normally terminating trace never traverses an absorbing fault or
blackhole. This derives the per-step successful classification from the
actual final control, instead of assuming coverage along the trace. -/
 theorem rawRun_graph {ticks : Nat} {state : State} {source : Term}
    (represented : GraphRepresents state source)
    (successful : ResultControl (rawRun ticks state).control) : GraphRepresents (rawRun ticks state) source := by
  induction ticks generalizing state with
  | zero => exact represented
  | succ ticks ih =>
      have nextSuccessful : ResultControl (stepRaw state).control := rawRun_resultControl successful
      exact ih (graph_stepRaw represented nextSuccessful) successful

 theorem graph_terminating_administration {state : State} {source result : Term}
    (represented : GraphRepresents state source) (born : HeapOriginsBorn state.heap)
    (terminates : Evaluates source result) : DemandAdministrationHalts state := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  obtain ⟨wholeCost,whole⟩ := source_evaluates_derivation
    (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
  obtain ⟨value,cost,demand,_⟩ := stack_derivation_demand whole
  have valid := lexical.2.1
  cases current : state.control with
  | evaluate term environment =>
      simp only [current,controlMeaning,Option.some.injEq] at control
      subst focus
      have evalValid : ClosureValid state.heap.size ⟨term,environment⟩ := by
        simpa only [current,ControlValid] using valid
      exact (administrative_budget_halts cost state.heap.size meaning state heap born).2
        term environment value current evalValid.2 demand
  | enter address =>
      simp only [current,controlMeaning,Option.some.injEq] at control
      subst focus
      have allocated : address < state.heap.size := by simpa only [current,ControlValid] using valid
      exact (administrative_budget_halts cost state.heap.size meaning state heap born).1
        address value current (Nat.succ_le_of_lt allocated) demand
  | returned value | complete value | refused reason | blackhole address | yielded _ =>
      exact ⟨0,by simp [rawRun,DemandAdministrative,current]⟩

 theorem rawRun_reachable {start state : State} (reachable : Reachable start state) (ticks : Nat) :
    Reachable start (rawRun ticks state) := by
  induction ticks generalizing state with
  | zero => exact reachable
  | succ ticks ih => exact ih (.next reachable)

/-- Independent source termination gives finite actual administrative progress
at EVERY running/finished raw prefix of the closed program. This is a concrete
executor theorem with no caller-supplied graph representation or acyclicity.
Its endpoint still explicitly allows a fault/blackhole; full completeness must
exclude those endpoints and compose demands through semantic constructors. -/
 theorem rawRun_terminating_administration {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (ticks : Nat)
    (successful : ResultControl (rawRun ticks (initial source)).control) :
    DemandAdministrationHalts (rawRun ticks (initial source)) := by
  exact graph_terminating_administration (rawRun_graph (graph_initializes closed) successful)
    (reachable_originsBorn closed (rawRun_reachable .start ticks)) terminates

/-- Phase provenance is genuinely required for completeness. Even the graph
relation plus birth-valid origins and a terminating source can be fabricated
with an unearned evaluating phase. Actual reachability must exclude this
state; treating GraphRepresents as a completeness oracle would be unsound. -/
 theorem represented_born_blackhole_counterexample :
    ∃ state : State, GraphRepresents state (.nat 0) ∧ HeapOriginsBorn state.heap ∧
      Evaluates (.nat 0) (.nat 0) ∧ (stepRaw state).control = .blackhole 0 := by
  let state : State := ⟨#[.evaluating ⟨.nat 0,[]⟩],.enter 0,[.update 0]⟩
  have singleton : ∀ address cell, state.heap[address]? = some cell →
      address = 0 ∧ cell = .evaluating ⟨.nat 0,[]⟩ := by
    intro address cell found
    have allocated := (Array.getElem?_eq_some_iff.mp found).1
    have addressEq : address = 0 := by change address < 1 at allocated; omega
    subst address
    exact ⟨rfl,by simpa [state] using found.symm⟩
  have lexical : LexicalInvariant state := by
    refine ⟨?_,by simp [state,ControlValid],?_⟩
    · intro address cell found
      obtain ⟨rfl,rfl⟩ := singleton address cell found
      exact ⟨.natural _,by simp [EnvironmentValid]⟩
    · intro frame member
      simp [state] at member
      subst frame
      simp [FrameValid,state]
  have busy : BusyInvariant state := by
    simp only [BusyInvariant,Busy,state,stackUpdates,List.nodup_cons,List.nodup_nil,List.not_mem_nil,true_and,not_false_eq_true]
    intro address
    cases address <;> simp
  have realized : HeapRealizes (fun _ => .nat 0) state.heap := by
    intro address cell found
    obtain ⟨rfl,rfl⟩ := singleton address cell found
    exact ⟨.refl _,trivial⟩
  refine ⟨state,⟨lexical,busy,?_,fun _ => .nat 0,?_,realized,.nat 0,rfl,?_⟩,?_,⟨.refl _,.natural _⟩,?_⟩
  · intro value complete; cases complete
  · intro address allocated; exact .natural _
  · exact ⟨.refl _,.refl _⟩
  · intro address cell found
    obtain ⟨rfl,rfl⟩ := singleton address cell found
    exact Or.inl (by simp [EnvironmentValid,cellOrigin])
  · simp [stepRaw,state]

 theorem rawRun_natural_sound {ticks : Nat} {source : Term} {number : Nat}
    (closed : Scoped 0 source) (complete : (rawRun ticks (initial source)).control = .complete (.natural number)) :
    Evaluates source (.nat number) := by
  apply graph_complete_natural_sound (rawRun_graph (graph_initializes closed) ?_) complete
  simp only [complete,ResultControl]

 theorem rawRun_boolean_sound {ticks : Nat} {source : Term} {value : Bool}
    (closed : Scoped 0 source) (complete : (rawRun ticks (initial source)).control = .complete (.boolean value)) :
    Evaluates source (.boolean value) := by
  apply graph_complete_boolean_sound (rawRun_graph (graph_initializes closed) ?_) complete
  simp only [complete,ResultControl]

 theorem rawRun_label_sound {ticks : Nat} {source : Term} {name : String}
    (closed : Scoped 0 source) (complete : (rawRun ticks (initial source)).control = .complete (.label name)) :
    Evaluates source (.label name) := by
  apply graph_complete_label_sound (rawRun_graph (graph_initializes closed) ?_) complete
  simp only [complete,ResultControl]

 theorem step_finished_control {limits : Limits} {state final : State} {value : RuntimeValue}
    (finished : step limits state = .finished value final) : final.control = .complete value := by
  cases control : state.control <;> simp only [step,control] at finished
  all_goals try (split at finished <;> contradiction)
  all_goals try contradiction
  cases finished
  exact control

 theorem step_ticks_raw {limits : Limits} {state next : State}
    (stepped : step limits state = .suspended .ticks next) : next = stepRaw state := by
  cases control : state.control <;> simp only [step,control] at stepped
  all_goals try contradiction
  all_goals split at stepped <;> simp_all

 theorem runBounded_finished_control {limits : Limits} {ticks : Nat} {state final : State} {value : RuntimeValue}
    (finished : runBounded limits ticks state = .finished value final) : final.control = .complete value := by
  induction ticks generalizing state with
  | zero =>
      cases control : state.control <;> simp only [runBounded,control] at finished
      all_goals try contradiction
      cases finished
      exact control
  | succ ticks ih =>
      cases stepped : step limits state with
      | finished value next =>
          simp only [runBounded,stepped] at finished
          cases finished
          exact step_finished_control stepped
      | suspended reason next =>
          cases reason with
          | ticks => exact ih (by simpa only [runBounded,stepped] using finished)
          | capacity => simp [runBounded,stepped] at finished
      | divergent address next | refused reason next | yielded _ next => simp [runBounded,stepped] at finished

 theorem runBounded_finished_resultControl {limits : Limits} {ticks : Nat} {state final : State} {value : RuntimeValue}
    (finished : runBounded limits ticks state = .finished value final) : ResultControl state.control := by
  cases control : state.control with
  | evaluate _ _ | enter _ | returned _ | complete _ => trivial
  | blackhole address | refused reason | yielded _ =>
      cases ticks <;> simp [runBounded,step,control] at finished

/-- The actual finite-resource executor is sound at EVERY bound: a finished
result supplies its own successful-path classification. Tick/capacity
suspension and blackholes cannot be laundered into source evaluations. -/
 theorem runBounded_finished_graph {limits : Limits} {ticks : Nat} {state final : State}
    {source : Term} {value : RuntimeValue} (represented : GraphRepresents state source)
    (finished : runBounded limits ticks state = .finished value final) : GraphRepresents final source := by
  induction ticks generalizing state with
  | zero =>
      cases control : state.control <;> simp only [runBounded,control] at finished
      all_goals try contradiction
      cases finished
      exact represented
  | succ ticks ih =>
      cases stepped : step limits state with
      | finished value next =>
          have eq : next = state := by
            cases control : state.control <;> simp only [step,control] at stepped
            all_goals try (split at stepped <;> contradiction)
            all_goals try contradiction
            cases stepped; rfl
          simp only [runBounded,stepped] at finished
          cases finished
          simpa only [eq] using represented
      | suspended reason next =>
          cases reason with
          | ticks =>
              have rest : runBounded limits ticks next = .finished value final := by simpa only [runBounded,stepped] using finished
              have raw := step_ticks_raw stepped
              have successful : ResultControl (stepRaw state).control := by
                simpa only [←raw] using runBounded_finished_resultControl rest
              exact ih (by simpa only [raw] using graph_stepRaw represented successful) rest
          | capacity => simp [runBounded,stepped] at finished
      | divergent address next | refused reason next | yielded _ next => simp [runBounded,stepped] at finished

 theorem runBounded_natural_sound {limits : Limits} {ticks : Nat} {source : Term} {number : Nat} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished (.natural number) final) :
    Evaluates source (.nat number) :=
  graph_complete_natural_sound (runBounded_finished_graph (graph_initializes closed) finished) (runBounded_finished_control finished)

 theorem runBounded_boolean_sound {limits : Limits} {ticks : Nat} {source : Term} {value : Bool} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished (.boolean value) final) :
    Evaluates source (.boolean value) :=
  graph_complete_boolean_sound (runBounded_finished_graph (graph_initializes closed) finished) (runBounded_finished_control finished)

 theorem runBounded_label_sound {limits : Limits} {ticks : Nat} {source : Term} {name : String} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished (.label name) final) :
    Evaluates source (.label name) :=
  graph_complete_label_sound (runBounded_finished_graph (graph_initializes closed) finished) (runBounded_finished_control finished)

 theorem runBounded_value_sound {limits : Limits} {ticks : Nat} {source : Term} {value : RuntimeValue} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished value final) :
    ∃ meaning : AddressMeaning, MeaningsScoped final.heap.size meaning ∧ HeapRealizes meaning final.heap ∧
      Evaluates source (valueMeaning meaning value) :=
  graph_complete_value_sound (runBounded_finished_graph (graph_initializes closed) finished) (runBounded_finished_control finished)

def observationTerm : Observation → Term
  | .natural number => .nat number
  | .boolean value => .boolean value
  | .label name => .label name

def observationRuntime : Observation → RuntimeValue
  | .natural number => .natural number
  | .boolean value => .boolean value
  | .label name => .label name

 theorem runBounded_observation_sound {limits : Limits} {ticks : Nat} {source : Term} {result : Observation} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished (observationRuntime result) final) :
    Evaluates source (observationTerm result) := by
  cases result with
  | natural _ => exact runBounded_natural_sound closed finished
  | boolean _ => exact runBounded_boolean_sound closed finished
  | label _ => exact runBounded_label_sound closed finished

 theorem runBounded_observes_sound {limits : Limits} {ticks : Nat} {source : Term} {result : Observation} {final : State}
    (closed : Scoped 0 source) (finished : runBounded limits ticks (initial source) = .finished (observationRuntime result) final) :
    ∃ value, Evaluates source value ∧ Observes value result := by
  refine ⟨observationTerm result,runBounded_observation_sound closed finished,?_⟩
  cases result with
  | natural number => exact Observes.natural number
  | boolean value => exact Observes.boolean value
  | label name => exact Observes.label name

/-- Changing resources cannot change a normally returned ground observation.
This covers every closed partial program and observations of different kinds,
not only repeated numeric fixture runs. Suspension makes no result claim. -/
 theorem runBounded_resource_independent {source : Term} {firstLimits secondLimits : Limits}
    {firstTicks secondTicks : Nat} {first second : Observation} {firstState secondState : State}
    (closed : Scoped 0 source)
    (left : runBounded firstLimits firstTicks (initial source) = .finished (observationRuntime first) firstState)
    (right : runBounded secondLimits secondTicks (initial source) = .finished (observationRuntime second) secondState) :
    first = second := by
  have eq := source_evaluates_unique (runBounded_observation_sound closed left) (runBounded_observation_sound closed right)
  cases first <;> cases second <;> simp [observationTerm] at eq
  all_goals subst_vars; rfl

 theorem runBounded_retains_rawRun {limits : Limits} {ticks : Nat} {state : State}
    (fits : TraceFits limits ticks state) :
    retainedState (runBounded limits ticks state) = rawRun ticks state := by
  induction ticks generalizing state with
  | zero => cases control : state.control <;> simp [runBounded,rawRun,retainedState,control]
  | succ ticks ih =>
      have next := ih fits.2.2
      cases control : state.control
      all_goals first
        | have admitted : step limits state = .suspended .ticks (stepRaw state) := by
            simp [step,control,fits.1,fits.2.1]
          simpa only [runBounded,admitted,rawRun] using next
        | have absorbing : stepRaw state = state := by simp [stepRaw,control]
          simpa only [runBounded,step,control,retainedState] using
            (rawRun_absorbs (ticks+1) absorbing).symm

set_option linter.unnecessarySimpa false in
 theorem runBounded_complete_classifies {limits : Limits} {ticks : Nat} {state : State}
    {value : RuntimeValue}
    (complete : (retainedState (runBounded limits ticks state)).control = .complete value) :
    runBounded limits ticks state =
      .finished value (retainedState (runBounded limits ticks state)) := by
  induction ticks generalizing state with
  | zero => cases control : state.control <;> simp_all [runBounded,retainedState]
  | succ ticks ih =>
      cases control : state.control
      all_goals first
        | simpa [runBounded,step,control,retainedState] using complete
        | by_cases within : (stepRaw state).heap.size ≤ limits.heap ∧
              (stepRaw state).stack.length ≤ limits.stack
          · have admitted : step limits state = .suspended .ticks (stepRaw state) := by
              simp [step,control,within.1,within.2]
            simp only [runBounded,admitted] at complete ⊢
            exact ih complete
          · have capacity : step limits state = .suspended .capacity state := by
              simp [step,control,Bool.and_eq_true,within]
            simp only [runBounded,capacity,retainedState] at complete
            rw [control] at complete
            contradiction

 theorem adequate_trace_execution (ticks : Nat) (state : State) :
    retainedState (runBounded (traceLimits ticks state) ticks state) = rawRun ticks state :=
  runBounded_retains_rawRun (traceFits_traceLimits ticks state)

/-- The finite-resource wrapper realizes the source-derived administrative
progress segment at its concrete trace maxima. This promises progress past
pointer lookup, not normal completion of the entire program. -/
 theorem runBounded_terminating_administration {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (prefixTicks : Nat)
    (successful : ResultControl (rawRun prefixTicks (initial source)).control) :
    ∃ ticks limits, ¬ DemandAdministrative
      (retainedState (runBounded limits ticks (rawRun prefixTicks (initial source)))) := by
  obtain ⟨ticks,stop⟩ := rawRun_terminating_administration closed terminates prefixTicks successful
  refine ⟨ticks,traceLimits ticks (rawRun prefixTicks (initial source)),?_⟩
  simpa only [adequate_trace_execution] using stop

 theorem adequate_trace_completion {ticks : Nat} {state : State} {value : RuntimeValue}
    (complete : (rawRun ticks state).control = .complete value) :
    runBounded (traceLimits ticks state) ticks state = .finished value (rawRun ticks state) := by
  have retained := adequate_trace_execution ticks state
  have classified := runBounded_complete_classifies (retained ▸ complete)
  simpa only [retained] using classified

 theorem rawRun_lexicalInvariant {source : Term} (closed : Scoped 0 source) (ticks : Nat) :
    LexicalInvariant (rawRun ticks (initial source)) := by
  have general : ∀ ticks state, LexicalInvariant state → LexicalInvariant (rawRun ticks state) := by
    intro ticks
    induction ticks with
    | zero => intro state invariant; exact invariant
    | succ ticks ih => intro state invariant; exact ih _ (stepRaw_lexicalInvariant invariant)
  exact general ticks _ (initial_lexicalInvariant closed)

 theorem rawRun_preservesOrigins (ticks : Nat) (state : State) :
    PreservesOrigins state.heap (rawRun ticks state).heap := by
  induction ticks generalizing state with
  | zero => exact preservesOrigins_refl _
  | succ ticks ih => exact preservesOrigins_trans (stepRaw_preservesOrigins _) (ih _)

 theorem rawRun_preservesCached (ticks : Nat) (state : State) :
    PreservesCached state.heap (rawRun ticks state).heap := by
  induction ticks generalizing state with
  | zero => exact preservesCached_refl _
  | succ ticks ih => exact preservesCached_trans (stepRaw_preservesCached _) (ih _)

/-- All unused arguments, including arbitrary diverging Fix computations,
remain suspended at their original lexical address. This is a general theorem
about the actual bounded executor, not a single closed native test. -/
 theorem unused_argument_executor (argument : Term) (number : Nat) :
    runBounded ⟨1,1⟩ 5 (initial (.app (.lam (.nat number)) argument)) =
      .finished (.natural number)
        ⟨#[.suspended ⟨argument,[]⟩],.complete (.natural number),[]⟩ := by
  simp [runBounded,step,stepRaw,initial]

 theorem unused_argument_source (argument : Term) (number : Nat) :
    Evaluates (.app (.lam (.nat number)) argument) (.nat number) := by
  constructor
  · have beta := Step.beta (.nat number) argument
    simpa [instantiate,Term.substitute] using Steps.next beta (Steps.refl _)
  · exact .natural _

/-- The second demand sees the first demand's cache at the identical address.
This exercises real memoization for every natural argument. -/
 theorem shared_argument_executor (number : Nat) :
    runBounded ⟨1,2⟩ 13
      (initial (.app (.lam (.binary .add (.bound 0) (.bound 0))) (.nat number))) =
    .finished (.natural (number+number))
      ⟨#[.cached ⟨.nat number,[]⟩ (.natural number)],.complete (.natural (number+number)),[]⟩ := by
  simp [runBounded,step,stepRaw,initial,primitiveResult,valueTerm,scalarValue,
    Array.set!,Array.setIfInBounds]

 theorem shared_argument_source (number : Nat) :
    Evaluates (.app (.lam (.binary .add (.bound 0) (.bound 0))) (.nat number)) (.nat (number+number)) := by
  constructor
  · have beta := Step.beta (.binary .add (.bound 0) (.bound 0)) (.nat number)
    have primitive := Step.primitive .add (.nat number) (.nat number) (.nat (number+number))
      (.natural _) (.natural _) rfl
    exact .next (by simpa [instantiate,Term.substitute] using beta) (.next primitive (.refl _))
  · exact .natural _

/-- Two demands of the same record field cache exactly its one address. The
other field retains arbitrary source, including a divergent knot, suspended.
The record target itself also retains its original source and cached pointer map. -/
 theorem shared_field_executor (unused : Term) (number : Nat) :
    runBounded ⟨3,3⟩ 21
      (initial (.app
        (.lam (.binary .add (.get (.bound 0) "x") (.get (.bound 0) "x")))
        (.record [("x",.nat number),("unused",unused)]))) =
    .finished (.natural (number+number))
      ⟨#[.cached ⟨.record [("x",.nat number),("unused",unused)],[]⟩
          (.record [("x",1),("unused",2)]),
        .cached ⟨.nat number,[]⟩ (.natural number),
        .suspended ⟨unused,[]⟩],.complete (.natural (number+number)),[]⟩ := by
  simp [runBounded,step,stepRaw,initial,primitiveResult,valueTerm,scalarValue,
    allocateFields,Array.set!,Array.setIfInBounds]

 theorem shared_field_source (unused : Term) (number : Nat) :
    Evaluates (.app
      (.lam (.binary .add (.get (.bound 0) "x") (.get (.bound 0) "x")))
      (.record [("x",.nat number),("unused",unused)])) (.nat (number+number)) := by
  let fields : List (String × Term) := [("x",.nat number),("unused",unused)]
  have field := Step.field fields "x" (.nat number) rfl
  have beta := Step.beta (.binary .add (.get (.bound 0) "x") (.get (.bound 0) "x")) (.record fields)
  have primitive := Step.primitive .add (.nat number) (.nat number) (.nat (number+number))
    (.natural _) (.natural _) rfl
  constructor
  · exact .next (by simpa [instantiate,Term.substitute,fields] using beta)
      (.next (.binaryLeft .add _ field)
        (.next (.binaryRight .add _ (.natural _) field) (.next primitive (.refl _))))
  · exact .natural _

/-- General tied Fix can return a ground target without demanding either
recursive self or inherited target. Both argument thunks stay suspended, while
the tied address is memoized in place with its retained unfolding origin. -/
 theorem fixed_constant_executor (inherited : Term) (number : Nat) :
    runBounded ⟨3,3⟩ 11 (initial (.fix (.lam (.lam (.nat number))) inherited)) =
    .finished (.natural number)
      ⟨#[.cached
          ⟨.app (.app (.lam (.lam (.nat number))) (.bound 0)) (inherited.rename Nat.succ),[0]⟩
          (.natural number),
        .suspended ⟨.bound 0,[0]⟩,
        .suspended ⟨inherited.rename Nat.succ,[0]⟩],.complete (.natural number),[]⟩ := by
  simp [runBounded,step,stepRaw,initial,Term.rename,
    Array.set!,Array.setIfInBounds]

 theorem fixed_constant_source (inherited : Term) (number : Nat) :
    Evaluates (.fix (.lam (.lam (.nat number))) inherited) (.nat number) := by
  constructor
  · have selfBeta := Step.beta (.lam (.nat number)) (.fix (.lam (.lam (.nat number))) inherited)
    have inheritedBeta := Step.beta (.nat number) inherited
    exact .next (.fix _ _) (.next (.application inherited (by
      simpa [instantiate,Term.substitute] using selfBeta)) (.next (by
        simpa [instantiate,Term.substitute] using inheritedBeta) (.refl _)))
  · exact .natural _

#assert_axioms graph_enter_suspended graph_cache_update graph_enter_cached
  graph_evaluate_application graph_closure_call graph_evaluate_fix graph_evaluate_context
  graph_evaluate_pair graph_evaluate_bound graph_evaluate_immediate graph_object_access
  graph_specification_call graph_primitive_return allocateFields_realizes graph_evaluate_record
  graph_field_return graph_evaluate_mix graph_condition_zero graph_condition_successor
  graph_extend_record graph_stepRaw rawRun_graph rawRun_natural_sound rawRun_boolean_sound
  rawRun_label_sound runBounded_finished_graph runBounded_natural_sound runBounded_boolean_sound
  runBounded_label_sound sourceStep_deterministic source_evaluates_unique
  runBounded_observation_sound runBounded_resource_independent sourceSteps_evaluates_tail
  stepRaw_originsBorn reachable_originsBorn stackRealizes_erases graph_complete_value_sound
  runBounded_value_sound graph_enteredFocus_source runBounded_observes_sound
  graph_complete_boolean_sound closeTerm_beta graph_binary_left_return graph_complete_return
  initial_fix_graph adequate_trace_execution adequate_trace_completion shared_field_executor
  shared_field_source fixed_constant_executor fixed_constant_source source_evaluates_iff_derivation
  sourceDerivation_cost_unique sourceStep_derivation_tail originBorn_demand_descent
  graph_terminating_demand administrative_budget_halts rawRun_terminating_administration
  runBounded_terminating_administration represented_born_blackhole_counterexample
  graph_stepRaw_names

/-- Finite actual traces construct coherent name assignments. Already allocated
source identities survive every prefix, including cached structured values;
only freshly allocated addresses acquire names. -/
 theorem rawRun_graphBy_names {meaning : AddressMeaning} {state : State} {source : Term} {ticks : Nat}
    (represented : GraphRepresentsBy meaning state source)
    (successful : ResultControl (rawRun ticks state).control) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ GraphRepresentsBy next (rawRun ticks state) source := by
  induction ticks generalizing state meaning with
  | zero => exact ⟨meaning,(fun _ _ => rfl),represented⟩
  | succ ticks ih =>
      have nextSuccessful : ResultControl (stepRaw state).control := rawRun_resultControl successful
      obtain ⟨middle,first,nextRepresented⟩ := graph_stepRaw_names represented nextSuccessful
      obtain ⟨next,rest,finalRepresented⟩ := ih nextRepresented successful
      refine ⟨next,?_,finalRepresented⟩
      intro address allocated
      exact (first address allocated).trans
        (rest address (Nat.lt_of_lt_of_le allocated (stepRaw_preservesOrigins state).1))

 theorem rawRun_named_graph {source : Term} (closed : Scoped 0 source) (ticks : Nat)
    (successful : ResultControl (rawRun ticks (initial source)).control) :
    ∃ meaning : AddressMeaning, GraphRepresentsBy meaning (rawRun ticks (initial source)) source := by
  obtain ⟨meaning,_,represented⟩ := rawRun_graphBy_names (graphBy_initializes closed) successful
  exact ⟨meaning,represented⟩

#assert_axioms rawRun_graphBy_names rawRun_named_graph

 theorem push_nonEvaluating_backward {heap : Array Cell} {cell : Cell} {address : Address} {origin : Closure}
    (notEvaluating : ∀ source, cell ≠ .evaluating source)
    (found : (heap.push cell)[address]? = some (.evaluating origin)) :
    heap[address]? = some (.evaluating origin) := by
  by_cases same : address = heap.size
  · subst address
    simp at found
    exact False.elim (notEvaluating origin found)
  · simpa [Array.getElem?_push,same] using found

 theorem allocateFields_evaluating_backward {heap : Array Cell} {environment : Environment}
    {fields : List (String × Term)} {address : Address} {origin : Closure}
    (found : (allocateFields heap environment fields).1[address]? = some (.evaluating origin)) :
    heap[address]? = some (.evaluating origin) := by
  induction fields generalizing heap with
  | nil => exact found
  | cons field fields ih =>
      rw [allocateFields_cons] at found
      exact push_nonEvaluating_backward (by intro source; cases source; simp) (ih found)

 theorem set_nonEvaluating_backward {heap : Array Cell} {target address : Address} {cell : Cell} {origin : Closure}
    (notEvaluating : ∀ source, cell ≠ .evaluating source)
    (found : (heap.set! target cell)[address]? = some (.evaluating origin)) :
    heap[address]? = some (.evaluating origin) := by
  by_cases allocated : target < heap.size
  · by_cases same : address = target
    · subst address
      simp [Array.set!,allocated] at found
      exact False.elim (notEvaluating origin found)
    · simpa [Array.set!,allocated,same,Ne.symm same] using found
  · simpa [Array.set!,Array.setIfInBounds,allocated] using found

/-- An evaluating phase can only survive from an existing evaluating cell or
be created by entering that exact suspended address. All actual allocations,
including tied Fix and cached predecessor allocation, are covered. -/
 theorem stepRaw_evaluating_birth {state : State} {address : Address} {origin : Closure}
    (found : (stepRaw state).heap[address]? = some (.evaluating origin)) :
    state.heap[address]? = some (.evaluating origin) ∨
      (state.control = .enter address ∧ state.heap[address]? = some (.suspended origin)) := by
  cases current : state.control with
  | complete value | refused reason | blackhole target | yielded _ => exact Or.inl (by simpa [stepRaw,current] using found)
  | enter target =>
      cases prior : state.heap[target]? with
      | none => exact Or.inl (by simpa [stepRaw,current,prior] using found)
      | some cell =>
          cases cell with
          | evaluating old | cached old value => exact Or.inl (by simpa [stepRaw,current,prior] using found)
          | suspended old =>
              have changed : (state.heap.set! target (.evaluating old))[address]? = some (.evaluating origin) := by
                simpa [stepRaw,current,prior] using found
              by_cases same : address = target
              · subst address
                have allocated := (Array.getElem?_eq_some_iff.mp prior).1
                simp [Array.set!,allocated] at changed
                subst old
                exact Or.inr ⟨rfl,prior⟩
              · exact Or.inl (by simpa [Array.set!,same,Ne.symm same] using changed)
  | evaluate term environment =>
      cases term <;> simp only [stepRaw,current] at found
      all_goals repeat' first | split at found
      all_goals first
        | exact Or.inl found
        | exact Or.inl (allocateFields_evaluating_backward found)
        | exact Or.inl (push_nonEvaluating_backward (by intro source; simp) found)
        | exact Or.inl (push_nonEvaluating_backward (by intro source; simp)
            (push_nonEvaluating_backward (by intro source; simp) found))
  | returned value =>
      cases frames : state.stack with
      | nil => exact Or.inl (by simpa [stepRaw,current,frames] using found)
      | cons frame rest =>
          cases frame <;> cases value <;> simp only [stepRaw,current,frames] at found
          all_goals repeat' first | split at found
          all_goals first
            | exact Or.inl found
            | exact Or.inl (allocateFields_evaluating_backward found)
            | exact Or.inl (push_nonEvaluating_backward (by intro source; simp) found)
            | exact Or.inl (set_nonEvaluating_backward (by intro source; simp) found)

/-- Every reachable evaluating cell has a real entry witness at its permanent
address and source origin. This rules out the unearned phase in the named
GraphRepresents/Born counterexample, independently of source termination. -/
 theorem reachable_evaluating_started {source : Term} {state : State} {address : Address} {origin : Closure}
    (reachable : Reachable (initial source) state)
    (found : state.heap[address]? = some (.evaluating origin)) :
    ∃ entered : State, Reachable (initial source) entered ∧ entered.control = .enter address ∧
      entered.heap[address]? = some (.suspended origin) := by
  induction reachable with
  | start => simp [initial] at found
  | next reachable ih =>
      rcases stepRaw_evaluating_birth found with existing | ⟨entered,suspended⟩
      · exact ih existing
      · exact ⟨_,reachable,entered,suspended⟩

#assert_axioms stepRaw_evaluating_birth reachable_evaluating_started

/-- An actual uninterrupted evaluating interval starts by entering this exact
suspended origin. Every later member is an actual transition still carrying
that same evaluating cell, rather than an assumed phase marker. -/
inductive EvaluatingSegment (address : Address) (origin : Closure) (entered : State) : State → Prop where
  | start : entered.control = .enter address → entered.heap[address]? = some (.suspended origin) →
      EvaluatingSegment address origin entered (stepRaw entered)
  | next {state : State} : EvaluatingSegment address origin entered state →
      (stepRaw state).heap[address]? = some (.evaluating origin) →
      EvaluatingSegment address origin entered (stepRaw state)

 theorem evaluatingSegment_reachable {address : Address} {origin : Closure} {entered state : State}
    (segment : EvaluatingSegment address origin entered state) : Reachable (stepRaw entered) state := by
  induction segment with
  | start _ _ => exact .start
  | next segment found ih => exact .next ih

 theorem evaluatingSegment_cell {address : Address} {origin : Closure} {entered state : State}
    (segment : EvaluatingSegment address origin entered state) : state.heap[address]? = some (.evaluating origin) := by
  cases segment with
  | start enter suspended =>
      have allocated := (Array.getElem?_eq_some_iff.mp suspended).1
      simp only [stepRaw,enter,suspended]
      simp [Array.set!,allocated]
  | next segment found => exact found

/-- Every actual reachable evaluating phase comes with an uninterrupted real
machine interval from its precise suspended closure entry. Combined with the
coherent assignment theorem, this is the phase-provenance input for proving
active-update budgets and excluding blackholes in terminating source runs. -/
 theorem reachable_evaluating_segment {source : Term} {state : State} {address : Address} {origin : Closure}
    (reachable : Reachable (initial source) state)
    (found : state.heap[address]? = some (.evaluating origin)) :
    ∃ entered : State, Reachable (initial source) entered ∧ entered.control = .enter address ∧
      entered.heap[address]? = some (.suspended origin) ∧ EvaluatingSegment address origin entered state := by
  induction reachable with
  | start => simp [initial] at found
  | next reachable ih =>
      rcases stepRaw_evaluating_birth found with existing | ⟨entered,suspended⟩
      · obtain ⟨entry,earlier,enter,old,segment⟩ := ih existing
        exact ⟨entry,earlier,enter,old,.next segment found⟩
      · exact ⟨_,reachable,entered,suspended,.start entered suspended⟩

#assert_axioms reachable_evaluating_segment

 theorem reachable_graphBy_names {start state : State} {source : Term} {meaning : AddressMeaning}
    (represented : GraphRepresentsBy meaning start source) (reachable : Reachable start state)
    (successful : ResultControl state.control) :
    ∃ next : AddressMeaning, SourceNamesAgree start meaning next ∧ GraphRepresentsBy next state source := by
  induction reachable with
  | start => exact ⟨meaning,(fun _ _ => rfl),represented⟩
  | @next before reachable ih =>
      have priorSuccessful : ResultControl before.control := rawRun_resultControl (ticks := 1) successful
      obtain ⟨middle,first,prior⟩ := ih priorSuccessful
      obtain ⟨next,last,current⟩ := graph_stepRaw_names prior successful
      refine ⟨next,?_,current⟩
      intro address allocated
      exact (first address allocated).trans
        (last address (Nat.lt_of_lt_of_le allocated (reachable_preservesOrigins reachable).1))

/-- Whole-source termination supplies a finite independent budget for EVERY
actual evaluating interval's entered source name and retained lexical origin.
The origin cost is bounded by its name cost, and is strictly smaller for tied
Fix; ordinary aliases instead capture only older addresses. The concrete
interval witness is derived from reachability, including faulty endpoints. -/
 theorem reachable_evaluating_budget {source result : Term} {state : State} {address : Address} {origin : Closure}
    (closed : Scoped 0 source) (terminates : Evaluates source result)
    (reachable : Reachable (initial source) state)
    (found : state.heap[address]? = some (.evaluating origin)) :
    ∃ (entered : State) (meaning : AddressMeaning) (value : Term) (nameCost originCost : Nat),
      Reachable (initial source) entered ∧ entered.control = .enter address ∧
      entered.heap[address]? = some (.suspended origin) ∧ EvaluatingSegment address origin entered state ∧
      GraphRepresentsBy meaning entered source ∧ SourceDerivation (meaning address) value nameCost ∧
      SourceDerivation (closeOrigin meaning origin) value originCost ∧ originCost ≤ nameCost ∧
      (EnvironmentValid address origin.environment ∨ originCost < nameCost) := by
  obtain ⟨entered,earlier,enter,suspended,segment⟩ := reachable_evaluating_segment reachable found
  have successful : ResultControl entered.control := by simp [enter,ResultControl]
  obtain ⟨meaning,_,represented⟩ := reachable_graphBy_names (graphBy_initializes closed) earlier successful
  have snapshot := represented
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp only [enter,controlMeaning,Option.some.injEq] at control
  subst focus
  obtain ⟨wholeCost,whole⟩ := source_evaluates_derivation
    (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
  obtain ⟨value,nameCost,demand,_⟩ := stack_derivation_demand whole
  have originSteps := (heap address _ suspended).1
  obtain ⟨originCost,originDemand,le⟩ := sourceSteps_derivation_tail originSteps demand
  have born := reachable_originsBorn closed earlier address _ suspended
  have descent : EnvironmentValid address origin.environment ∨ originCost < nameCost := by
    rcases originBorn_demand_descent born originSteps demand with captures | ⟨smaller,tail,less⟩
    · exact Or.inl captures
    · have aligned := sourceDerivation_cost_unique tail originDemand
      exact Or.inr (aligned ▸ less)
  exact ⟨entered,meaning,value,nameCost,originCost,earlier,enter,suspended,segment,snapshot,demand,originDemand,le,descent⟩

#assert_axioms reachable_graphBy_names reachable_evaluating_budget

 theorem evaluatingSegment_from_entry {address : Address} {origin : Closure} {entered state : State}
    (segment : EvaluatingSegment address origin entered state) : Reachable entered state := by
  induction segment with
  | start _ _ => exact .next .start
  | next segment found ih => exact .next ih

/-- The source budget earned at suspended entry survives in the coherent
assignment at the CURRENT evaluating phase. Captured origins and the same
address name retain their exact source term while other allocations occur. -/
 theorem reachable_evaluating_current_budget {source result : Term} {state : State} {address : Address} {origin : Closure}
    (closed : Scoped 0 source) (terminates : Evaluates source result)
    (reachable : Reachable (initial source) state) (successful : ResultControl state.control)
    (found : state.heap[address]? = some (.evaluating origin)) :
    ∃ (meaning : AddressMeaning) (value : Term) (nameCost originCost : Nat),
      GraphRepresentsBy meaning state source ∧ SourceDerivation (meaning address) value nameCost ∧
      SourceDerivation (closeOrigin meaning origin) value originCost ∧ originCost ≤ nameCost ∧
      (EnvironmentValid address origin.environment ∨ originCost < nameCost) := by
  obtain ⟨entered,priorMeaning,value,nameCost,originCost,earlier,enter,suspended,segment,prior,demand,originDemand,le,descent⟩ :=
    reachable_evaluating_budget closed terminates reachable found
  obtain ⟨meaning,same,current⟩ := reachable_graphBy_names prior (evaluatingSegment_from_entry segment) successful
  have allocated := (Array.getElem?_eq_some_iff.mp suspended).1
  have originValid : ClosureValid entered.heap.size origin := prior.1.1 address _ suspended
  have sourceEq : closeOrigin priorMeaning origin = closeOrigin meaning origin :=
    closeTerm_meaning_congr originValid.2 originValid.1 same
  refine ⟨meaning,value,nameCost,originCost,current,?_,?_,le,descent⟩
  · simpa only [←same address allocated] using demand
  · simpa only [←sourceEq] using originDemand

/-- Extract the genuine local source segment for an update anywhere in the
continuation. Inner updates retain their own local provenance while erasing
administrative boundaries from the demanded context. -/
 theorem stackRealizes_update_segment {meaning : AddressMeaning} {root focus : Term}
    {before after : List Frame} {address : Address}
    (realizes : StackRealizes meaning root focus (before ++ .update address::after)) :
    Steps (meaning address) (stackMeaning meaning before focus) := by
  induction before generalizing focus with
  | nil => exact realizes.1
  | cons frame before ih =>
      cases frame with
      | update other =>
          have head : Steps (meaning other) focus := realizes.1
          have rest := ih realizes.2
          exact sourceSteps_trans rest (sourceSteps_stack meaning before head)
      | argument _ _ | field _ | reflect | metadata | project | extend _ _
      | condition _ _ _ | binaryLeft _ _ _ | binaryRight _ _ | case _ _ | ifBool _ _ _ =>
          exact ih realizes

/-- Every active update bounds the current demanded source budget, derived
from its local continuation segment. This theorem allows intervening sharing
updates and arbitrary source contexts, rather than assuming an execution
oracle for the heap. -/
 theorem graphBy_pending_budget {meaning : AddressMeaning} {state : State} {source nameValue focus : Term}
    {address : Address} {before after : List Frame} {nameCost : Nat}
    (represented : GraphRepresentsBy meaning state source)
    (head : state.stack = before ++ .update address::after)
    (current : controlMeaning meaning state.control = some focus)
    (demand : SourceDerivation (meaning address) nameValue nameCost) :
    ∃ focusValue focusCost, SourceDerivation focus focusValue focusCost ∧ focusCost ≤ nameCost := by
  obtain ⟨_,_,_,_,_,other,control,stack⟩ := represented
  have aligned : other = focus := Option.some.inj (control.symm.trans current)
  subst other
  have segment := stackRealizes_update_segment (head ▸ stack)
  obtain ⟨contextCost,context,contextLe⟩ := sourceSteps_derivation_tail segment demand
  obtain ⟨value,cost,focusDemand,le⟩ := stack_derivation_demand context
  exact ⟨value,cost,focusDemand,Nat.le_trans le contextLe⟩

#assert_axioms reachable_evaluating_current_budget graphBy_pending_budget

/-- A cap for the exact addresses retained by the current lexical closure. -/
def captureCap : Environment → Nat
  | [] => 0
  | address::rest => max (address+1) (captureCap rest)

 theorem captureCap_le {environment : Environment} {cap : Nat}
    (captures : EnvironmentValid cap environment) : captureCap environment ≤ cap := by
  induction environment with
  | nil => exact Nat.zero_le _
  | cons address rest ih =>
      apply Nat.max_le.mpr
      exact ⟨Nat.succ_le_of_lt (captures address (List.mem_cons_self ..)),
        ih (fun reference member => captures reference (List.mem_cons_of_mem _ member))⟩

 theorem captureCap_valid (environment : Environment) : EnvironmentValid (captureCap environment) environment := by
  induction environment with
  | nil => simp [EnvironmentValid]
  | cons address rest ih =>
      intro reference member
      rcases List.mem_cons.mp member with equal | old
      · subst reference
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih reference old) (Nat.le_max_right _ _)

/-- Demand focus also exposes evaluating entry as its permanent name, so a
finite-budget active-update invariant can rule it out instead of silently
omitting the blackhole-producing state. -/
def budgetFocus (meaning : AddressMeaning) (state : State) : Option Term :=
  match state.control with
  | .enter address => match state.heap[address]? with
      | some (.suspended origin) => some (closeOrigin meaning origin)
      | some (.cached _ value) => some (valueMeaning meaning value)
      | some (.evaluating _) | none => some (meaning address)
  | control => controlMeaning meaning control

def budgetCap (state : State) : Nat :=
  match state.control with
  | .evaluate _ environment => captureCap environment
  | .enter address => match state.heap[address]? with
      | some (.suspended origin) => captureCap origin.environment
      | some (.cached _ _) => 0
      | some (.evaluating _) | none => address+1
  | _ => 0

/-- Universal partial-budget invariant: undemanded divergent names need no
finite evaluation. Every FINITE pending-name/current-demand pair satisfies
strict semantic decrease or equal-cost lexical cap confinement. -/
def DemandSafety (meaning : AddressMeaning) (state : State) : Prop :=
  ∀ (address : Address) (origin : Closure), state.heap[address]? = some (.evaluating origin) →
    ∀ (nameValue : Term) (nameCost : Nat), SourceDerivation (meaning address) nameValue nameCost →
      ∀ focus, budgetFocus meaning state = some focus →
        ∀ (focusValue : Term) (focusCost : Nat), SourceDerivation focus focusValue focusCost →
          focusCost < nameCost ∨ (focusCost = nameCost ∧ budgetCap state ≤ address)

 theorem initial_demandSafety (source : Term) (meaning : AddressMeaning) : DemandSafety meaning (initial source) := by
  intro address origin found
  simp [initial] at found

 theorem demandSafety_returned {meaning : AddressMeaning} {state : State} {value : RuntimeValue}
    (returned : state.control = .returned value) : DemandSafety meaning state := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have positive := sourceDerivation_cost_positive nameDemand
  simp only [budgetFocus,returned,controlMeaning,Option.some.injEq] at current
  subst focus
  obtain ⟨_,rfl⟩ := sourceDerivation_value_inv (valueMeaning_value meaning value) focusDemand
  by_cases greater : 1 < nameCost
  · exact Or.inl greater
  · right
    refine ⟨by omega,?_⟩
    simp [budgetCap,returned]

 theorem demandSafety_forbids_finite_reentry {meaning : AddressMeaning} {state : State} {address : Address} {origin : Closure}
    {value : Term} {cost : Nat} (safe : DemandSafety meaning state)
    (enter : state.control = .enter address) (busy : state.heap[address]? = some (.evaluating origin))
    (demand : SourceDerivation (meaning address) value cost) : False := by
  have focus : budgetFocus meaning state = some (meaning address) := by simp [budgetFocus,enter,busy]
  rcases safe address origin busy value cost demand (meaning address) focus value cost demand with less | ⟨equal,cap⟩
  · exact Nat.lt_irrefl _ less
  · have impossible : address+1 ≤ address := by simpa only [budgetCap,enter,busy] using cap
    exact Nat.not_succ_le_self _ impossible

/-- The real suspended→evaluating transition preserves active demand safety
and registers the newly active update with its source-origin budget. This
is general heap/closure preservation, including actual tied Fix origins. -/
 theorem stepRaw_demandSafety_enter_suspended {meaning : AddressMeaning} {state : State}
    {address : Address} {origin : Closure} (safe : DemandSafety meaning state)
    (heap : HeapRealizes meaning state.heap) (born : HeapOriginsBorn state.heap)
    (enter : state.control = .enter address) (suspended : state.heap[address]? = some (.suspended origin)) :
    DemandSafety meaning (stepRaw state) := by
  intro other old found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have focusEq : focus = closeOrigin meaning origin := by
    simpa only [budgetFocus,stepRaw,enter,suspended,controlMeaning,Option.some.injEq] using current.symm
  subst focus
  have oldFocus : budgetFocus meaning state = some (closeOrigin meaning origin) := by simp [budgetFocus,enter,suspended]
  have capEq : budgetCap (stepRaw state) = budgetCap state := by simp [budgetCap,stepRaw,enter,suspended]
  rcases stepRaw_evaluating_birth found with prior | ⟨entered,oldSuspended⟩
  · have previous := safe other old prior nameValue nameCost nameDemand _ oldFocus focusValue focusCost focusDemand
    simpa only [capEq] using previous
  · have addressEq : other = address := by rw [enter] at entered; exact (Control.enter.inj entered).symm
    subst other
    have originEq : old = origin := Cell.suspended.inj (Option.some.inj (oldSuspended.symm.trans suspended))
    subst old
    have originSteps := (heap address _ suspended).1
    have originBorn := born address _ suspended
    rcases originBorn_demand_descent originBorn originSteps nameDemand with captures | ⟨smaller,tail,less⟩
    · obtain ⟨smaller,tail,le⟩ := sourceSteps_derivation_tail originSteps nameDemand
      have aligned := sourceDerivation_cost_unique focusDemand tail
      have budgetLe : focusCost ≤ nameCost := aligned.symm ▸ le
      by_cases strict : focusCost < nameCost
      · exact Or.inl strict
      · right
        refine ⟨by omega,?_⟩
        simpa [budgetCap,stepRaw,enter,suspended] using captureCap_le captures
    · have aligned := sourceDerivation_cost_unique tail focusDemand
      exact Or.inl (aligned ▸ less)

#assert_axioms stepRaw_demandSafety_enter_suspended demandSafety_forbids_finite_reentry

 theorem budgetFocus_enter_steps {meaning : AddressMeaning} {state : State} {address : Address} {focus : Term}
    (heap : HeapRealizes meaning state.heap) (enter : state.control = .enter address)
    (current : budgetFocus meaning state = some focus) : Steps (meaning address) focus := by
  cases found : state.heap[address]? with
  | none => simp [budgetFocus,enter,found] at current; subst focus; exact .refl _
  | some cell =>
      cases cell with
      | evaluating origin => simp [budgetFocus,enter,found] at current; subst focus; exact .refl _
      | suspended origin =>
          simp [budgetFocus,enter,found] at current
          subst focus
          exact (heap address _ found).1
      | cached origin value =>
          simp [budgetFocus,enter,found] at current
          subst focus
          exact (heap address _ found).2.1

 theorem budgetCap_enter_bound {state : State} {address : Address}
    (born : HeapOriginsBorn state.heap) (enter : state.control = .enter address) : budgetCap state ≤ address+1 := by
  cases found : state.heap[address]? with
  | none => simp [budgetCap,enter,found]
  | some cell =>
      cases cell with
      | evaluating origin | cached origin value => simp [budgetCap,enter,found]
      | suspended origin =>
          simpa only [budgetCap,enter,found] using captureCap_le (originBorn_capture_bound (born address _ found))

/-- Bare lexical lookup preserves active source/capture safety. Suspended and
cached phases reduce source budget; every origin's cap is bounded by the
looked-up address, itself retained by the current environment. -/
 theorem stepRaw_demandSafety_bound {meaning : AddressMeaning} {state : State}
    {environment : Environment} {index address : Nat} (safe : DemandSafety meaning state)
    (heap : HeapRealizes meaning state.heap) (born : HeapOriginsBorn state.heap)
    (evaluate : state.control = .evaluate (.bound index) environment)
    (lookup : environment[index]? = some address) : DemandSafety meaning (stepRaw state) := by
  have nextEnter : (stepRaw state).control = .enter address := by simp [stepRaw,evaluate,lookup]
  have nextHeap : HeapRealizes meaning (stepRaw state).heap := by simpa [stepRaw,evaluate,lookup] using heap
  have nextBorn : HeapOriginsBorn (stepRaw state).heap := by simpa [stepRaw,evaluate,lookup] using born
  have closes : closeTerm meaning environment (.bound index) = meaning address := by
    cases environment with
    | nil => simp at lookup
    | cons reference references => simp [closeTerm,Term.substitute,environmentSubstitution,lookup]
  have oldFocus : budgetFocus meaning state = some (meaning address) := by simp [budgetFocus,evaluate,controlMeaning,closes]
  have capLe : budgetCap (stepRaw state) ≤ budgetCap state := by
    have addressCap : address+1 ≤ captureCap environment :=
      Nat.succ_le_of_lt (captureCap_valid environment address (List.mem_of_getElem? lookup))
    calc
      budgetCap (stepRaw state) ≤ address+1 := budgetCap_enter_bound nextBorn nextEnter
      _ ≤ captureCap environment := addressCap
      _ = budgetCap state := by simp [budgetCap,evaluate]
  intro other origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have oldFound : state.heap[other]? = some (.evaluating origin) := by simpa [stepRaw,evaluate,lookup] using found
  have enters := budgetFocus_enter_steps nextHeap nextEnter current
  have evaluated : Evaluates (meaning address) focusValue :=
    ⟨sourceSteps_trans enters (sourceDerivation_evaluates focusDemand).1,(sourceDerivation_evaluates focusDemand).2⟩
  obtain ⟨priorCost,priorDemand⟩ := source_evaluates_derivation evaluated
  obtain ⟨smaller,tail,le⟩ := sourceSteps_derivation_tail enters priorDemand
  have aligned := sourceDerivation_cost_unique focusDemand tail
  have budgetLe : focusCost ≤ priorCost := aligned.symm ▸ le
  rcases safe other origin oldFound nameValue nameCost nameDemand _ oldFocus focusValue priorCost priorDemand with less | ⟨equal,cap⟩
  · exact Or.inl (Nat.lt_of_le_of_lt budgetLe less)
  · by_cases strict : focusCost < nameCost
    · exact Or.inl strict
    · right
      exact ⟨by omega,Nat.le_trans capLe cap⟩

 theorem demandSafety_terminal {meaning : AddressMeaning} {state : State}
    (terminal : (∃ reason, state.control = .refused reason) ∨ (∃ address, state.control = .blackhole address)) :
    DemandSafety meaning state := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  rcases terminal with ⟨reason,refused⟩ | ⟨target,blackhole⟩
  · simp [budgetFocus,refused,controlMeaning] at current
  · simp [budgetFocus,blackhole,controlMeaning] at current

/-- EVERY actual administrative transition preserves active demand safety.
Explicit terminal faults remain classified; source termination plus earned
finite update budgets is used separately to exclude evaluating re-entry. -/
 theorem stepRaw_demandSafety_administrative {meaning : AddressMeaning} {state : State}
    (safe : DemandSafety meaning state) (heap : HeapRealizes meaning state.heap)
    (born : HeapOriginsBorn state.heap) (administrative : DemandAdministrative state) :
    DemandSafety meaning (stepRaw state) := by
  cases current : state.control with
  | enter address =>
      cases found : state.heap[address]? with
      | none => exact demandSafety_terminal (Or.inl ⟨.missingCell,by simp [stepRaw,current,found]⟩)
      | some cell =>
          cases cell with
          | suspended origin => exact stepRaw_demandSafety_enter_suspended safe heap born current found
          | cached origin value => exact demandSafety_returned (value := value) (by simp [stepRaw,current,found])
          | evaluating origin => exact demandSafety_terminal (Or.inr ⟨address,by simp [stepRaw,current,found]⟩)
  | evaluate term environment =>
      cases term <;> try simp [DemandAdministrative,current] at administrative
      case bound index =>
        cases lookup : environment[index]? with
        | none => exact demandSafety_terminal (Or.inl ⟨.unbound,by simp [stepRaw,current,lookup]⟩)
        | some address => exact stepRaw_demandSafety_bound safe heap born current lookup
  | returned value | complete value | refused reason | blackhole address | yielded _ => simp [DemandAdministrative,current] at administrative

#assert_axioms stepRaw_demandSafety_administrative stepRaw_demandSafety_bound

 theorem frame_derivation_demand_strict {meaning : AddressMeaning} {frame : Frame} {focus result : Term} {cost : Nat}
    (ordinary : ∀ address, frame ≠ .update address)
    (derivation : SourceDerivation (frameMeaning meaning frame focus) result cost) :
    ∃ value demandCost, SourceDerivation focus value demandCost ∧ demandCost < cost := by
  cases frame with
  | update address => exact False.elim (ordinary address rfl)
  | argument term environment =>
      cases derivation with
      | value value => cases value
      | applicationLambda first second => exact ⟨_,_,first,by omega⟩
      | applicationSpecification first second => exact ⟨_,_,first,by omega⟩
  | field name =>
      cases derivation with
      | value value => cases value
      | field first found second => exact ⟨_,_,first,by omega⟩
  | reflect =>
      cases derivation with
      | value value => cases value
      | reflect first second => exact ⟨_,_,first,by omega⟩
  | metadata =>
      cases derivation with
      | value value => cases value
      | metadata first second => exact ⟨_,_,first,by omega⟩
  | project =>
      cases derivation with
      | value value => cases value
      | project first second => exact ⟨_,_,first,by omega⟩
  | extend fields environment =>
      cases derivation with
      | value value => cases value
      | extend first => exact ⟨_,_,first,by omega⟩
  | condition zero body environment =>
      cases derivation with
      | value value => cases value
      | zero first second => exact ⟨_,_,first,by omega⟩
      | successor first second => exact ⟨_,_,first,by omega⟩
  | binaryLeft primitive right environment =>
      cases derivation with
      | value value => cases value
      | binary first second found => exact ⟨_,_,first,by omega⟩
  | binaryRight primitive left =>
      cases derivation with
      | value value => cases value
      | binary first second found => exact ⟨_,_,second,by omega⟩
  | case arms environment =>
      cases derivation with
      | value value => cases value
      | case first found second => exact ⟨_,_,first,by omega⟩
  | ifBool whenTrue whenFalse environment =>
      cases derivation with
      | value value => cases value
      | ifTrue first second => exact ⟨_,_,first,by omega⟩
      | ifFalse first second => exact ⟨_,_,first,by omega⟩

 theorem stackUpdates_member_split {stack : List Frame} {address : Address}
    (member : address ∈ stackUpdates stack) :
    ∃ before after, stack = before ++ .update address::after := by
  induction stack with
  | nil => simp [stackUpdates] at member
  | cons frame rest ih =>
      by_cases update : ∃ other, frame = .update other
      · obtain ⟨other,eq⟩ := update
        subst frame
        rcases List.mem_cons.mp member with same | later
        · subst address; exact ⟨[],rest,rfl⟩
        · obtain ⟨before,after,eq⟩ := ih later
          exact ⟨.update other::before,after,by simp [eq]⟩
      · have later : address ∈ stackUpdates rest := by
          cases frame <;> simp_all [stackUpdates]
        obtain ⟨before,after,eq⟩ := ih later
        exact ⟨frame::before,after,by simp [eq]⟩

 theorem budgetFocus_control_steps {meaning : AddressMeaning} {state : State} {before focus : Term}
    (heap : HeapRealizes meaning state.heap)
    (control : controlMeaning meaning state.control = some before)
    (current : budgetFocus meaning state = some focus) : Steps before focus := by
  cases actual : state.control with
  | enter address =>
      simp only [actual,controlMeaning,Option.some.injEq] at control
      subst before
      exact budgetFocus_enter_steps heap actual current
  | evaluate term environment | returned value | complete value | refused reason | blackhole address | yielded _ =>
      have aligned : before = focus := by
        apply Option.some.inj
        exact control.symm.trans (by simpa only [budgetFocus,actual] using current)
      subst focus
      exact .refl _

/-- Any actual graph with a demanding continuation at its head is safe: the
head's child consumes strictly less budget than every enclosing active update.
This is a general semantic consequence for all eight lazy demand contexts. -/
 theorem graphBy_nonUpdate_head_demandSafety {meaning : AddressMeaning} {state : State} {source : Term}
    {frame : Frame} {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (head : state.stack = frame::rest) (ordinary : ∀ address, frame ≠ .update address) : DemandSafety meaning state := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have busy := represented.2.1
  have member := busy.2 address |>.mpr ⟨origin,found⟩
  have restMember : address ∈ stackUpdates rest := by
    rw [head] at member
    cases frame <;> try exact member
    case update other => exact False.elim (ordinary other rfl)
  obtain ⟨before,after,split⟩ := stackUpdates_member_split restMember
  obtain ⟨_,_,_,_,heap,oldFocus,control,stack⟩ := represented
  have localHead : state.stack = (frame::before) ++ .update address::after := by simp [head,split]
  have segment := stackRealizes_update_segment (localHead ▸ stack)
  obtain ⟨contextCost,context,contextLe⟩ := sourceSteps_derivation_tail segment nameDemand
  obtain ⟨middle,middleCost,middleDerivation,middleLe⟩ := stack_derivation_demand (stack := before) context
  obtain ⟨child,childCost,childDerivation,childLt⟩ := frame_derivation_demand_strict ordinary middleDerivation
  have focused := budgetFocus_control_steps heap control current
  obtain ⟨actualCost,actualDerivation,actualLe⟩ := sourceSteps_derivation_tail focused childDerivation
  have aligned := sourceDerivation_cost_unique focusDemand actualDerivation
  have below : actualCost < nameCost :=
    Nat.lt_of_le_of_lt actualLe (Nat.lt_of_lt_of_le childLt (Nat.le_trans middleLe contextLe))
  exact Or.inl (aligned.symm ▸ below)

/-- General application/object/field/extension/condition/primitive demand
dispatch constructs the actual next named graph AND active-update safety.
No finite-source or evaluator oracle is a premise. -/
 theorem graph_evaluate_context_safety {meaning : AddressMeaning} {state : State} {source hole : Term}
    {context : DemandContext} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (context.term hole) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current⟩ := graph_evaluate_context_names represented evaluate
  refine ⟨next,same,current,?_⟩
  apply graphBy_nonUpdate_head_demandSafety current
    (frame := context.frame environment) (rest := state.stack)
  · simp only [demandContext_dispatch evaluate]
  · intro address
    cases context <;> simp [DemandContext.frame]

#assert_axioms graphBy_nonUpdate_head_demandSafety graph_evaluate_context_safety


/-- A genuine source reduction after an actual continuation prefix makes the
next demand strictly smaller than every surviving active update. Allocation
may change future names; the actual old heap prefix retains its assignment. -/
 theorem graphBy_semantic_reduction_demandSafety {meaning next : AddressMeaning}
    {state : State} {source before after : Term} {consumed : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (same : SourceNamesAgree state meaning next)
    (representedNext : GraphRepresentsBy next (stepRaw state) source)
    (noEnter : ∀ address, state.control ≠ .enter address)
    (head : state.stack = consumed ++ (stepRaw state).stack)
    (oldControl : controlMeaning meaning state.control = some before)
    (newControl : controlMeaning next (stepRaw state).control = some after)
    (reduce : Step (stackMeaning meaning consumed before) after) :
    DemandSafety next (stepRaw state) := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have oldFound : state.heap[address]? = some (.evaluating origin) := by
    rcases stepRaw_evaluating_birth found with old | ⟨entered,_⟩
    · exact old
    · exact False.elim (noEnter address entered)
  have oldDemand : SourceDerivation (meaning address) nameValue nameCost := by
    rw [same address (Array.getElem?_eq_some_iff.mp oldFound).1]
    exact nameDemand
  have busy := representedNext.2.1
  have member := busy.2 address |>.mpr ⟨origin,found⟩
  obtain ⟨frames,rest,split⟩ := stackUpdates_member_split member
  have oldHead : state.stack = (consumed ++ frames) ++ .update address::rest := by
    rw [head,split,List.append_assoc]
  obtain ⟨_,_,_,_,_,oldFocus,control,stack⟩ := represented
  have aligned : oldFocus = before := Option.some.inj (control.symm.trans oldControl)
  subst oldFocus
  have segment := stackRealizes_update_segment (oldHead ▸ stack)
  have contextEq : stackMeaning meaning (consumed ++ frames) before =
      stackMeaning meaning frames (stackMeaning meaning consumed before) := by
    simp [stackMeaning,List.foldl_append]
  rw [contextEq] at segment
  obtain ⟨contextCost,context,contextLe⟩ := sourceSteps_derivation_tail segment oldDemand
  obtain ⟨middle,middleCost,middleDerivation,middleLe⟩ := stack_derivation_demand (stack := frames) context
  obtain ⟨childCost,childDerivation,childLt⟩ := sourceStep_derivation_tail reduce middleDerivation
  have focused := budgetFocus_control_steps representedNext.2.2.2.2.1 newControl current
  obtain ⟨actualCost,actualDerivation,actualLe⟩ := sourceSteps_derivation_tail focused childDerivation
  have costEq := sourceDerivation_cost_unique focusDemand actualDerivation
  have below : actualCost < nameCost :=
    Nat.lt_of_le_of_lt actualLe (Nat.lt_of_lt_of_le childLt (Nat.le_trans middleLe contextLe))
  exact Or.inl (costEq.symm ▸ below)

 theorem graph_object_access_safety {meaning : AddressMeaning} {state : State} {source : Term}
    {access : ObjectAccess} {first second : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (access.value first second))
    (head : state.stack = access.frame::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,consumed,before,after,oldControl,newControl,split,reduce⟩ :=
    graph_object_access_execution represented returned head
  refine ⟨next,same,current,?_⟩
  exact graphBy_semantic_reduction_demandSafety represented same current
    (by intro address; simp [returned]) split oldControl newControl reduce

#assert_axioms graphBy_semantic_reduction_demandSafety graph_object_access_safety


 theorem graph_execution_demandSafety {meaning next : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (same : SourceNamesAgree state meaning next)
    (current : GraphRepresentsBy next (stepRaw state) source)
    (noEnter : ∀ address, state.control ≠ .enter address)
    (dispatch : SourceDispatch meaning next state) : DemandSafety next (stepRaw state) := by
  obtain ⟨consumed,before,after,oldControl,newControl,split,reduce⟩ := dispatch
  exact graphBy_semantic_reduction_demandSafety represented same current noEnter split oldControl newControl reduce

 theorem graph_evaluate_mix_safety {meaning : AddressMeaning} {state : State} {source lower upper : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_evaluate_mix_execution represented evaluate
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [evaluate]) dispatch⟩

 theorem graph_evaluate_done_safety {meaning : AddressMeaning} {state : State} {source value : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.done value) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_evaluate_done_execution represented evaluate
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [evaluate]) dispatch⟩

 theorem graph_closure_call_safety {meaning : AddressMeaning} {state : State} {source body argument : Term}
    {captured environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.closure body captured))
    (head : state.stack = .argument argument environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_closure_call_execution represented returned head
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

 theorem graph_condition_zero_safety {meaning : AddressMeaning} {state : State} {source zero body : Term}
    {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.natural 0))
    (head : state.stack = .condition zero body environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_condition_zero_execution represented returned head
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

 theorem graph_condition_successor_safety {meaning : AddressMeaning} {state : State} {source zero body : Term}
    {environment : Environment} {rest : List Frame} {number : Nat}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.natural (number+1)))
    (head : state.stack = .condition zero body environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_condition_successor_execution represented returned head
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

 theorem graph_field_return_safety {meaning : AddressMeaning} {state : State} {source : Term}
    {fields : List (String × Address)} {name key : String} {address : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.record fields))
    (head : state.stack = .field name::rest)
    (found : fields.find? (fun field => field.1 == name) = some (key,address)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_field_return_execution represented returned head found
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

/-- A tied thunk's actual source origin contains its own permanent source name
properly. Entering that origin therefore strictly reduces every finite pending
update budget, even though the heap graph itself is cyclic. -/
 theorem graphBy_enter_tied_demandSafety {meaning : AddressMeaning} {state : State} {source spec inherited : Term}
    {address : Address} {captured : Environment}
    (represented : GraphRepresentsBy meaning state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.suspended
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),address::captured⟩)) :
    DemandSafety meaning state := by
  intro other origin busyFound nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have focusEq : focus = closeOrigin meaning
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),address::captured⟩ := by
    simpa [budgetFocus,enter,found] using current.symm
  subst focus
  have member := represented.2.1.2 other |>.mpr ⟨origin,busyFound⟩
  obtain ⟨before,after,split⟩ := stackUpdates_member_split member
  have fixed : controlMeaning meaning state.control = some (meaning address) := by simp [controlMeaning,enter]
  obtain ⟨result,cost,demand,le⟩ := graphBy_pending_budget represented split fixed nameDemand
  have heap := represented.2.2.2.2.1
  have sourceOrigin := (heap address _ found).1
  have proper := tiedOrigin_name_proper meaning address spec inherited captured
  have different : meaning address ≠ closeOrigin meaning
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),address::captured⟩ := by
    intro equal; rw [equal] at proper; exact Nat.lt_irrefl _ proper
  obtain ⟨smaller,tail,less⟩ := sourceSteps_derivation_strict sourceOrigin different demand
  have aligned := sourceDerivation_cost_unique focusDemand tail
  exact Or.inl (aligned.symm ▸ Nat.lt_of_lt_of_le less le)

 theorem graph_evaluate_fix_safety {meaning : AddressMeaning} {state : State} {source spec inherited : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.fix spec inherited) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current⟩ := graph_evaluate_fix_names represented evaluate
  refine ⟨next,same,current,?_⟩
  apply graphBy_enter_tied_demandSafety current
    (address := state.heap.size) (spec := spec) (inherited := inherited) (captured := environment)
  · simp [stepRaw,evaluate]
  · simp [stepRaw,evaluate]

#assert_axioms graph_closure_call_safety graph_condition_successor_safety
  graphBy_enter_tied_demandSafety graph_evaluate_fix_safety


 theorem budgetFocus_meaning_congr {meaning next : AddressMeaning} {state : State}
    (lexical : LexicalInvariant state) (same : ∀ address, address < state.heap.size → meaning address = next address) :
    budgetFocus meaning state = budgetFocus next state := by
  cases control : state.control with
  | evaluate term environment =>
      have valid : ClosureValid state.heap.size ⟨term,environment⟩ := by simpa [control,ControlValid] using lexical.2.1
      simp only [budgetFocus,control,controlMeaning,closeTerm_meaning_congr valid.2 valid.1 same]
  | returned value | complete value =>
      have valid : RuntimeValueValid state.heap.size value := by simpa [control,ControlValid] using lexical.2.1
      simp only [budgetFocus,control,controlMeaning,valueMeaning_congr valid same]
  | refused reason | blackhole address => simp [budgetFocus,control,controlMeaning]
  | yielded plan =>
      have allocated : plan < state.heap.size := by simpa [control,ControlValid] using lexical.2.1
      simp only [budgetFocus,control,controlMeaning,same plan allocated]
  | enter address =>
      have allocated : address < state.heap.size := by simpa [control,ControlValid] using lexical.2.1
      cases found : state.heap[address]? with
      | none => simp [budgetFocus,control,found,same address allocated]
      | some cell =>
          have valid := lexical.1 address cell found
          cases cell with
          | suspended origin =>
              simp only [CellValid] at valid
              simp only [budgetFocus,control,found,closeOrigin,closeTerm_meaning_congr valid.2 valid.1 same]
          | cached origin value =>
              simp only [CellValid] at valid
              simp only [budgetFocus,control,found,valueMeaning_congr valid.2 same]
          | evaluating origin => simp [budgetFocus,control,found,same address allocated]

 theorem demandSafety_meaning_congr {meaning next : AddressMeaning} {state : State}
    (lexical : LexicalInvariant state) (same : ∀ address, address < state.heap.size → meaning address = next address)
    (safe : DemandSafety meaning state) : DemandSafety next state := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have oldDemand : SourceDerivation (meaning address) nameValue nameCost := by
    rw [same address (Array.getElem?_eq_some_iff.mp found).1]; exact nameDemand
  have oldFocus : budgetFocus meaning state = some focus := (budgetFocus_meaning_congr lexical same).trans current
  exact safe address origin found nameValue nameCost oldDemand focus oldFocus focusValue focusCost focusDemand

#assert_axioms demandSafety_meaning_congr


 theorem demandSafety_complete {meaning : AddressMeaning} {state : State} {value : RuntimeValue}
    (complete : state.control = .complete value) : DemandSafety meaning state := by
  intro address origin found nameValue nameCost nameDemand focus current focusValue focusCost focusDemand
  have positive := sourceDerivation_cost_positive nameDemand
  simp only [budgetFocus,complete,controlMeaning,Option.some.injEq] at current
  subst focus
  obtain ⟨_,rfl⟩ := sourceDerivation_value_inv (valueMeaning_value meaning value) focusDemand
  by_cases greater : 1 < nameCost
  · exact Or.inl greater
  · right; refine ⟨by omega,?_⟩; simp [budgetCap,complete]

 theorem graph_next_returned_safety {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (returned : ∃ value, (stepRaw state).control = .returned value) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨value,returned⟩ := returned
  obtain ⟨next,same,current⟩ := graph_stepRaw_names represented successful
  exact ⟨next,same,current,demandSafety_returned returned⟩

 theorem graph_next_complete_safety {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (complete : ∃ value, (stepRaw state).control = .complete value) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨value,complete⟩ := complete
  obtain ⟨next,same,current⟩ := graph_stepRaw_names represented successful
  exact ⟨next,same,current,demandSafety_complete complete⟩

 theorem graph_next_ordinary_safety {meaning : AddressMeaning} {state : State} {source : Term} {frame : Frame} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (head : (stepRaw state).stack = frame::rest) (ordinary : ∀ address, frame ≠ .update address) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current⟩ := graph_stepRaw_names represented successful
  exact ⟨next,same,current,graphBy_nonUpdate_head_demandSafety current head ordinary⟩

 theorem graph_administrative_safety {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (safe : DemandSafety meaning state)
    (born : HeapOriginsBorn state.heap) (successful : ResultControl (stepRaw state).control)
    (administrative : DemandAdministrative state) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  have unchanged : (stepRaw state).heap.size = state.heap.size := by
    cases control : state.control with
    | enter address =>
        cases found : state.heap[address]? with
        | none => simp [stepRaw,control,found]
        | some cell => cases cell <;> simp [stepRaw,control,found]
    | evaluate term environment =>
        cases term <;> try simp [DemandAdministrative,control] at administrative
        case bound index =>
          cases found : environment[index]? <;> simp [stepRaw,control,found]
    | returned value | complete value | refused reason | blackhole address | yielded _ => simp [DemandAdministrative,control] at administrative
  obtain ⟨next,same,current⟩ := graph_stepRaw_names represented successful
  have agreement : ∀ address, address < (stepRaw state).heap.size → meaning address = next address := by
    intro address allocated; rw [unchanged] at allocated; exact same address allocated
  exact ⟨next,same,current,demandSafety_meaning_congr current.1 agreement
    (stepRaw_demandSafety_administrative safe represented.2.2.2.2.1 born administrative)⟩

/-- Every running/finished actual raw transition preserves the named graph
and active finite-demand safety, including cyclic Fix allocation and sharing.
Fault exclusion is a separate source-termination consequence. -/
 theorem graph_case_return_safety {meaning : AddressMeaning} {state : State} {source body : Term}
    {arms : List (String × Term)} {environment : Environment} {tag key : String} {payload : Address}
    {rest : List Frame} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.variant tag payload))
    (head : state.stack = .case arms environment::rest)
    (found : arms.find? (fun arm => arm.1 == tag) = some (key,body)) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_case_return_execution represented returned head found
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

 theorem graph_ifBool_return_safety {meaning : AddressMeaning} {state : State} {source whenTrue whenFalse : Term}
    {environment : Environment} {rest : List Frame} {value : Bool} (represented : GraphRepresentsBy meaning state source)
    (returned : state.control = .returned (.boolean value))
    (head : state.stack = .ifBool whenTrue whenFalse environment::rest) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  obtain ⟨next,same,current,dispatch⟩ := graph_ifBool_return_execution represented returned head
  exact ⟨next,same,current,graph_execution_demandSafety represented same current (by intro address; simp [returned]) dispatch⟩

 theorem graph_stepRaw_safety_names {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (safe : DemandSafety meaning state)
    (born : HeapOriginsBorn state.heap) (successful : ResultControl (stepRaw state).control) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (stepRaw state) source ∧ DemandSafety next (stepRaw state) := by
  cases control : state.control with
  | complete value => exact graph_next_complete_safety represented successful (by simp [stepRaw,control])
  | refused reason | blackhole address | yielded _ =>
      simp [stepRaw,control,ResultControl] at successful
  | enter address =>
      cases found : state.heap[address]? with
      | none => simp [stepRaw,control,found,ResultControl] at successful
      | some cell =>
          cases cell with
          | suspended origin => exact graph_administrative_safety represented safe born successful (by simp [DemandAdministrative,control])
          | cached origin value => exact graph_next_returned_safety represented successful (by simp [stepRaw,control,found])
          | evaluating origin => simp [stepRaw,control,found,ResultControl] at successful
  | evaluate term environment =>
      cases term with
      | bound index =>
          cases found : environment[index]? with
          | none => simp [stepRaw,control,found,ResultControl] at successful
          | some address => exact graph_administrative_safety represented safe born successful (by simp [DemandAdministrative,control])
      | lam body => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | nat number => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | boolean value => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | label name => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | app function argument => exact graph_evaluate_context_safety (context := .argument argument) represented control
      | mix lower upper => exact graph_evaluate_mix_safety represented control
      | fix spec inherited => exact graph_evaluate_fix_safety represented control
      | specification descriptor extension => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | prototype spec target => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | record fields => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | reflect term => exact graph_evaluate_context_safety (context := .reflect) represented control
      | metadata term => exact graph_evaluate_context_safety (context := .metadata) represented control
      | project term => exact graph_evaluate_context_safety (context := .project) represented control
      | get target name => exact graph_evaluate_context_safety (context := .field name) represented control
      | extend inherited fields => exact graph_evaluate_context_safety (context := .extend fields) represented control
      | ifZero value zero body => exact graph_evaluate_context_safety (context := .condition zero body) represented control
      | binary primitive left right => exact graph_evaluate_context_safety (context := .binary primitive right) represented control
      | inject tag payload => exact graph_next_returned_safety represented successful (by simp [stepRaw,control])
      | case scrutinee arms => exact graph_evaluate_context_safety (context := .case arms) represented control
      | ifBool condition whenTrue whenFalse =>
          exact graph_evaluate_context_safety (context := .ifBool whenTrue whenFalse) represented control
      | perform plan =>
          cases shared : forcingShared state.stack <;> simp [stepRaw,control,shared,ResultControl] at successful
      | done value => exact graph_evaluate_done_safety represented control
  | returned value =>
      cases frames : state.stack with
      | nil => exact graph_next_complete_safety represented successful (by simp [stepRaw,control,frames])
      | cons frame rest =>
          cases frame with
          | update address => 
              obtain ⟨origin,found⟩ := busy_update_exists represented.2.1 frames
              exact graph_next_returned_safety represented successful (by simp [stepRaw,control,frames,found])
          | argument argument environment =>
              cases value with
              | closure body captured => exact graph_closure_call_safety represented control frames
              | specification descriptor extension =>
                  exact graph_next_ordinary_safety represented successful
                    (frame := .argument argument environment) (rest := rest)
                    (by simp [stepRaw,control,frames]) (by intro address; simp)
              | natural _ | boolean _ | label _ | record _ | prototype _ _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | reflect =>
              cases value with
              | prototype spec target => exact graph_object_access_safety (access := .reflect) represented control frames
              | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | metadata =>
              cases value with
              | specification descriptor extension => exact graph_object_access_safety (access := .metadata) represented control frames
              | closure _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | project =>
              cases value with
              | prototype spec target => exact graph_object_access_safety (access := .project) represented control frames
              | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | field name =>
              cases value with
              | record fields =>
                  cases found : fields.find? (fun field => field.1 == name) with
                  | none => simp [stepRaw,control,frames,found,ResultControl] at successful
                  | some field =>
                      obtain ⟨key,address⟩ := field
                      exact graph_field_return_safety represented control frames found
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | extend fields environment =>
              cases value with
              | record inherited => exact graph_next_returned_safety represented successful (by simp [stepRaw,control,frames])
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | condition zero body environment =>
              cases value with
              | natural number =>
                  cases number with
                  | zero => exact graph_condition_zero_safety represented control frames
                  | succ number => exact graph_condition_successor_safety represented control frames
              | closure _ _ | specification _ _ | prototype _ _ | record _ | boolean _ | label _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | binaryLeft primitive right environment =>
              exact graph_next_ordinary_safety represented successful
                (frame := .binaryRight primitive value) (rest := rest)
                (by simp [stepRaw,control,frames]) (by intro address; simp)
          | binaryRight primitive left =>
              cases dispatch : (valueTerm left).bind (fun l => (valueTerm value).bind (primitiveResult primitive l)) with
              | none => simp [stepRaw,control,frames,dispatch,ResultControl] at successful
              | some result =>
                  cases scalar : scalarValue result with
                  | none => simp [stepRaw,control,frames,dispatch,scalar,ResultControl] at successful
                  | some next => exact graph_next_returned_safety represented successful (by simp [stepRaw,control,frames,dispatch,scalar])
          | case arms environment =>
              cases value with
              | variant tag payload =>
                  cases found : arms.find? (fun arm => arm.1 == tag) with
                  | none => simp [stepRaw,control,frames,found,ResultControl] at successful
                  | some arm =>
                      obtain ⟨key,body⟩ := arm
                      exact graph_case_return_safety represented control frames found
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | ifBool whenTrue whenFalse environment =>
              cases value with
              | boolean value => exact graph_ifBool_return_safety represented control frames
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful


#assert_axioms graph_stepRaw_safety_names


 theorem rawRun_graphBy_safety_names {meaning : AddressMeaning} {state : State} {source : Term} {ticks : Nat}
    (represented : GraphRepresentsBy meaning state source) (safe : DemandSafety meaning state)
    (born : HeapOriginsBorn state.heap) (successful : ResultControl (rawRun ticks state).control) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧
      GraphRepresentsBy next (rawRun ticks state) source ∧ DemandSafety next (rawRun ticks state) := by
  induction ticks generalizing state meaning with
  | zero => exact ⟨meaning,(fun _ _ => rfl),represented,safe⟩
  | succ ticks ih =>
      have nextSuccessful : ResultControl (stepRaw state).control := rawRun_resultControl successful
      obtain ⟨middle,first,nextRepresented,nextSafe⟩ := graph_stepRaw_safety_names represented safe born nextSuccessful
      have nextBorn := stepRaw_originsBorn represented.1 born
      obtain ⟨next,rest,finalRepresented,finalSafe⟩ := ih nextRepresented nextSafe nextBorn successful
      refine ⟨next,?_,finalRepresented,finalSafe⟩
      intro address allocated
      exact (first address allocated).trans
        (rest address (Nat.lt_of_lt_of_le allocated (stepRaw_preservesOrigins state).1))

/-- Closed source initialization earns the active-update invariant for every
actual running/finished prefix. No heap representation or safety oracle is a
premise, and undemanded divergent fields remain permitted. -/
 theorem rawRun_closed_demandSafety {source : Term} (closed : Scoped 0 source) (ticks : Nat)
    (successful : ResultControl (rawRun ticks (initial source)).control) :
    ∃ meaning : AddressMeaning, GraphRepresentsBy meaning (rawRun ticks (initial source)) source ∧
      DemandSafety meaning (rawRun ticks (initial source)) := by
  obtain ⟨meaning,_,current,safe⟩ := rawRun_graphBy_safety_names (graphBy_initializes closed)
    (initial_demandSafety source _) (initial_originsBorn source) successful
  exact ⟨meaning,current,safe⟩

 theorem graphBy_terminating_control_budget {meaning : AddressMeaning} {state : State} {source result focus : Term}
    (represented : GraphRepresentsBy meaning state source) (terminates : Evaluates source result)
    (control : controlMeaning meaning state.control = some focus) :
    ∃ value cost, SourceDerivation focus value cost := by
  obtain ⟨_,_,_,_,_,before,actual,stack⟩ := represented
  have aligned : before = focus := Option.some.inj (actual.symm.trans control)
  subst before
  have residual := sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates
  obtain ⟨cost,whole⟩ := source_evaluates_derivation residual
  obtain ⟨value,demandCost,demand,_⟩ := stack_derivation_demand whole
  exact ⟨value,demandCost,demand⟩

 theorem graphBy_terminating_reentry_impossible {meaning : AddressMeaning} {state : State} {source result : Term}
    {address : Address} {origin : Closure} (represented : GraphRepresentsBy meaning state source)
    (safe : DemandSafety meaning state) (terminates : Evaluates source result)
    (enter : state.control = .enter address) (busy : state.heap[address]? = some (.evaluating origin)) : False := by
  obtain ⟨value,cost,demand⟩ := graphBy_terminating_control_budget represented terminates
    (show controlMeaning meaning state.control = some (meaning address) by simp [controlMeaning,enter])
  exact demandSafety_forbids_finite_reentry safe enter busy demand

/-- A terminating independent closed source cannot re-enter any actually
busy thunk at any running prefix of the real graph executor, including tied
Fix. The named graph and safety proof are constructed by the actual trace. -/
 theorem rawRun_terminating_reentry_impossible {source result : Term} {ticks : Nat}
    {address : Address} {origin : Closure} (closed : Scoped 0 source) (terminates : Evaluates source result)
    (enter : (rawRun ticks (initial source)).control = .enter address)
    (busy : (rawRun ticks (initial source)).heap[address]? = some (.evaluating origin)) : False := by
  have successful : ResultControl (rawRun ticks (initial source)).control := by simp [ResultControl,enter]
  obtain ⟨meaning,represented,safe⟩ := rawRun_closed_demandSafety closed ticks successful
  exact graphBy_terminating_reentry_impossible represented safe terminates enter busy

#assert_axioms rawRun_closed_demandSafety rawRun_terminating_reentry_impossible


 theorem reachable_closed_demandSafety {source : Term} {state : State} (closed : Scoped 0 source)
    (reachable : Reachable (initial source) state) (successful : ResultControl state.control) :
    ∃ meaning : AddressMeaning, GraphRepresentsBy meaning state source ∧ DemandSafety meaning state := by
  induction reachable with
  | start => exact ⟨_,graphBy_initializes closed,initial_demandSafety source _⟩
  | @next before path ih =>
      have priorSuccessful : ResultControl before.control := rawRun_resultControl (ticks := 1) successful
      obtain ⟨meaning,represented,safe⟩ := ih priorSuccessful
      obtain ⟨next,_,current,nextSafe⟩ := graph_stepRaw_safety_names represented safe
        (reachable_originsBorn closed path) successful
      exact ⟨next,current,nextSafe⟩

 theorem stepRaw_blackhole_origin {state : State} {address : Address}
    (hole : (stepRaw state).control = .blackhole address) :
    state.control = .blackhole address ∨
      (state.control = .enter address ∧ ∃ origin, state.heap[address]? = some (.evaluating origin)) := by
  unfold stepRaw at hole
  split at hole <;> repeat' first | split at hole
  all_goals simp_all

/-- General terminating closed-source consequence for EVERY reachable state:
the actual graph executor never produces a blackhole. This says nothing about
classifying blackholes for arbitrary diverging source computations. -/
 theorem reachable_terminating_no_blackhole {source result : Term} {state : State}
    (closed : Scoped 0 source) (terminates : Evaluates source result)
    (reachable : Reachable (initial source) state) : ∀ address, state.control ≠ .blackhole address := by
  induction reachable with
  | start => intro address; simp [initial]
  | @next before path ih =>
      intro address hole
      rcases stepRaw_blackhole_origin hole with prior | ⟨enter,origin,found⟩
      · exact ih address prior
      · have successful : ResultControl before.control := by simp [ResultControl,enter]
        obtain ⟨meaning,represented,safe⟩ := reachable_closed_demandSafety closed path successful
        exact graphBy_terminating_reentry_impossible represented safe terminates enter found

 theorem rawRun_terminating_no_blackhole {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (ticks : Nat) :
    ∀ address, (rawRun ticks (initial source)).control ≠ .blackhole address :=
  reachable_terminating_no_blackhole closed terminates (rawRun_reachable .start ticks)

#assert_axioms reachable_terminating_no_blackhole rawRun_terminating_no_blackhole


/-- A finite independent derivation of the demanded returned-value context
forces every real frame dispatch to have the required operand/field. This
uses source semantics, without a separate typed-source restriction. -/
 theorem closeTerm_lam_form (meaning : AddressMeaning) (environment : Environment) (body : Term) :
    closeTerm meaning environment (.lam body) = .lam
      (match environment with
        | [] => body
        | _::_ => body.substitute (liftSubstitution (environmentSubstitution meaning environment))) := by
  cases environment <;> simp [closeTerm,Term.substitute]

 theorem frame_derivation_return_progress {meaning : AddressMeaning} {state : State} {frame : Frame}
    {rest : List Frame} {returnedValue : RuntimeValue} {result : Term} {cost : Nat}
    (busy : BusyInvariant state) (returned : state.control = .returned returnedValue)
    (head : state.stack = frame::rest)
    (derivation : SourceDerivation (frameMeaning meaning frame (valueMeaning meaning returnedValue)) result cost) :
    ResultControl (stepRaw state).control := by
  cases frame with
  | update address =>
      obtain ⟨origin,found⟩ := busy_update_exists busy head
      simp [stepRaw,returned,head,found,ResultControl]
  | argument argument environment =>
      cases derivation with
      | value value => cases value
      | applicationLambda first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
      | applicationSpecification first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
  | reflect =>
      cases derivation with
      | value value => cases value
      | reflect first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
  | metadata =>
      cases derivation with
      | value value => cases value
      | metadata first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
  | project =>
      cases derivation with
      | value value => cases value
      | project first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
  | field name =>
      cases derivation with
      | value value => cases value
      | @field target body result fields name targetCost resultCost first selected second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case record addresses =>
            subst fields
            cases found : addresses.find? (fun field => field.1 == name) with
            | none => simp [List.find?_map,Function.comp_def,found] at selected
            | some field => obtain ⟨key,address⟩ := field; simp [stepRaw,returned,head,found,ResultControl]
  | extend fields environment =>
      cases derivation with
      | value value => cases value
      | extend first =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          simp [stepRaw,returned,head,ResultControl]
  | condition zero body environment =>
      cases derivation with
      | value value => cases value
      | zero first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case natural number => subst number; simp [stepRaw,returned,head,ResultControl]
      | successor first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case natural number => subst number; simp [stepRaw,returned,head,ResultControl]
  | binaryLeft primitive right environment => simp [stepRaw,returned,head,ResultControl]
  | binaryRight primitive left =>
      cases derivation with
      | value value => cases value
      | binary first second found =>
          have leftEq := (sourceDerivation_value_inv (valueMeaning_value meaning left) first).1
          have rightEq := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) second).1
          rw [leftEq,rightEq] at found
          cases primitive <;> cases left <;> cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form,primitiveResult] at found
          all_goals simp [stepRaw,returned,head,valueTerm,primitiveResult,scalarValue,ResultControl]
  | case arms environment =>
      cases derivation with
      | value value => cases value
      | @case scrutinee payload body result closedArms tag scrutineeCost resultCost first selected second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case variant label address =>
            obtain ⟨rfl,-⟩ := same
            cases found : arms.find? (fun arm => arm.1 == tag) with
            | none => rw [find_map_arms,found] at selected; simp at selected
            | some arm => obtain ⟨key,armBody⟩ := arm; simp [stepRaw,returned,head,found,ResultControl]
  | ifBool whenTrue whenFalse environment =>
      cases derivation with
      | value value => cases value
      | ifTrue first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case boolean value => subst value; simp [stepRaw,returned,head,ResultControl]
      | ifFalse first second =>
          have same := (sourceDerivation_value_inv (valueMeaning_value meaning returnedValue) first).1
          cases returnedValue <;> simp [valueMeaning,closeTerm_lam_form] at same
          case boolean value => subst value; simp [stepRaw,returned,head,ResultControl]

#assert_axioms frame_derivation_return_progress


/-- Independent source termination supplies the exact demanded frame operand
and selected field, while earned Safety excludes busy re-entry. Thus every
actual next raw control is running/finished, with no typed-domain premise. -/
 theorem graphBy_terminating_next_result {meaning : AddressMeaning} {state : State} {source result : Term}
    (represented : GraphRepresentsBy meaning state source) (safe : DemandSafety meaning state)
    (terminates : Evaluates source result) : ResultControl (stepRaw state).control := by
  cases control : state.control with
  | refused reason | blackhole address =>
      obtain ⟨_,_,_,_,_,focus,current,_⟩ := represented
      simp [control,controlMeaning] at current
  | yielded plan =>
      -- A terminating source never yields: the focus would be a stuck perform.
      exfalso
      obtain ⟨_,_,_,_,_,focus,current,stack⟩ := represented
      simp only [control,controlMeaning,Option.some.injEq] at current
      subst focus
      obtain ⟨cost,whole⟩ := source_evaluates_derivation (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
      obtain ⟨_,_,demand,_⟩ := stack_derivation_demand whole
      cases demand with
      | value isValue => cases isValue
  | complete value => simp [stepRaw,control,ResultControl]
  | enter address =>
      cases found : state.heap[address]? with
      | none =>
          have noMissing := stepRaw_no_missingCell represented.1 (by simp [control])
          simp [stepRaw,control,found] at noMissing
      | some cell =>
          cases cell with
          | evaluating origin => exact False.elim (graphBy_terminating_reentry_impossible represented safe terminates control found)
          | suspended origin | cached origin value => simp [stepRaw,control,found,ResultControl]
  | evaluate term environment =>
      cases term <;> try simp [stepRaw,control,ResultControl]
      case perform plan =>
        -- A terminating source never demands a perform: it has no derivation.
        exfalso
        obtain ⟨_,_,_,_,_,focus,current,stack⟩ := represented
        have aligned : focus = closeTerm meaning environment (.perform plan) := by
          simpa [controlMeaning,control] using current.symm
        subst focus
        obtain ⟨cost,whole⟩ := source_evaluates_derivation (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
        obtain ⟨_,_,demand,_⟩ := stack_derivation_demand whole
        rw [closeTerm_perform] at demand
        cases demand with
        | value isValue => cases isValue
      case bound index =>
        cases found : environment[index]? with
        | none =>
            have noUnbound := stepRaw_no_unbound represented.1 (by simp [control])
            simp [stepRaw,control,found] at noUnbound
        | some address => simp [stepRaw,control,found,ResultControl]
  | returned value =>
      cases head : state.stack with
      | nil => simp [stepRaw,control,head,ResultControl]
      | cons frame rest =>
          obtain ⟨_,busy,_,_,_,focus,current,stack⟩ := represented
          have aligned : focus = valueMeaning meaning value := by simpa [controlMeaning,control] using current.symm
          subst focus
          have residual := sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates
          obtain ⟨cost,whole⟩ := source_evaluates_derivation residual
          have framed : SourceDerivation
              (stackMeaning meaning rest (frameMeaning meaning frame (valueMeaning meaning value))) result cost := by
            simpa only [head,stackMeaning,List.foldl_cons] using whole
          obtain ⟨middle,middleCost,demand,_⟩ := stack_derivation_demand framed
          exact frame_derivation_return_progress busy control head demand

 theorem rawRun_terminating_graphSafety {meaning : AddressMeaning} {state : State} {source result : Term}
    (represented : GraphRepresentsBy meaning state source) (safe : DemandSafety meaning state)
    (born : HeapOriginsBorn state.heap) (terminates : Evaluates source result) (ticks : Nat) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (rawRun ticks state) source ∧ DemandSafety next (rawRun ticks state) := by
  induction ticks generalizing state meaning with
  | zero => exact ⟨meaning,represented,safe⟩
  | succ ticks ih =>
      have successful := graphBy_terminating_next_result represented safe terminates
      obtain ⟨next,_,current,nextSafe⟩ := graph_stepRaw_safety_names represented safe born successful
      exact ih current nextSafe (stepRaw_originsBorn represented.1 born)

/-- Every finite prefix of the actual executor remains running/finished for
EVERY independently terminating closed source. All refusals and blackholes
are excluded from these actual traces; finite completion is still separate. -/
 theorem rawRun_terminating_resultControl {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (ticks : Nat) :
    ResultControl (rawRun ticks (initial source)).control := by
  obtain ⟨meaning,represented,safe⟩ := rawRun_terminating_graphSafety (graphBy_initializes closed)
    (initial_demandSafety source _) (initial_originsBorn source) terminates ticks
  obtain ⟨_,_,_,_,_,focus,control,stack⟩ := represented
  cases actual : (rawRun ticks (initial source)).control <;> try trivial
  all_goals first
    | (simp [actual,controlMeaning] at control; done)
    | (exfalso
       simp only [actual,controlMeaning,Option.some.injEq] at control
       subst focus
       obtain ⟨cost,whole⟩ := source_evaluates_derivation (sourceSteps_evaluates_tail (stackRealizes_erases stack) terminates)
       obtain ⟨_,_,demand,_⟩ := stack_derivation_demand whole
       cases demand with
       | value isValue => cases isValue)

#assert_axioms graphBy_terminating_next_result rawRun_terminating_resultControl


/-- For arbitrary capacities, the bounded executor retains an exact actual
raw prefix; suspension can shorten its physical work, but cannot synthesize
or replace machine state. -/
 theorem runBounded_retained_prefix (limits : Limits) (ticks : Nat) (state : State) :
    ∃ count, count ≤ ticks ∧ retainedState (runBounded limits ticks state) = rawRun count state := by
  induction ticks generalizing state with
  | zero =>
      refine ⟨0,Nat.le_refl _,?_⟩
      cases control : state.control <;> simp [runBounded,control,retainedState,rawRun]
  | succ ticks ih =>
      cases control : state.control with
      | complete value | refused reason | blackhole address | yielded _ =>
          refine ⟨0,Nat.zero_le _,?_⟩
          simp [runBounded,step,control,retainedState,rawRun]
      | evaluate term environment | enter address | returned value =>
          by_cases fits : (stepRaw state).heap.size ≤ limits.heap ∧ (stepRaw state).stack.length ≤ limits.stack
          · have dispatched : step limits state = .suspended .ticks (stepRaw state) := by simp [step,control,fits]
            obtain ⟨count,bound,exactState⟩ := ih (stepRaw state)
            refine ⟨count+1,Nat.succ_le_succ bound,?_⟩
            simpa only [runBounded,dispatched,rawRun] using exactState
          · have suspended : step limits state = .suspended .capacity state := by simp [step,control,fits]
            refine ⟨0,Nat.zero_le _,?_⟩
            simp only [runBounded,suspended,retainedState,rawRun]

 theorem runBounded_terminating_retained_resultControl {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (limits : Limits) (ticks : Nat) :
    ResultControl (retainedState (runBounded limits ticks (initial source))).control := by
  obtain ⟨count,_,exactState⟩ := runBounded_retained_prefix limits ticks (initial source)
  rw [exactState]
  exact rawRun_terminating_resultControl closed terminates count

/-- Finite resource classification follows the actual source-derived raw
progress theorem. Any capacities/ticks yield a genuine finish or retained
suspension, never a semantic refusal or blackhole for a terminating source. -/
 theorem runBounded_only_finish_or_suspend (limits : Limits) (ticks : Nat) (state : State)
    (progress : ∀ count, ResultControl (rawRun count state).control) :
    (∃ value final, runBounded limits ticks state = .finished value final) ∨
      (∃ reason retained, runBounded limits ticks state = .suspended reason retained) := by
  induction ticks generalizing state with
  | zero =>
      have current := progress 0
      cases control : state.control with
      | refused reason | blackhole address | yielded _ => simp [rawRun,control,ResultControl] at current
      | complete value => exact Or.inl ⟨value,state,by simp [runBounded,control]⟩
      | evaluate term environment | enter address | returned value =>
          exact Or.inr ⟨.ticks,state,by simp [runBounded,control]⟩
  | succ ticks ih =>
      have current := progress 0
      cases control : state.control with
      | refused reason | blackhole address | yielded _ => simp [rawRun,control,ResultControl] at current
      | complete value => exact Or.inl ⟨value,state,by simp [runBounded,step,control]⟩
      | evaluate term environment | enter address | returned value =>
          by_cases fits : (stepRaw state).heap.size ≤ limits.heap ∧ (stepRaw state).stack.length ≤ limits.stack
          · have dispatched : step limits state = .suspended .ticks (stepRaw state) := by simp [step,control,fits]
            have nextProgress : ∀ count, ResultControl (rawRun count (stepRaw state)).control := fun count => progress (count+1)
            simpa only [runBounded,dispatched] using ih (stepRaw state) nextProgress
          · have suspended : step limits state = .suspended .capacity state := by simp [step,control,fits]
            exact Or.inr ⟨.capacity,state,by simp only [runBounded,suspended]⟩

 theorem runBounded_terminating_finish_or_suspend {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) (limits : Limits) (ticks : Nat) :
    (∃ value final, runBounded limits ticks (initial source) = .finished value final) ∨
      (∃ reason retained, runBounded limits ticks (initial source) = .suspended reason retained) :=
  runBounded_only_finish_or_suspend limits ticks (initial source) (rawRun_terminating_resultControl closed terminates)

#assert_axioms runBounded_retained_prefix runBounded_terminating_finish_or_suspend

/-! Axiom pins for every r11 theorem not pinned above. -/
#assert_axioms sourceSteps_trans source_value_noStep source_value_steps_identity
  sourceStep_evaluates_tail sourceSteps_lift primitiveResult_value sourceDerivation_evaluates
  sourceDerivation_cost_positive sourceDerivation_value_inv sourceStep_derivation_prepend
  source_evaluates_derivation sourceDerivation_result_unique sourceSteps_derivation_tail
  sourceSteps_derivation_strict scoped_rename_identity scoped_substitute_identity
  scoped_substitution_congr liftRename_comp liftRename_substitution_comp scoped_rename_comp
  scoped_rename_substitute lifted_substitution_scoped lifted_substitution_rename
  scoped_substitute_rename lifted_substitution_comp scoped_substitute_comp
  environmentSubstitution_scoped closeTerm_eq_substitution closeTerm_meaning_congr closeTerm_scoped
  valueMeaning_scoped valueMeaning_congr cellRealizes_congr heapRealizes_congr heapRealizes_push
  frameMeaning_congr valueMeaning_value enteredFocus_steps sourceSteps_frame stackRealizes_congr
  stackRealizes_steps sourceSteps_stack heapRealizes_set cachedCell_realizes graph_initializes
  graph_complete_natural_sound graph_complete_label_sound frame_derivation_demand
  stack_derivation_demand demandContext_closes demandContext_dispatch valueTerm_meaning
  scalarValue_meaning closeTerm_app closeTerm_lambda extendMeaning_prefix allocateClosure_realizes
  allocationLoop_accumulator allocateFields_cons closeTerm_record closeTerm_mixBody closeTerm_weaken
  closeTerm_fix tiedOrigin_name_proper heapOriginsBorn_sameSize heapOriginsBorn_set
  heapOriginsBorn_push heapOriginsBorn_suspend heapOriginsBorn_fix allocateFields_originsBorn
  initial_originsBorn graphBy_graph graphBy_initializes graph_evaluate_context_names
  graph_evaluate_bound_names graph_evaluate_immediate_names graph_object_access_execution
  graph_object_access_names graph_specification_call_names graph_primitive_return_names
  graph_enter_suspended_names graph_cache_update_names graph_enter_cached_names
  graph_evaluate_pair_names graph_evaluate_record_names graph_field_return_execution
  graph_field_return_names graph_evaluate_mix_execution graph_evaluate_mix_names
  graph_condition_zero_execution graph_condition_zero_names graph_condition_successor_execution
  graph_condition_successor_names graph_extend_record_names graph_evaluate_fix_names
  graph_closure_call_execution graph_closure_call_names graph_evaluate_application_names
  graph_binary_left_return_names graph_complete_return_names originBorn_capture_bound traceFits_mono
  traceFits_traceLimits rawRun_absorbs rawRun_resultControl graph_terminating_administration
  rawRun_reachable step_finished_control step_ticks_raw runBounded_finished_control
  runBounded_finished_resultControl runBounded_retains_rawRun runBounded_complete_classifies
  rawRun_lexicalInvariant rawRun_preservesOrigins rawRun_preservesCached unused_argument_executor
  unused_argument_source shared_argument_executor shared_argument_source push_nonEvaluating_backward
  allocateFields_evaluating_backward set_nonEvaluating_backward evaluatingSegment_reachable
  evaluatingSegment_cell evaluatingSegment_from_entry stackRealizes_update_segment captureCap_le
  captureCap_valid initial_demandSafety demandSafety_returned budgetFocus_enter_steps
  budgetCap_enter_bound demandSafety_terminal frame_derivation_demand_strict
  stackUpdates_member_split budgetFocus_control_steps graph_execution_demandSafety
  graph_evaluate_mix_safety graph_condition_zero_safety graph_field_return_safety
  budgetFocus_meaning_congr demandSafety_complete graph_next_returned_safety
  graph_next_complete_safety graph_next_ordinary_safety graph_administrative_safety
  rawRun_graphBy_safety_names graphBy_terminating_control_budget
  graphBy_terminating_reentry_impossible reachable_closed_demandSafety stepRaw_blackhole_origin
  closeTerm_lam_form rawRun_terminating_graphSafety runBounded_terminating_retained_resultControl
  runBounded_only_finish_or_suspend

/-! Non-vacuity of the r11 source-only premises. Every new r11 theorem whose
premises are `Scoped 0 source` and `Evaluates source result` is instantiated
below at a closed Fix program that genuinely evaluates. The internal graph
lemmas (GraphRepresentsBy / DemandSafety / HeapOriginsBorn premises) are
discharged on actual traces by `rawRun_terminating_graphSafety` from
`graphBy_initializes`, `initial_demandSafety` and `initial_originsBorn`. -/

/-- The closed lazy Fix program of `lazy_fixed_function`. -/
def lazyFixedSource : Term := .fix (.lam (.lam (.lam (.bound 0)))) (.nat 7)

theorem lazyFixedSource_closed : Scoped 0 lazyFixedSource :=
  .fix (.lam (.lam (.lam (.bound (by decide))))) (.natural 7)

theorem lazyFixedSource_evaluates : Evaluates lazyFixedSource (.lam (.bound 0)) :=
  lazy_fixed_function

theorem lazyFixedSource_resultControl (ticks : Nat) :
    ResultControl (rawRun ticks (initial lazyFixedSource)).control :=
  rawRun_terminating_resultControl lazyFixedSource_closed lazyFixedSource_evaluates ticks

theorem lazyFixedSource_finish_or_suspend (limits : Limits) (ticks : Nat) :
    (∃ value final, runBounded limits ticks (initial lazyFixedSource) = .finished value final) ∨
      (∃ reason retained, runBounded limits ticks (initial lazyFixedSource) = .suspended reason retained) :=
  runBounded_terminating_finish_or_suspend lazyFixedSource_closed lazyFixedSource_evaluates limits ticks

#assert_axioms lazyFixedSource_closed lazyFixedSource_evaluates lazyFixedSource_resultControl
  lazyFixedSource_finish_or_suspend graph_evaluate_inject_names graph_case_return_execution
  graph_ifBool_return_execution graph_case_return_safety graph_ifBool_return_safety graph_via_names

end Minidregg.Theory.ObjectiveBendDemandAdequacy
