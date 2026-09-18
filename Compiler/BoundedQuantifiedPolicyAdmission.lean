/-
# Compiler.BoundedQuantifiedPolicyAdmission -- bounded views through canonical policy admission

The finite quantifier views are consumed by the existing `PredCompile.lower`
and `CanonicalPolicyAdmission` paths.  This module introduces no evaluator,
constraint vocabulary, portal, or authorization judgment.  Its theorems are
specializations of the existing general compiler and canonical-admission
reflection theorems.
-/
import Compiler.CanonicalPolicyAdmission
import Pred.BoundedQuantifiedView

namespace Minidregg.Compiler.BoundedQuantifiedPolicyAdmission

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Pred
open Minidregg.Pred.BoundedQuantifiedView
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Supported-fragment projection -/

theorem supportedL_ofList (profile : CompilerProfile) (predicates : List Pred) :
    supportedL profile (PredList.ofList predicates) =
      predicates.all (supported profile) := by
  induction predicates with
  | nil => rfl
  | cons predicate rest induction =>
      simp [PredList.ofList, supportedL, induction]

/-- A bounded universal is supported exactly when all instantiated bodies are. -/
theorem supported_forallView (profile : CompilerProfile) {Index : Type} (range : List Index)
    (body : Index -> Pred) :
    supported profile (forallView range body) =
      range.all (fun index => supported profile (body index)) := by
  simp [forallView, Pred.all, supported, supportedL_ofList, Function.comp_def]

/-- The existential uses the same existing structural support check. -/
theorem supported_existsView (profile : CompilerProfile) {Index : Type} (range : List Index)
    (body : Index -> Pred) :
    supported profile (existsView range body) =
      range.all (fun index => supported profile (body index)) := by
  simp [existsView, Pred.any, supported, supportedL_ofList, Function.comp_def]

/-- Source-range validation is universal over instantiated bodies, even for an existential. -/
theorem inputsInRangeL_ofList (profile : CompilerProfile) (predicates : List Pred)
    (old new : State) :
    inputsInRangeL profile (PredList.ofList predicates) old new =
      predicates.all (fun predicate => inputsInRange profile predicate old new) := by
  induction predicates with
  | nil => rfl
  | cons predicate rest induction =>
      simp [PredList.ofList, inputsInRangeL, induction]

theorem inputsInRange_forallView (profile : CompilerProfile) {Index : Type}
    (range : List Index) (body : Index → Pred) (old new : State) :
    inputsInRange profile (forallView range body) old new =
      range.all (fun index => inputsInRange profile (body index) old new) := by
  simp [forallView, Pred.all, inputsInRange, inputsInRangeL_ofList, Function.comp_def]

theorem inputsInRange_existsView (profile : CompilerProfile) {Index : Type}
    (range : List Index) (body : Index → Pred) (old new : State) :
    inputsInRange profile (existsView range body) old new =
      range.all (fun index => inputsInRange profile (body index) old new) := by
  simp [existsView, Pred.any, inputsInRange, inputsInRangeL_ofList, Function.comp_def]

/-! ## Existing AIR compiler, specialized without a second lowering -/

theorem lower_forallView_correct {F Index : Type} [Field F] [DecidableEq F]
    (profile : CompilerProfile) (profileAdmissible : profile.Admissible F)
    (range : List Index) (body : Index -> Pred) (old new : State)
    (castExact : castInjOn F (intsOf (forallView range body) old new))
    (allSupported : range.all (fun index => supported profile (body index)) = true)
    (allInputsInRange : range.all (fun index => inputsInRange profile (body index) old new) = true) :
    (exists auxiliary : List Nat -> Nat -> F,
        systemAccepts (stepAsg old new auxiliary)
          (lower profile (forallView range body))) <->
      range.all (fun index => Minidregg.Pred.eval (body index) old new) = true := by
  rw [lower_correct profile profileAdmissible castExact
    (by simpa [supported_forallView] using allSupported)
    (by simpa [inputsInRange_forallView] using allInputsInRange)]
  exact Bool.eq_iff_iff.mp (eval_forallView range body old new)

theorem lower_existsView_correct {F Index : Type} [Field F] [DecidableEq F]
    (profile : CompilerProfile) (profileAdmissible : profile.Admissible F)
    (range : List Index) (body : Index -> Pred) (old new : State)
    (castExact : castInjOn F (intsOf (existsView range body) old new))
    (allSupported : range.all (fun index => supported profile (body index)) = true)
    (allInputsInRange : range.all (fun index => inputsInRange profile (body index) old new) = true) :
    (exists auxiliary : List Nat -> Nat -> F,
        systemAccepts (stepAsg old new auxiliary)
          (lower profile (existsView range body))) <->
      range.any (fun index => Minidregg.Pred.eval (body index) old new) = true := by
  rw [lower_correct profile profileAdmissible castExact
    (by simpa [supported_existsView] using allSupported)
    (by simpa [inputsInRange_existsView] using allInputsInRange)]
  exact Bool.eq_iff_iff.mp (eval_existsView range body old new)

/-! ## The committed canonical policy gate, specialized to a universal view -/

/-- A resolved committed policy whose source predicate is a finite universal
inherits the canonical gate's exact reflection.  No quantifier-specific portal
or verifier is introduced. -/
theorem canonical_forallView_verifies_iff
    {F Index : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    {oldState newState : State} {range : List Index} {body : Index -> Pred}
    (predicateExact : committed.record.predicate = forallView range body)
    (resolved : config.registry.resolve request.policyId request.policyRevision =
      some committed)
    (policyIdExact : committed.record.policyId = request.policyId)
    (versionExact : committed.record.version = request.policyRevision)
    (domainExact : committed.record.domain = request.domain)
    (semanticsExact : committed.record.semantics = request.semantics)
    (recordDigestExact : config.recordDigest committed.record = committed.address)
    (stepExact : config.stepBinding.matches request oldState newState = true)
    (profileCompatible : config.compilerProfile.compatible config.stepBinding = true)
    (profileSemanticsExact : request.semantics = config.compilerProfile.semantics)
    (supportedExact : supported config.compilerProfile.compiler committed.record.predicate = true)
    (rangesExact : inputsInRange config.compilerProfile.compiler committed.record.predicate
      oldState newState = true)
    (castExact : castInjOn F
      (intsOf committed.record.predicate oldState newState)) :
    config.verifies request (canonicalWitness config.compilerProfile.compiler committed oldState newState) = true <->
      range.all (fun index =>
        Minidregg.Pred.eval (body index) oldState newState) = true := by
  rw [canonical_verifies_iff_eval resolved policyIdExact versionExact domainExact
    semanticsExact recordDigestExact stepExact profileCompatible profileSemanticsExact supportedExact
    rangesExact castExact]
  rw [predicateExact, eval_forallView]

/-! ## Concrete AIR non-vacuity through the shared lowering -/

theorem witness_forall_air_accepts :
    exists auxiliary : List Nat -> Nat -> ZMod 7,
      systemAccepts (stepAsg witnessOld witnessGood auxiliary)
        (lower CompilerProfile.disabled (forallView witnessRange witnessBody)) := by
  apply (lower_forallView_correct CompilerProfile.disabled (by trivial) witnessRange witnessBody witnessOld witnessGood
    (by decide) (by decide) (by decide)).mpr
  decide

theorem witness_forall_air_rejects :
    ¬ (exists auxiliary : List Nat -> Nat -> ZMod 7,
      systemAccepts (stepAsg witnessOld witnessBad auxiliary)
        (lower CompilerProfile.disabled (forallView witnessRange witnessBody))) := by
  rw [lower_forallView_correct CompilerProfile.disabled (by trivial) witnessRange witnessBody witnessOld witnessBad
    (by decide) (by decide) (by decide)]
  decide

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.BoundedQuantifiedPolicyAdmission.lower_forallView_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_forallView_correct

/-- info: 'Minidregg.Compiler.BoundedQuantifiedPolicyAdmission.canonical_forallView_verifies_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canonical_forallView_verifies_iff

end Minidregg.Compiler.BoundedQuantifiedPolicyAdmission
