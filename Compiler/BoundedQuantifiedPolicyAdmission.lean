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

theorem supportedL_ofList (predicates : List Pred) :
    supportedL (PredList.ofList predicates) =
      predicates.all supported := by
  induction predicates with
  | nil => rfl
  | cons predicate rest induction =>
      simp [PredList.ofList, supportedL, induction]

/-- A bounded universal is supported exactly when all instantiated bodies are. -/
theorem supported_forallView {Index : Type} (range : List Index)
    (body : Index -> Pred) :
    supported (forallView range body) =
      range.all (fun index => supported (body index)) := by
  simp [forallView, Pred.all, supported, supportedL_ofList, Function.comp_def]

/-- The existential uses the same existing structural support check. -/
theorem supported_existsView {Index : Type} (range : List Index)
    (body : Index -> Pred) :
    supported (existsView range body) =
      range.all (fun index => supported (body index)) := by
  simp [existsView, Pred.any, supported, supportedL_ofList, Function.comp_def]

/-! ## Existing AIR compiler, specialized without a second lowering -/

theorem lower_forallView_correct {F Index : Type} [Field F] [DecidableEq F]
    (range : List Index) (body : Index -> Pred) (old new : State)
    (castExact : castInjOn F (intsOf (forallView range body) old new))
    (allSupported : range.all (fun index => supported (body index)) = true) :
    (exists auxiliary : List Nat -> Nat -> F,
        systemAccepts (stepAsg old new auxiliary)
          (lower (forallView range body))) <->
      range.all (fun index => Minidregg.Pred.eval (body index) old new) = true := by
  rw [lower_correct castExact (by simpa [supported_forallView] using allSupported)]
  exact Bool.eq_iff_iff.mp (eval_forallView range body old new)

theorem lower_existsView_correct {F Index : Type} [Field F] [DecidableEq F]
    (range : List Index) (body : Index -> Pred) (old new : State)
    (castExact : castInjOn F (intsOf (existsView range body) old new))
    (allSupported : range.all (fun index => supported (body index)) = true) :
    (exists auxiliary : List Nat -> Nat -> F,
        systemAccepts (stepAsg old new auxiliary)
          (lower (existsView range body))) <->
      range.any (fun index => Minidregg.Pred.eval (body index) old new) = true := by
  rw [lower_correct castExact (by simpa [supported_existsView] using allSupported)]
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
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
      some committed)
    (policyIdExact : committed.record.policyId = request.policyId)
    (versionExact : committed.record.version = request.policyEpoch)
    (domainExact : committed.record.domain = request.domain)
    (semanticsExact : committed.record.semantics = request.semantics)
    (recordDigestExact : config.recordDigest committed.record = committed.address)
    (preRootExact : config.stateDigest oldState = request.preStateRoot)
    (effectDigestExact : config.stepDigest oldState newState = request.effectsDigest)
    (supportedExact : supported committed.record.predicate = true)
    (castExact : castInjOn F
      (intsOf committed.record.predicate oldState newState)) :
    config.verifies request (canonicalWitness committed oldState newState) = true <->
      range.all (fun index =>
        Minidregg.Pred.eval (body index) oldState newState) = true := by
  rw [canonical_verifies_iff_eval resolved policyIdExact versionExact domainExact
    semanticsExact recordDigestExact preRootExact effectDigestExact supportedExact
    castExact]
  rw [predicateExact, eval_forallView]

/-! ## Concrete AIR non-vacuity through the shared lowering -/

theorem witness_forall_air_accepts :
    exists auxiliary : List Nat -> Nat -> ZMod 7,
      systemAccepts (stepAsg witnessOld witnessGood auxiliary)
        (lower (forallView witnessRange witnessBody)) := by
  apply (lower_forallView_correct witnessRange witnessBody witnessOld witnessGood
    (by decide) (by decide)).mpr
  decide

theorem witness_forall_air_rejects :
    ¬ (exists auxiliary : List Nat -> Nat -> ZMod 7,
      systemAccepts (stepAsg witnessOld witnessBad auxiliary)
        (lower (forallView witnessRange witnessBody))) := by
  rw [lower_forallView_correct witnessRange witnessBody witnessOld witnessBad
    (by decide) (by decide)]
  decide

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.BoundedQuantifiedPolicyAdmission.lower_forallView_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_forallView_correct

/-- info: 'Minidregg.Compiler.BoundedQuantifiedPolicyAdmission.canonical_forallView_verifies_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canonical_forallView_verifies_iff

end Minidregg.Compiler.BoundedQuantifiedPolicyAdmission
