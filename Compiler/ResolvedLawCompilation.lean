/-
# Compiler.ResolvedLawCompilation -- the effective-law lowering seam

The existing CanonicalPolicyAdmission verifier and this adapter share the one
compiledLawAccepts check. The root source address remains witness.address;
resolution/manifest authenticity and durable guards are receiving obligations.
This module intentionally returns no Authorized from a graph alone.
-/
import Compiler.CanonicalPolicyAdmission

namespace Minidregg.Compiler.ResolvedLawCompilation

open Minidregg.Pred
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.LawComposition
open Minidregg.Compiler.CanonicalPolicyAdmission

set_option autoImplicit false

/-- Canonical presentation order fixes witness coordinates without changing the
intersection semantics. The source root's digest is kept separately. -/
def predicate {input : GraphInput} (resolved : ResolvedDAG input) : Pred :=
  effective (canonicalOrder resolved.postorder)

def witness {F : Type} [Field F] [DecidableEq F]
    (profile : CompilerProfile) {input : GraphInput} (resolved : ResolvedDAG input)
    (sourceAddress : Digest) (oldState newState : State) : CompiledPolicyWitness F where
  address := sourceAddress
  oldState := oldState
  newState := newState
  auxiliary := wit profile (predicate resolved) oldState newState

/-- The closure identity must be authenticated by the receiving constructor;
it is never substituted for the policy membership address. -/
structure Witness (F : Type) where
  compiled : CompiledPolicyWitness F
  closureDigest : Digest

def checks {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F) {input : GraphInput} (resolved : ResolvedDAG input)
    (sourceAddress expectedClosure : Digest) (supplied : Witness F) : Bool :=
  decide (supplied.compiled.address = sourceAddress) &&
  decide (supplied.closureDigest = expectedClosure) &&
  compiledLawAccepts profile (predicate resolved) supplied.compiled

theorem checks_sound {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F) {input : GraphInput} (resolved : ResolvedDAG input)
    (sourceAddress expectedClosure : Digest) (supplied : Witness F)
    (accepted : checks profile resolved sourceAddress expectedClosure supplied = true) :
    supplied.compiled.address = sourceAddress ∧
    supplied.closureDigest = expectedClosure ∧
    Minidregg.Pred.eval (predicate resolved) supplied.compiled.oldState supplied.compiled.newState = true := by
  simp only [checks, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨accepted.1.1, accepted.1.2,
    compiledLawAccepts_sound profile (predicate resolved) supplied.compiled accepted.2⟩

/-- Even a valid root membership address cannot select a different closure. -/
theorem wrong_closure_refused {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F) {input : GraphInput} (resolved : ResolvedDAG input)
    (sourceAddress expectedClosure : Digest) (supplied : Witness F)
    (wrong : supplied.closureDigest ≠ expectedClosure) :
    checks profile resolved sourceAddress expectedClosure supplied = false := by
  simp [checks, wrong]

end Minidregg.Compiler.ResolvedLawCompilation
