/- Reusable public arithmetic syntax, source quantity and public bounds.
Input indices are de Bruijn indices (0 is the last formal parameter). The
artifact records the exact ordered wire/name map; no consumer guesses it.
Q2 Nat/Data formal parameters permit repeated uses; each exact Nat.add call
consumes Q1 copies. Private program topology is outside this public profile. -/
import Compiler.BendLogicNatAdd
import Theory.BendExecutionTrace

namespace Minidregg.Compiler.BendNaturalExpression
open Minidregg.Theory
open BendLogicSpecialization (BTerm BBook)
open BendSourceRepresentation (natTerm)
set_option autoImplicit false

inductive Expr (arity : Nat) where
  | input (index : Fin arity)
  | literal (value : Nat)
  | add (left right : Expr arity)
  deriving DecidableEq, Repr

def Expr.value {n : Nat} (inputs : Fin n → Nat) : Expr n → Nat
  | .input i => inputs i
  | .literal value => value
  | .add left right => left.value inputs + right.value inputs

def Expr.source {n : Nat} (inputTerms : Fin n → BTerm) : Expr n → BTerm
  | .input i => inputTerms i
  | .literal value => natTerm value
  | .add left right => .App .Q1 (.App .Q1 (.Ref "Nat.add") (left.source inputTerms))
      (right.source inputTerms)

def Expr.air {n : Nat} {F Idx : Type} [Field F] (inputTerms : Fin n → Idx) :
    Expr n → Term (AirSig F Idx)
  | .input i => vr (inputTerms i)
  | .literal value => cst (value : F)
  | .add left right => add' (left.air (F := F) inputTerms) (right.air (F := F) inputTerms)

/-- Physical addition-node count, separate from source semantic charge. -/
def Expr.addCount {n : Nat} : Expr n → Nat
  | .input _ | .literal _ => 0
  | .add left right => left.addCount + right.addCount + 1

/-- Inclusive upper bound; all operations are monotone natural addition. -/
def Expr.upper {n : Nat} (caps : Fin n → Nat) : Expr n → Nat := Expr.value caps

/-- Actual source reduction count after the installed method's one Eval.call.
The Nat.add source reduces in first-operand+1 Eval transitions. This charge is
independent of the flattened circuit's gate count and backend latency. -/
def Expr.sourceCount {n : Nat} (inputs : Fin n → Nat) : Expr n → Nat
  | .input _ | .literal _ => 0
  | .add left right => left.sourceCount inputs + right.sourceCount inputs +
      left.value inputs + 1

def Expr.countBound {n : Nat} (caps : Fin n → Nat) : Expr n → Nat := Expr.sourceCount caps

theorem value_le {n : Nat} (expr : Expr n) (inputs caps : Fin n → Nat)
    (bounded : ∀ i, inputs i ≤ caps i) : expr.value inputs ≤ expr.upper caps := by
  induction expr with
  | input i => exact bounded i
  | literal value => exact le_refl value
  | add left right ihLeft ihRight => exact Nat.add_le_add ihLeft ihRight

theorem count_le {n : Nat} (expr : Expr n) (inputs caps : Fin n → Nat)
    (bounded : ∀ i, inputs i ≤ caps i) : expr.sourceCount inputs ≤ expr.countBound caps := by
  induction expr with
  | input i => exact le_refl 0
  | literal value => exact le_refl 0
  | add left right ihLeft ihRight =>
    have valueBound := value_le left inputs caps bounded
    change left.sourceCount inputs + right.sourceCount inputs + left.value inputs + 1 ≤
      left.sourceCount caps + right.sourceCount caps + left.value caps + 1
    simp only [Expr.countBound, Expr.upper] at ihLeft ihRight valueBound
    omega

theorem air_correct {n : Nat} {F Idx : Type} [Field F] (expr : Expr n)
    (inputTerms : Fin n → Idx) (asg : Idx → F) (inputs : Fin n → Nat)
    (pinned : ∀ i, asg (inputTerms i) = (inputs i : F)) :
    eval asg (expr.air (F := F) inputTerms) = (expr.value inputs : F) := by
  induction expr with
  | input i => simpa only [Expr.air, eval_vr, Expr.value] using pinned i
  | literal value => rfl
  | add left right ihLeft ihRight =>
    simp only [Expr.air, eval_add', ihLeft, ihRight, Expr.value, Nat.cast_add]

/-- Existing flattening emits precisely one constructive gate per addition.
This is a backend shape/capacity fact, never an equality to semantic charge. -/
theorem flat_shape {n : Nat} {F Idx : Type} [Field F] (expr : Expr n)
    (inputTerms : Fin n → Idx) (start : Nat) :
    (flatten (expr.air (F := F) inputTerms) start).next = start + expr.addCount ∧
      (flatten (expr.air (F := F) inputTerms) start).gates.length = expr.addCount := by
  induction expr generalizing start with
  | input i => exact ⟨rfl, rfl⟩
  | literal value => exact ⟨rfl, rfl⟩
  | add left right ihLeft ihRight =>
    obtain ⟨leftNext, leftSize⟩ := ihLeft start
    obtain ⟨rightNext, rightSize⟩ := ihRight (flatten (left.air (F := F) inputTerms) start).next
    constructor
    · change (flatten (right.air (F := F) inputTerms) (flatten (left.air (F := F) inputTerms) start).next).next + 1 = _
      rw [rightNext, leftNext]
      simp only [Expr.addCount]
      omega
    · change ((flatten (left.air (F := F) inputTerms) start).gates ++
        (flatten (right.air (F := F) inputTerms) (flatten (left.air (F := F) inputTerms) start).next).gates ++ [_]).length = _
      simp only [List.length_append, List.length_singleton, leftSize, rightSize, Expr.addCount]

/-- The compiler profile declares the exact source-cost outcome. Public profiles admit
only budgets covering countBound+one installed method call, so all admitted
private inputs finish; smaller budgets remain explicit reference exhaustion. -/
inductive ChargedOutcome where
  | complete (value : Nat)
  | exhausted
  deriving DecidableEq, Repr

def outcome {n : Nat} (expr : Expr n) (inputs : Fin n → Nat) (budget : Nat) : ChargedOutcome :=
  if 1 + expr.sourceCount inputs ≤ budget then .complete (expr.value inputs) else .exhausted

theorem admitted_budget_finishes {n : Nat} (expr : Expr n) (inputs caps : Fin n → Nat)
    (bounded : ∀ i, inputs i ≤ caps i) (budget : Nat)
    (admitted : 1 + expr.countBound caps ≤ budget) :
    outcome expr inputs budget = .complete (expr.value inputs) := by
  have actualBound := count_le expr inputs caps bounded
  have enough : 1 + expr.sourceCount inputs ≤ budget := by omega
  simp [outcome, enough]

theorem underbudget_exhausts {n : Nat} (expr : Expr n) (inputs : Fin n → Nat)
    (budget : Nat) (short : budget < 1 + expr.sourceCount inputs) :
    outcome expr inputs budget = .exhausted := by
  simp [outcome, Nat.not_le.mpr short]

#assert_axioms value_le
#assert_axioms count_le
#assert_axioms air_correct
#assert_axioms flat_shape
#assert_axioms admitted_budget_finishes
#assert_axioms underbudget_exhausts
end Minidregg.Compiler.BendNaturalExpression
