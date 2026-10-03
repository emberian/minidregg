/- Public supported-source producer. Recover the expression from the selected
method, then structurally bind the full actual definition and check public source
and backend bounds. No caller-provided graph replaces this compiler expression. -/
import Compiler.BendNaturalMethod

namespace Minidregg.Compiler.BendNaturalExpression
open Minidregg.Theory.BendTT Minidregg.Theory.BendLiveMachine
open BendSourceRepresentation
set_option autoImplicit false

def recover {n : Nat} : Nat → BTerm → Option (Expr n)
  | 0, _ => none
  | fuel + 1, .Var index => if h : index < n then some (.input ⟨index, h⟩) else none
  | fuel + 1, .App .Q1 (.App .Q1 (.Ref "Nat.add") left) right => do
      pure (.add (← recover fuel left) (← recover fuel right))
  | _ + 1, term => (decodeNat term).map Expr.literal

def unwrap : Nat → BTerm → Option BTerm
  | 0, term => some term
  | n + 1, .Lam .Q2 body => unwrap n body
  | _ + 1, _ => none

structure Plan (arity : Nat) where
  expression : Expr arity
  inputBits : Nat
  outputBits : Nat
  sourceBudget : Nat
  plaintextModulus : Nat
  deriving DecidableEq, Repr

def Plan.inputCap {n : Nat} (plan : Plan n) : Nat := 2 ^ plan.inputBits
def Plan.outputMax {n : Nat} (plan : Plan n) : Nat :=
  plan.expression.upper (fun _ => plan.inputCap - 1)
def Plan.reservation {n : Nat} (plan : Plan n) : Nat :=
  1 + plan.expression.countBound (fun _ => plan.inputCap - 1)

def profileAccepted {n p : Nat} (plan : Plan n) : Bool :=
  decide (0 < n ∧ n ≤ 16 ∧ plan.expression.addCount ≤ 64 ∧ plan.inputBits ≤ plan.outputBits ∧
    2 ^ plan.outputBits ≤ p ∧ plan.outputMax < 2 ^ plan.outputBits ∧
    plan.outputMax < plan.plaintextModulus ∧ plan.reservation ≤ plan.sourceBudget)

def compile {n p : Nat} (book : Book) (entry : String) (fuel : Nat)
    (inputBits outputBits sourceBudget plaintextModulus : Nat) : Option (Plan n) := do
  let found ← Book.get book entry
  let body ← unwrap n found.v
  let expression ← recover fuel body
  let plan := Plan.mk expression inputBits outputBits sourceBudget plaintextModulus
  if admitMethod book entry expression && profileAccepted (p := p) plan then some plan else none

theorem compile_exact {n p : Nat} {book : Book} {entry : String} {fuel : Nat}
    {inputBits outputBits sourceBudget plaintextModulus : Nat} {plan : Plan n}
    (accepted : compile (p := p) book entry fuel inputBits outputBits sourceBudget plaintextModulus = some plan) :
    admitMethod book entry plan.expression = true ∧ profileAccepted (p := p) plan = true := by
  unfold compile at accepted
  cases found : Book.get book entry with
  | none => simp [found] at accepted
  | some definition =>
    cases opened : unwrap n definition.v with
    | none => simp [found, opened] at accepted
    | some body =>
      cases parsed : recover (n := n) fuel body with
      | none => simp [found, opened, parsed] at accepted
      | some expression =>
        simp only [found, opened, parsed, Option.bind_some] at accepted
        split at accepted
        · rename_i admitted
          have identity := Option.some.inj accepted
          subst plan
          simpa only [Bool.and_eq_true] using admitted
        · contradiction

theorem profile_exact {n p : Nat} {plan : Plan n}
    (accepted : profileAccepted (p := p) plan = true) :
    0 < n ∧ n ≤ 16 ∧ plan.expression.addCount ≤ 64 ∧ plan.inputBits ≤ plan.outputBits ∧
      2 ^ plan.outputBits ≤ p ∧ plan.outputMax < 2 ^ plan.outputBits ∧
      plan.outputMax < plan.plaintextModulus ∧ plan.reservation ≤ plan.sourceBudget := by
  simpa only [profileAccepted, decide_eq_true_eq] using accepted

/-- Accepted source methods preserve the exact source Trace, typed Nat result,
and abstract exhausted/complete outcome under the admitted uniform budget. -/
theorem compiled_source_complete {n p : Nat} {book : Book} {entry : String} {fuel : Nat}
    {inputBits outputBits sourceBudget plaintextModulus : Nat} {plan : Plan n}
    (accepted : compile (p := p) book entry fuel inputBits outputBits sourceBudget plaintextModulus = some plan)
    (inputs : Fin n → Nat) (bounded : ∀ i, inputs i < plan.inputCap) :
    Trace book (1 + plan.expression.sourceCount inputs) (invocation entry inputs)
      (natTerm (plan.expression.value inputs)) ∧
      Typed book [] (natTerm (plan.expression.value inputs)) (.Ref "Nat") ∧
      outcome plan.expression inputs plan.sourceBudget = .complete (plan.expression.value inputs) ∧
      plan.expression.value inputs ≤ plan.outputMax ∧
      plan.expression.value inputs < plan.plaintextModulus := by
  obtain ⟨methodAdmitted, profileAdmitted⟩ := compile_exact accepted
  obtain ⟨_, types, _⟩ := admitMethod_exact methodAdmitted
  obtain ⟨_, _, _, _, _, _, plainBound, budgetBound⟩ := profile_exact profileAdmitted
  have inputBound : ∀ i, inputs i ≤ plan.inputCap - 1 := by
    intro i; have := bounded i; omega
  have resultBound := value_le plan.expression inputs (fun _ => plan.inputCap - 1) inputBound
  exact ⟨admitted_entry_trace methodAdmitted inputs, natTerm_typed book types _,
    admitted_budget_finishes plan.expression inputs (fun _ => plan.inputCap - 1)
      inputBound plan.sourceBudget budgetBound, resultBound, lt_of_le_of_lt resultBound plainBound⟩

#assert_axioms compile_exact
#assert_axioms profile_exact
#assert_axioms compiled_source_complete
end Minidregg.Compiler.BendNaturalExpression
