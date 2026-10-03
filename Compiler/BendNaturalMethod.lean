/- Exact installed-method source admission for reusable arithmetic.
Q2 Nat/Data parameters permit repeated source occurrences. Actual lowering and
source call count are proved; no attribution/import or receiver authority is
inferred from Book.check. A public source graph never hides selected code. -/
import Compiler.BendNaturalCircuit

namespace Minidregg.Compiler.BendNaturalExpression
open Minidregg.Theory.BendTT Minidregg.Theory.BendLiveMachine
open BendSourceRepresentation
set_option autoImplicit false

def wrap : Nat → BTerm → BTerm
  | 0, body => body
  | n + 1, body => .Lam .Q2 (wrap n body)
def methodType : Nat → BTerm
  | 0 => .Ref "Nat"
  | n + 1 => .All .Q2 (.Ref "Nat") (methodType n)
def lower {n : Nat} (expr : Expr n) : BTerm := wrap n (expr.source (fun i => .Var i.val))
def definition {n : Nat} (entry : String) (expr : Expr n) : Def :=
  ⟨entry, methodType n, lower expr, false⟩

theorem natTerm_sub (s : Subst) (value : Nat) : Term.sub s (natTerm value) = natTerm value := by
  induction value with
  | zero => rfl
  | succ value ih => simp [natTerm, Term.sub, ih]

theorem source_sub {n : Nat} (expr : Expr n) (inputTerms : Fin n → BTerm) (s : Subst) :
    Term.sub s (expr.source inputTerms) = expr.source (fun i => Term.sub s (inputTerms i)) := by
  induction expr with
  | input i => rfl
  | literal value => exact natTerm_sub s value
  | add left right ihLeft ihRight => simp only [Expr.source, Term.sub, ihLeft, ihRight]

theorem source_leaf {n : Nat} (expr : Expr n) :
    Term.node (expr.source (fun i => .Var i.val)) = false := by
  cases expr with
  | input i => rfl
  | literal value => cases value <;> rfl
  | add left right =>
    simp only [Expr.source]
    cases right.source (fun i => .Var i.val) <;> rfl

private theorem env_lookup (values : List Nat) (i : Fin values.length) :
    Env.sub (values.map natTerm) i.val = natTerm values[i] := by
  induction values with
  | nil => exact i.elim0
  | cons value values ih =>
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; simpa [Env.sub] using ih j

private theorem env_ofFn {n : Nat} (inputs : Fin n → Nat) (i : Fin n) :
    Env.sub ((List.ofFn inputs).map natTerm) i.val = natTerm (inputs i) := by
  have known := env_lookup (List.ofFn inputs) ⟨i.val, by simpa using i.isLt⟩
  simpa using known

private theorem wrap_walk (book : Book) (body : BTerm) (leaf : Term.node body = false)
    (args : List BTerm) (data : ∀ a ∈ args, Data a) (env : Env) :
    Walk book (wrap args.length body) env (args.map (fun a => (.Q2, a)))
      (some (Term.sub (Env.sub (args.reverse ++ env)) body)) := by
  induction args generalizing env with
  | nil => exact .done leaf
  | cons a args ih =>
    apply Walk.lam rfl (fun _ => data a (by simp))
    have rest := ih (fun x hx => data x (by simp [hx])) (a :: env)
    simpa [List.reverse_cons, List.append_assoc] using rest

def invocation {n : Nat} (entry : String) (inputs : Fin n → Nat) : BTerm :=
  Term.spine (.Ref entry) (((List.ofFn inputs).reverse.map natTerm).map (fun a => (.Q2, a)))

private theorem args_values (book : Book) (values : List Nat) :
    Values book ((values.map natTerm).map (fun a => (.Q2, a))) := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (fun _ => natTerm_value book value) ih

/-- One actual source Ref call unfolds the exact selected arithmetic method.
The subsequent source expression schedule is counted by expression_trace. -/
theorem entry_step {n : Nat} (book : Book) (entry : String) (expr : Expr n)
    (installed : Book.get book entry = some (definition entry expr))
    (inputs : Fin n → Nat) :
    Eval book (invocation entry inputs) (expr.source (fun i => natTerm (inputs i))) := by
  apply Eval.call installed (args_values book (List.ofFn inputs).reverse)
  have walked := wrap_walk book (expr.source (fun i => .Var i.val)) (source_leaf expr)
    ((List.ofFn inputs).reverse.map natTerm)
    (by intro a h; obtain ⟨v, _, rfl⟩ := List.mem_map.mp h; exact natTerm_data v) []
  have substitution : Term.sub (Env.sub ((List.ofFn inputs).map natTerm))
      (expr.source (fun i => .Var i.val)) = expr.source (fun i => natTerm (inputs i)) := by
    rw [source_sub]
    congr 1
    funext i
    exact env_ofFn inputs i
  simp only [List.length_map, List.length_reverse, List.length_ofFn, List.map_reverse,
    List.reverse_reverse, List.append_nil] at walked
  rw [substitution] at walked
  simpa only [definition, lower, List.map_reverse] using walked

/-- The complete actual selected method trace includes its one Eval.call.
No native gate census is used as a semantic meter. -/
theorem entry_trace {n : Nat} (book : Book) (entry : String) (expr : Expr n)
    (installed : Book.get book entry = some (definition entry expr))
    (natAdd : Book.get book "Nat.add" = some natAddDef) (inputs : Fin n → Nat) :
    Trace book (1 + expr.sourceCount inputs) (invocation entry inputs)
      (natTerm (expr.value inputs)) := by
  have full := Trace.step (entry_step book entry expr installed inputs)
    (expression_trace book natAdd expr inputs)
  simpa [Nat.add_comm] using full

/-- Frontend acceptance is a structural equality against the actual selected
full definition; erased metadata or matching a name alone never authorizes code. -/
def admitMethod {n : Nat} (book : Book) (entry : String) (expr : Expr n) : Bool :=
  decide (Book.get book entry = some (definition entry expr)) &&
    BendLogicNatAdd.bookBinding book

theorem admitMethod_exact {n : Nat} {book : Book} {entry : String} {expr : Expr n}
    (accepted : admitMethod book entry expr = true) :
    Book.get book entry = some (definition entry expr) ∧ NatBookBinding book ∧
      Book.get book "Nat.add" = some natAddDef := by
  simp only [admitMethod, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨types, natAdd⟩ := BendLogicNatAdd.bookBinding_sound accepted.2
  exact ⟨accepted.1, types, natAdd⟩

theorem admitted_entry_trace {n : Nat} {book : Book} {entry : String} {expr : Expr n}
    (accepted : admitMethod book entry expr = true) (inputs : Fin n → Nat) :
    Trace book (1 + expr.sourceCount inputs) (invocation entry inputs)
      (natTerm (expr.value inputs)) := by
  obtain ⟨installed, _, natAdd⟩ := admitMethod_exact accepted
  exact entry_trace book entry expr installed natAdd inputs

#assert_axioms natTerm_sub
#assert_axioms source_sub
#assert_axioms source_leaf
#assert_axioms entry_step
#assert_axioms entry_trace
#assert_axioms admitMethod_exact
#assert_axioms admitted_entry_trace
end Minidregg.Compiler.BendNaturalExpression
