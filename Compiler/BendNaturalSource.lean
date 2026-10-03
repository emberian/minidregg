/- Source correspondence and canonical exact Eval charge for the reusable
natural-expression grammar. No new interpreter: all transitions are constructors
of the pinned Eval/Walk relations. Method erasure/lowering may stutter physically;
source trace count is the declared arithmetic charge, never emitted gate count. -/
import Compiler.BendNaturalExpression

namespace Minidregg.Compiler.BendNaturalExpression
open Minidregg.Theory.BendTT Minidregg.Theory.BendLiveMachine
open BendSourceRepresentation
set_option autoImplicit false

private theorem trace_map {book : Book} {count : Nat} {first last : BTerm}
    (f : BTerm → BTerm) (step : ∀ {a b}, Eval book a b → Eval book (f a) (f b))
    (trace : Trace book count first last) : Trace book count (f first) (f last) := by
  induction trace with
  | refl => exact .refl _
  | step transition rest ih => exact .step (step transition) ih

private theorem natAdd_ref_value (book : Book)
    (binding : Book.get book "Nat.add" = some natAddDef) : Value book (.Ref "Nat.add") :=
  .call binding .nil (.need rfl)

private theorem natAdd_partial_value (book : Book)
    (binding : Book.get book "Nat.add" = some natAddDef) (a : Nat) :
    Value book (.App .Q1 (.Ref "Nat.add") (natTerm a)) := by
  cases a with
  | zero => exact .call binding (.cons (fun _ => natTerm_value book 0) .nil)
      (.prj rfl (.hit rfl (.hit rfl (.need rfl))))
  | succ a => exact .call binding (.cons (fun _ => natTerm_value book (a + 1)) .nil)
      (.prj rfl (.miss rfl (by decide) (.hit rfl
        (.prj rfl (.lam rfl (by intro h; cases h) (.hit rfl (.need rfl)))))))

/-- Exact captured unary Nat.add semantic count, for every natural pair. -/
theorem natAdd_trace (book : Book)
    (binding : Book.get book "Nat.add" = some natAddDef) (a b : Nat) :
    Trace book (a + 1) (natAddCall a b) (natTerm (a + b)) := by
  induction a with
  | zero =>
    apply Trace.step
    · exact .call binding (.cons (fun _ => natTerm_value book 0)
        (.cons (fun _ => natTerm_value book b) .nil))
        (.prj rfl (.hit rfl (.hit rfl
          (.lam rfl (by intro h; cases h) (.done rfl)))))
    · simpa only [Nat.zero_add] using Trace.refl (natTerm b)
  | succ a ih =>
    have lifted := trace_map succTerm
      (fun step => Eval.tup_b (fun _ => Value.lab) (Eval.tup_a rfl step)) ih
    have first : Eval book (natAddCall (a + 1) b) (succTerm (natAddCall a b)) :=
      .call binding (.cons (fun _ => natTerm_value book (a + 1))
        (.cons (fun _ => natTerm_value book b) .nil))
        (.prj rfl (.miss rfl (by decide) (.hit rfl
          (.prj rfl (.lam rfl (by intro h; cases h)
            (.hit rfl (.lam rfl (by intro h; cases h) (.done rfl))))))))
    simpa [natTerm, succTerm, Nat.succ_add] using Trace.step first lifted

/-- All accepted supported-source compositions follow exactly their declared
charge, including nested argument evaluation. This is a theorem over arbitrary
expressions/inputs; closed fixture executions only test the real consumer. -/
theorem expression_trace {n : Nat} (book : Book)
    (binding : Book.get book "Nat.add" = some natAddDef) (expr : Expr n)
    (inputs : Fin n → Nat) :
    Trace book (expr.sourceCount inputs)
      (expr.source (fun i => natTerm (inputs i))) (natTerm (expr.value inputs)) := by
  induction expr with
  | input i => exact .refl _
  | literal value => exact .refl _
  | add left right ihLeft ihRight =>
    have leftTrace := trace_map
      (fun t => .App .Q1 (.App .Q1 (.Ref "Nat.add") t)
        (right.source (fun i => natTerm (inputs i))))
      (fun step => Eval.app_f (Eval.app_x (natAdd_ref_value book binding) rfl step)) ihLeft
    have rightTrace := trace_map
      (fun t => .App .Q1 (.App .Q1 (.Ref "Nat.add") (natTerm (left.value inputs))) t)
      (fun step => Eval.app_x (natAdd_partial_value book binding _) rfl step) ihRight
    have callTrace := natAdd_trace book binding (left.value inputs) (right.value inputs)
    have complete := Minidregg.Theory.BendExecutionTrace.append
      (Minidregg.Theory.BendExecutionTrace.append leftTrace rightTrace) callTrace
    simpa only [Expr.source, Expr.sourceCount, Expr.value, natAddCall, Nat.add_assoc] using complete

/-- The reference charged outcome is actually reachable at the declared count;
a versioned compiler profile must preserve this observation. This does not prove
a native heap/controller classifier or a physical cost measurement. -/
theorem expression_complete {n : Nat} (book : Book)
    (binding : Book.get book "Nat.add" = some natAddDef) (expr : Expr n)
    (inputs : Fin n → Nat) :
    Trace book (expr.sourceCount inputs)
      (expr.source (fun i => natTerm (inputs i))) (natTerm (expr.value inputs)) ∧
      Value book (natTerm (expr.value inputs)) :=
  ⟨expression_trace book binding expr inputs, natTerm_value book _⟩

#assert_axioms natAdd_trace
#assert_axioms expression_trace
#assert_axioms expression_complete
end Minidregg.Compiler.BendNaturalExpression
