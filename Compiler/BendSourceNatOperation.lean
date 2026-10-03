import Compiler.BendSourceRepresentation
namespace Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false
open Minidregg.Theory.BendTT

/-- Exact safe_emit Nat.add body from the pinned Base definition. -/
def natAddBody : BTerm := .Prj (.Mat "Zero" (unitArm (.Lam .Q1 (.Var 0)))
  (.Mat "Succ" (.Prj (.Lam .Q1 (unitArm (.Lam .Q1
    (.Tup .Q1 (.Lab "Succ") (.Tup .Q1
      (.App .Q1 (.App .Q1 (.Ref "Nat.add") (.Var 1)) (.Var 0)) (.Lab "()"))))))) .Efq))
def natAddDef : Def := ⟨"Nat.add", .All .Q1 (.Ref "Nat")
  (.All .Q1 (.Ref "Nat") (.Ref "Nat")), natAddBody, false⟩
def natAddCall (a b : Nat) : BTerm :=
  .App .Q1 (.App .Q1 (.Ref "Nat.add") (natTerm a)) (natTerm b)
def succTerm (t : BTerm) : BTerm := .Tup .Q1 (.Lab "Succ") (.Tup .Q1 t (.Lab "()"))

theorem natTerm_value (bk : Book) (n : Nat) : Value bk (natTerm n) := by
  induction n with
  | zero => exact .tup (fun _ => .lab) .lab
  | succ n ih => exact .tup (fun _ => .lab) (.tup (fun _ => ih) .lab)

private theorem values_add (bk : Book) (a b : Nat) :
    Values bk [(.Q1, natTerm a), (.Q1, natTerm b)] :=
  .cons (fun _ => natTerm_value bk a) (.cons (fun _ => natTerm_value bk b) .nil)

private theorem add_zero_walk (bk : Book) (b : Nat) :
    Walk bk natAddBody [] [(.Q1, natTerm 0), (.Q1, natTerm b)] (some (natTerm b)) := by
  exact .prj rfl (.hit rfl (.hit rfl (.lam rfl (by intro h; cases h) (.done rfl))))

private theorem add_succ_walk (bk : Book) (a b : Nat) :
    Walk bk natAddBody [] [(.Q1, natTerm (a + 1)), (.Q1, natTerm b)]
      (some (succTerm (natAddCall a b))) := by
  exact .prj rfl (.miss rfl (by decide) (.hit rfl
    (.prj rfl (.lam rfl (by intro h; cases h)
      (.hit rfl (.lam rfl (by intro h; cases h) (.done rfl)))))))

theorem source_natAdd_normalizes (bk : Book)
    (binding : Book.get bk "Nat.add" = some natAddDef) (a b : Nat) :
    Normalizes bk (natAddCall a b) (natTerm (a + b)) := by
  induction a with
  | zero =>
    exact Relation.ReflTransGen.single (Eval.call binding (values_add bk 0 b) (add_zero_walk bk b))
  | succ a ih =>
    have lifted : Normalizes bk (succTerm (natAddCall a b)) (succTerm (natTerm (a + b))) :=
      Relation.ReflTransGen.lift succTerm
        (fun _ _ step => Eval.tup_b (fun _ => .lab) (Eval.tup_a rfl step)) ih
    have first : Eval bk (natAddCall (a + 1) b) (succTerm (natAddCall a b)) :=
      Eval.call binding (values_add bk (a + 1) b) (add_succ_walk bk a b)
    simpa [natTerm, succTerm, Nat.succ_add] using
      (Relation.ReflTransGen.single first).trans lifted

/-- A bounded native Nat profile must retain the exact integer sum; overflow
is an explicit refusal, and is never interpreted as Word modular arithmetic. -/
def boundedNatAdd (cap a b : Nat) : Option Nat := if a + b < cap then some (a + b) else none

theorem boundedNatAdd_exact (cap a b : Nat) (bound : a + b < cap) :
    boundedNatAdd cap a b = some (a + b) := by simp [boundedNatAdd, bound]
theorem boundedNatAdd_refuses (cap a b : Nat) (overflow : cap ≤ a + b) :
    boundedNatAdd cap a b = none := by simp [boundedNatAdd, Nat.not_lt.mpr overflow]

#assert_axioms natTerm_value
#assert_axioms source_natAdd_normalizes
#assert_axioms boundedNatAdd_exact
#assert_axioms boundedNatAdd_refuses
end Minidregg.Compiler.BendSourceRepresentation
