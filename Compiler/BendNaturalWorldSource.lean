/- Actual shared native input-pair source wrapper for arithmetic expressions.
Constructor matching happens in the source Walk, not a new host decoder. It
extracts exactly n source Nat-byte arguments, consumes Con/Nil units, and drops
current observations affinely. No observation or authority is manufactured.
Source charge counts the selected Ref call+expression Eval schedule; all case
walking is within that exact call, independent of physical gates. -/
import Compiler.BendNaturalCompiler
import Compiler.BendSourceListTyped

namespace Minidregg.Compiler.BendNaturalExpression
open Minidregg.Theory.BendTT Minidregg.Theory.BendLiveMachine
open BendSourceRepresentation
set_option autoImplicit false

def units : Nat → BTerm → BTerm
  | 0, body => body
  | n + 1, body => unitArm (units n body)

def extractList : Nat → Nat → BTerm → BTerm
  | 0, pending, body => .Prj (.Mat "Nil" (units (pending + 1) body)
      (.Mat "Con" (.Prj (.Lam .Q1 (.Prj (.Lam .Q1
        (units (pending + 1) (natTerm 0)))))) .Efq))
  | n + 1, pending, body => .Prj (.Mat "Nil" (units (pending + 1) (natTerm 0))
      (.Mat "Con" (.Prj (.Lam .Q2 (.Prj (extractList n (pending + 1) body)))) .Efq))

def worldBody {n : Nat} (expr : Expr n) : BTerm :=
  .Prj (.Lam .Q1 (.Lam .Q1
    (.App .Q1 (extractList n 0 (expr.source (fun i => .Var i.val))) (.Var 1))))
def worldType : BTerm := .All .Q1 (.Sig .Q1 listNatType listNatType) (.Ref "Nat")
def worldDefinition {n : Nat} (entry : String) (expr : Expr n) : Def :=
  ⟨entry, worldType, worldBody expr, false⟩
def worldInput {n : Nat} (inputs : Fin n → Nat) (observations : List Nat) : BTerm :=
  .Tup .Q1 (natListTerm (List.ofFn inputs).reverse) (natListTerm observations)
def worldInvocation {n : Nat} (entry : String) (inputs : Fin n → Nat)
    (observations : List Nat) : BTerm := .App .Q1 (.Ref entry) (worldInput inputs observations)

def unitArgs (count : Nat) : List Arg := List.replicate count (.Q1, .Lab "()")

private theorem units_walk (book : Book) (body : BTerm) (env : Env)
    (count : Nat) (args : List Arg) (result : Option BTerm)
    (rest : Walk book body env args result) :
    Walk book (units count body) env (unitArgs count ++ args) result := by
  induction count with
  | zero => simpa [units, unitArgs] using rest
  | succ count ih => simpa [units, unitArgs, List.replicate_succ] using Walk.hit rfl ih

/-- The constructor extractor is faithful for every exact-length vector.
All source Nat heads are Data, enabling Q2 reuse without copying closures. -/
theorem extract_walk (book : Book) (values : List Nat) (pending : Nat)
    (body : BTerm) (env : Env) (args : List Arg) (result : Option BTerm)
    (rest : Walk book body ((values.reverse.map natTerm) ++ env) args result) :
    Walk book (extractList values.length pending body) env
      ((.Q1, natListTerm values) :: unitArgs pending ++ args) result := by
  induction values generalizing pending env with
  | nil =>
    apply Walk.prj rfl
    apply Walk.hit rfl
    have walked := units_walk book body env (pending + 1) args result (by simpa using rest)
    simpa [unitArgs, List.replicate_succ] using walked
  | cons head values ih =>
    apply Walk.prj rfl
    apply Walk.miss rfl (by decide)
    apply Walk.hit rfl
    apply Walk.prj rfl
    apply Walk.lam (p := .Q2) (q := Quan.fld .Q1 .Q1) rfl (fun _ => natTerm_data head)
    apply Walk.prj rfl
    have tailWalk := ih (pending + 1) (natTerm head :: env)
      (by simpa [List.reverse_cons, List.map_append, List.append_assoc] using rest)
    simpa [unitArgs, List.replicate_succ] using tailWalk

private theorem natList_value (book : Book) (values : List Nat) : Value book (natListTerm values) := by
  induction values with
  | nil => exact .tup (fun _ => .lab) .lab
  | cons value values ih =>
    exact .tup (fun _ => .lab) (.tup (fun _ => natTerm_value book value) (.tup (fun _ => ih) .lab))

private theorem env_lookup_prefix (values : List Nat) (env : Env) (i : Fin values.length) :
    Env.sub (values.map natTerm ++ env) i.val = natTerm values[i] := by
  induction values with
  | nil => exact i.elim0
  | cons value values ih =>
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; simpa [Env.sub] using ih j

/-- Actual source selected world entry: exact affine byte-list pair, no scalar
method ABI substituted for the shared current-observation input contract. -/
theorem world_entry_step {n : Nat} (book : Book) (entry : String) (expr : Expr n)
    (installed : Book.get book entry = some (worldDefinition entry expr))
    (inputs : Fin n → Nat) (observations : List Nat) :
    Eval book (worldInvocation entry inputs observations)
      (expr.source (fun i => natTerm (inputs i))) := by
  apply Eval.call installed (.cons (fun _ =>
    Value.tup (fun _ => natList_value book _) (natList_value book _)) .nil)
  apply Walk.prj rfl
  apply Walk.lam rfl (by intro h; cases h)
  apply Walk.lam rfl (by intro h; cases h)
  apply Walk.app (by cases n <;> rfl)
  have substitution : Term.sub (Env.sub ((List.ofFn inputs).map natTerm ++
      [natListTerm observations, natListTerm (List.ofFn inputs).reverse]))
      (expr.source (fun i => .Var i.val)) = expr.source (fun i => natTerm (inputs i)) := by
    rw [source_sub]
    congr 1
    funext i
    have known := env_lookup_prefix (List.ofFn inputs)
      [natListTerm observations, natListTerm (List.ofFn inputs).reverse]
      ⟨i.val, by simpa using i.isLt⟩
    simpa using known
  have rest : Walk book (expr.source (fun i => .Var i.val))
      (((List.ofFn inputs).reverse.reverse.map natTerm) ++
        [natListTerm observations, natListTerm (List.ofFn inputs).reverse]) []
      (some (expr.source (fun i => natTerm (inputs i)))) := by
    have done := Walk.done (bk := book) (e := (List.ofFn inputs).map natTerm ++
        [natListTerm observations, natListTerm (List.ofFn inputs).reverse])
        (xs := []) (source_leaf expr)
    simp only [Term.spine] at done
    rw [substitution] at done
    simpa only [List.reverse_reverse] using done
  have walked := extract_walk book (List.ofFn inputs).reverse 0
    (expr.source (fun i => .Var i.val))
    [natListTerm observations, natListTerm (List.ofFn inputs).reverse] []
    (some (expr.source (fun i => natTerm (inputs i)))) rest
  simpa [unitArgs] using walked

theorem world_entry_trace {n : Nat} (book : Book) (entry : String) (expr : Expr n)
    (installed : Book.get book entry = some (worldDefinition entry expr))
    (natAdd : Book.get book "Nat.add" = some natAddDef)
    (inputs : Fin n → Nat) (observations : List Nat) :
    Trace book (1 + expr.sourceCount inputs) (worldInvocation entry inputs observations)
      (natTerm (expr.value inputs)) := by
  simpa [Nat.add_comm] using Trace.step
    (world_entry_step book entry expr installed inputs observations)
    (expression_trace book natAdd expr inputs)

/-- Source-byte domain is explicit; the wrapper itself accepts source Nats,
while shared native UInt8 injection/range constraints enforce actual bytes. -/
theorem world_input_typed {n : Nat} (book : Book) (natBinding : NatBookBinding book)
    (listBinding : ListBookBinding book) (inputs : Fin n → Nat) (observations : List Nat) :
    Typed book [] (worldInput inputs observations) (.Sig .Q1 listNatType listNatType) :=
  .tup (natListTerm_typed book natBinding listBinding _)
    (natListTerm_typed book natBinding listBinding _)

#assert_axioms extract_walk
#assert_axioms world_entry_step
#assert_axioms world_entry_trace
#assert_axioms world_input_typed
end Minidregg.Compiler.BendNaturalExpression
