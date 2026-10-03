/- Runtime book transport for Objective Bend linking.
Lookup equality preserves Eval/Value/Values/Trace. Walk itself never consults
the book. This does NOT transport Book.Live or checker acceptance: the live
checker inspects declaration indices, so reordered artifacts are rechecked. -/
import Theory.BendLiveMachine

namespace Minidregg.Theory.BendBookTransport
open BendTT
set_option autoImplicit false

def LookupEquivalent (left right : Book) : Prop :=
  ∀ name, Book.get left name = Book.get right name

theorem lookup_symm {left right : Book} (same : LookupEquivalent left right) :
    LookupEquivalent right left := fun name => (same name).symm

theorem walk {left right : Book} {term : Term} {env : Env}
    {args : List Arg} {result : Option Term}
    (proof : Walk left term env args result) : Walk right term env args result := by
  induction proof with
  | lam live data _ ih => exact .lam live data ih
  | prj live _ ih => exact .prj live ih
  | hit live _ ih => exact .hit live ih
  | miss live different _ ih => exact .miss live different ih
  | app node _ ih => exact .app node ih
  | need takes => exact .need takes
  | done node => exact .done node

mutual
theorem value {left right : Book} (same : LookupEquivalent left right)
    {term : Term} (proof : Value left term) : Value right term :=
  match proof with
  | .lam => .lam
  | .prj => .prj
  | .mat => .mat
  | .efq => .efq
  | .lab => .lab
  | .rfl => .rfl
  | .typ => .typ
  | .all => .all
  | .sig => .sig
  | .enu => .enu
  | .eql => .eql
  | .tup first second => .tup (fun live => value same (first live)) (value same second)
  | .call found args walked =>
      .call ((same _).symm.trans found) (values same args) (walk walked)

theorem values {left right : Book} (same : LookupEquivalent left right)
    {args : List Arg} (proof : Values left args) : Values right args :=
  match proof with
  | .nil => .nil
  | .cons first rest => .cons (fun live => value same (first live)) (values same rest)
end

theorem eval {left right : Book} (same : LookupEquivalent left right)
    {initial result : Term} (proof : Eval left initial result) :
    Eval right initial result := by
  induction proof with
  | ann => exact .ann
  | app_f _ ih => exact .app_f ih
  | app_x ready live _ ih => exact .app_x (value same ready) live ih
  | beta live ready data => exact .beta live (fun h => value same (ready h)) data
  | split live ready => exact .split live (value same ready)
  | hit live => exact .hit live
  | miss live different => exact .miss live different
  | call found args walked =>
      exact .call ((same _).symm.trans found) (values same args) (walk walked)
  | lett live _ ih => exact .lett live ih
  | unlet ready data => exact .unlet (fun h => value same (ready h)) data
  | tup_a live _ ih => exact .tup_a live ih
  | tup_b ready _ ih => exact .tup_b (fun h => value same (ready h)) ih
  | rwt _ ih => exact .rwt ih
  | cast => exact .cast

theorem trace {left right : Book} (same : LookupEquivalent left right)
    {count : Nat} {initial result : Term}
    (proof : BendLiveMachine.Trace left count initial result) :
    BendLiveMachine.Trace right count initial result := by
  induction proof with
  | refl term => exact .refl term
  | step head _ ih => exact .step (eval same head) ih

theorem eval_iff {left right : Book} (same : LookupEquivalent left right)
    {initial result : Term} :
    Eval left initial result ↔ Eval right initial result :=
  ⟨eval same, eval (lookup_symm same)⟩

theorem value_iff {left right : Book} (same : LookupEquivalent left right)
    {term : Term} : Value left term ↔ Value right term :=
  ⟨value same, value (lookup_symm same)⟩

theorem trace_iff {left right : Book} (same : LookupEquivalent left right)
    {count : Nat} {initial result : Term} :
    BendLiveMachine.Trace left count initial result ↔
      BendLiveMachine.Trace right count initial result :=
  ⟨trace same, trace (lookup_symm same)⟩

#assert_axioms walk
#assert_axioms value
#assert_axioms values
#assert_axioms eval
#assert_axioms trace
#assert_axioms eval_iff
#assert_axioms value_iff
#assert_axioms trace_iff
end Minidregg.Theory.BendBookTransport
