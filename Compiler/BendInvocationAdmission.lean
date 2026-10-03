/- Executable admission for an actual closed Objective Bend invocation.
The original Book is retained unchanged. Actual source checkers produce all
typing/liveness/closedness evidence; no CLI Boolean or supplied proposition
stands in for checking. Native receiving still binds exact input, source,
authority and output codec to this invocation. -/
import Theory.BendLiveMachine

namespace Minidregg.Compiler.BendInvocationAdmission
open Minidregg.Theory BendTT
set_option autoImplicit false

structure Admission (book : Book) (initial outputType : Term) : Type where
  bookChecked : Book.check book = .ok ()
  typed : Typed book [] initial outputType
  closed : Term.Closed initial
  live : Term.Live book initial

theorem sees_checked {book : Book} (checked : Book.check book = .ok ()) :
    Sees (Lib.of book) book := by
  intro name definition found
  have actual : Book.get book name = some definition := by
    simpa only [lib_get] using found
  exact ⟨definition.o, actual, (book_check book checked).2.1 name definition actual⟩

theorem checker_typed {book : Book} (checked : Book.check book = .ok ())
    (ticks : Nat) (initial outputType : Term)
    (accepted : Term.check (Lib.of book) ticks [] initial outputType = .ok ()) :
    Typed book [] initial outputType := by
  have typed := (chk (sees_checked checked) ticks [] initial outputType nofun).2 accepted
  simpa only [Chk, Ctx.decl, Ctx.drop, sub_var] using typed

def admit (book : Book) (ticks : Nat) (initial outputType : Term) :
    Option (Admission book initial outputType) :=
  match bookChecked : Book.check book with
  | .error _ => none
  | .ok () =>
    match typed : Term.check (Lib.of book) ticks [] initial outputType with
    | .error _ => none
    | .ok () =>
      if closed : Term.ren Nat.succ initial = initial then
        if live : Term.live ⟨book, book.length, [], [], []⟩ true initial = true then
          some ⟨bookChecked, checker_typed bookChecked ticks initial outputType typed,
            ren_closed closed, live⟩
        else none
      else none

/-- Upstream termination applies to the admitted pure invocation; it does not
bound physical memory/ticks or the lifetime of a reactive persistent object. -/
theorem admitted_halts {book : Book} {initial outputType : Term}
    (accepted : Admission book initial outputType) :
    Acc (fun next current => Eval book current next) initial :=
  halts book initial (book_check book accepted.bookChecked).2 accepted.closed accepted.live

#assert_axioms sees_checked
#assert_axioms checker_typed
#assert_axioms admit
#assert_axioms admitted_halts
end Minidregg.Compiler.BendInvocationAdmission
