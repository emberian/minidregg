/- Focused checks of the independent closure controller, not a replacement
for its pending general simulation theorem. These ten native execution checks
explicitly use compiler-trust pins which re-run each closed Boolean claim.
The general store/padding/source proofs remain kernel-axiom audited.
Reification constructs exact source
terms with proof; no source evaluator supplies the machine result. -/
import Theory.AssertCompiled
import Theory.BendClosureMachine
import Theory.BendClosureDecode
namespace Minidregg.Theory.BendClosureChecks
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private def limits : Limits :=
  {heap := {slots := 32, wordBits := 8, fits := by decide}, frames := 16, arguments := 16}
private def library (nodes : Array Code) (names : Array String := #[])
    (definitions : Array (Nat × Nat) := #[]) : Library :=
  {program := {code := nodes, names, enumerations := #[]}, definitions}

inductive Result where
  | complete (term : Term) (sourceSteps : Nat)
  | refused (reason : Failure)
  | unfinished
  | invalidReification
  deriving DecidableEq, Repr

def observe (bounds : Limits) (book : Library) (entry ticks : Nat) : Result :=
  match start bounds book entry with
  | .error reason => .refused reason
  | .ok initial =>
    let last := run bounds book ticks initial
    match last.control with
    | .complete pointer =>
      match decode book.program last.heap 64 pointer with
      | some result => .complete result.term last.sourceSteps
      | none => .invalidReification
    | .refused reason => .refused reason
    | _ => .unfinished

theorem beta_actual_controller :
    observe limits
      (library #[.lab 0, .var 0, .lam .Q1 1, .app .Q1 2 0] #["ok"]) 3 16 =
    .complete (.Lab "ok") 1 := by native_decide

theorem q0_preserves_binder_position_without_evaluating_argument :
    observe limits
      (library #[.lab 0, .ref 1, .lam .Q0 0, .app .Q0 2 1] #["ok", "missing"]) 3 16 =
    .complete (.Lab "ok") 1 := by native_decide

theorem live_rewrite_evidence_really_executes :
    observe limits
      (library #[.rfl, .typ .Q1, .ann 0 1, .lab 0, .rwt 2 1 3] #["ok"]) 4 16 =
    .complete (.Lab "ok") 2 := by native_decide

theorem live_unused_let_really_executes :
    observe limits
      (library #[.lab 0, .typ .Q1, .ann 0 1, .lett .Q1 2 0] #["ok"]) 3 16 =
    .complete (.Lab "ok") 2 := by native_decide

theorem partial_call_keeps_original_spine :
    observe limits
      (library #[.lab 0, .var 1, .lam .Q1 1, .lam .Q1 2, .ref 1, .app .Q1 4 0]
        #["ok", "f"] #[(1, 3)]) 5 24 =
    .complete (.App .Q1 (.Ref "f") (.Lab "ok")) 0 := by native_decide

theorem whole_case_walk_before_exposure :
    observe limits
      (library #[.lab 0, .lab 1, .lab 2, .mat 0 2 4, .lam .Q1 2, .ref 3, .app .Q1 5 1]
        #["left", "right", "same", "f"] #[(3, 3)]) 6 24 =
    .complete (.Lab "same") 1 := by native_decide

theorem q2_rejects_function_copy :
    observe limits
      (library #[.var 0, .lam .Q1 0, .lam .Q2 0, .app .Q1 2 1]) 3 16 =
    .refused .notData := by native_decide

/-- Even for a source case tree outside the admitted Live fragment, a
retained Q0 thunk forwarded into a live leaf argument is not asserted Data
before its actual evaluation. This guards a concrete controller shortcut. -/
theorem forwarded_thunk_evaluates_before_q2 :
    observe limits
      (library #[.lab 0, .typ .Q1, .ann 0 1, .var 0, .ref 1, .lam .Q1 4,
        .app .Q1 5 3, .app .Q1 6 3, .lam .Q0 7, .lam .Q2 3, .ref 2, .app .Q0 10 2]
        #["ok", "g", "f"] #[(2, 8), (1, 9)]) 11 80 =
    .complete (.Lab "ok") 3 := by native_decide

theorem zero_ticks_is_not_success :
    observe limits (library #[.lab 0] #["ok"]) 0 0 = .unfinished := by native_decide

theorem heap_capacity_is_not_success :
    observe {limits with heap := {slots := 1, wordBits := 8, fits := by decide}}
      (library #[.lab 0] #["ok"]) 0 8 = .refused (.arena .capacity) := by native_decide

#assert_compiled beta_actual_controller
#assert_compiled q0_preserves_binder_position_without_evaluating_argument
#assert_compiled live_rewrite_evidence_really_executes
#assert_compiled live_unused_let_really_executes
#assert_compiled partial_call_keeps_original_spine
#assert_compiled whole_case_walk_before_exposure
#assert_compiled q2_rejects_function_copy
#assert_compiled forwarded_thunk_evaluates_before_q2
#assert_compiled zero_ticks_is_not_success
#assert_compiled heap_capacity_is_not_success
end Minidregg.Theory.BendClosureChecks

