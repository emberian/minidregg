/- Reachable-stack readiness over the actual seven runtime frame forms.
Code/environment captures and retained value pointers are kept separately.
The relation projects to source contexts but also retains the stronger
recursive readiness needed by future argument reopening and installation. -/
import Theory.BendClosureRetainedReady
import Theory.BendClosureProjectionSteps

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

inductive RetainedFrame (book : Book) (program : Program) (heap : Heap) :
    BendClosureMachine.Frame → Context book → Prop
  | function {q : Quan} {pc environment : Nat} {source : Term} {values : Env} :
      CodeDenotes program pc source → CapturedReady book program heap environment values →
      RetainedFrame book program heap (.function q pc environment)
        (.function q (Term.sub (Env.sub values) source))
  | argument {q : Quan} {pointer : Nat} {source : Term}
      (ready : RetainedReady book program heap pointer source)
      (value : Value book source) (live : q.live = true) :
      RetainedFrame book program heap (.argument q pointer) (.argument q source value live)
  | knownArgument {q : Quan} {pointer : Nat} {source : Term} :
      RetainedReady book program heap pointer source →
      RetainedFrame book program heap (.knownArgument q pointer) (.function q source)
  | lett {q : Quan} {pc environment : Nat} {source : Term} {values : Env}
      (code : CodeDenotes program pc source)
      (captured : CapturedReady book program heap environment values) (live : q.live = true) :
      RetainedFrame book program heap (.lett q pc environment)
        (.lett q (Term.sub (Subst.up (Env.sub values)) source) live)
  | first {q : Quan} {pc environment : Nat} {source : Term} {values : Env}
      (code : CodeDenotes program pc source)
      (captured : CapturedReady book program heap environment values) (live : q.live = true) :
      RetainedFrame book program heap (.first q pc environment)
        (.first q (Term.sub (Env.sub values) source) live)
  | second {q : Quan} {pointer : Nat} {source : Term}
      (ready : RetainedReady book program heap pointer source)
      (value : q.live = true → Value book source) :
      RetainedFrame book program heap (.second q pointer) (.second q source value)
  | rewrite {pc environment : Nat} {source motive : Term} {values : Env} :
      CodeDenotes program pc source → CapturedReady book program heap environment values →
      RetainedFrame book program heap (.rewrite pc environment)
        (.rewrite motive (Term.sub (Env.sub values) source))

abbrev RetainedStack (book : Book) (program : Program) (heap : Heap) :=
  All₂ (RetainedFrame book program heap)

theorem RetainedFrame.denotes {book : Book} {program : Program} {heap : Heap}
    {frame : BendClosureMachine.Frame} {context : Context book}
    (ready : RetainedFrame book program heap frame context) :
    FrameDenotes book program heap frame context := by
  cases ready with
  | function code captured => exact .function (.exact code captured.denotes)
  | argument ready value live => exact .argument ready.denotes value live
  | knownArgument ready => exact .knownArgument ready.denotes
  | lett code captured live => exact .lett (.exact code captured.denotes) live
  | first code captured live => exact .first (.exact code captured.denotes) live
  | second ready value => exact .second ready.denotes value
  | rewrite code captured => exact .rewrite (.exact code captured.denotes)

theorem RetainedFrame.extends {book : Book} {program : Program} {old next : Heap}
    {frame : BendClosureMachine.Frame} {context : Context book} (extension : Extends old next)
    (ready : RetainedFrame book program old frame context) :
    RetainedFrame book program next frame context := by
  cases ready with
  | function code captured => exact .function code (captured.extends extension)
  | argument ready value live => exact .argument (ready.extends extension) value live
  | knownArgument ready => exact .knownArgument (ready.extends extension)
  | lett code captured live => exact .lett code (captured.extends extension) live
  | first code captured live => exact .first code (captured.extends extension) live
  | second ready value => exact .second (ready.extends extension) value
  | rewrite code captured => exact .rewrite code (captured.extends extension)

theorem RetainedStack.denotes {book : Book} {program : Program} {heap : Heap}
    {frames : List BendClosureMachine.Frame} {contexts : List (Context book)}
    (ready : RetainedStack book program heap frames contexts) :
    StackDenotes book program heap frames contexts := by
  induction ready with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.denotes ih

theorem RetainedStack.extends {book : Book} {program : Program} {old next : Heap}
    {frames : List BendClosureMachine.Frame} {contexts : List (Context book)}
    (extension : Extends old next) (ready : RetainedStack book program old frames contexts) :
    RetainedStack book program next frames contexts := by
  induction ready with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.extends extension) ih

theorem retained_pair_fields {book : Book} {program : Program} {heap : Heap}
    {pointer first second : Nat} {q : Quan} {a b : Term}
    (ready : RetainedReady book program heap pointer (.Tup q a b))
    (row : heap.get? pointer = some (.pair q first second)) :
    RetainedReady book program heap first a ∧ RetainedReady book program heap second b := by
  generalize sourceEq : Term.Tup q a b = source at ready
  cases ready with
  | closure other code captured => rw [row] at other; cases other
  | pair other left right value =>
    cases sourceEq
    rw [row] at other; cases other; exact ⟨left,right⟩
  | application other left right value => cases sourceEq

/-- The actual projection step's newly installed argument frames inherit
recursive readiness from the real pair row. Future reopening uses these facts;
no Value assertion is inferred for an arbitrary resident application row. -/
theorem projection_retains_stack {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument pc environment handler first second : Nat) (q r : Quan)
    (a b : Term) (contexts : List (Context book))
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.prj handler))
    (argumentRow : state.heap.get? argument = some (.pair r first second))
    (argumentReady : RetainedReady book library.program state.heap argument (.Tup r a b))
    (stack : RetainedStack book library.program state.heap state.stack contexts)
    (live : q.live = true) (room : state.stack.length + 1 < limits.frames) :
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack
      (.function (Quan.fld r q) a :: .function q b :: contexts) := by
  obtain ⟨left,right⟩ := retained_pair_fields argumentReady argumentRow
  rw [step_projection limits library state function argument pc environment handler first second q r
    control functionRow instruction argumentRow live room]
  exact .cons (.knownArgument left) (.cons (.knownArgument right) stack)

#assert_axioms RetainedFrame.denotes
#assert_axioms RetainedFrame.extends
#assert_axioms RetainedStack.denotes
#assert_axioms RetainedStack.extends
#assert_axioms retained_pair_fields
#assert_axioms projection_retains_stack
end Minidregg.Theory.BendClosureSimulation
