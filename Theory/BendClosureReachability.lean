/- Strong control-specific readiness for the ACTUAL closure machine.
This is the invariant being established from startup through implementation
transitions. It distinguishes original pending calls, value heads, and reopened
captures. Defining it does not assert global transition preservation. -/
import Theory.BendClosurePendingCall
import Theory.BendClosureStartup

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

inductive SpineHeadReady (book : Book) (program : Program) (heap : Heap) : Nat → Term → Prop
  | reference {pointer pc environment : Nat} {name : String} {values : Env} :
      heap.get? pointer = some (.closure pc environment) →
      CodeDenotes program pc (.Ref name) → CapturedReady book program heap environment values →
      SpineHeadReady book program heap pointer (.Ref name)
  | value {pointer : Nat} {source : Term} :
      RetainedReady book program heap pointer source → Value book source →
      SpineHeadReady book program heap pointer source

theorem SpineHeadReady.retained {book : Book} {program : Program} {heap : Heap}
    {pointer : Nat} {source : Term} (ready : SpineHeadReady book program heap pointer source) :
    RetainedReady book program heap pointer source := by
  cases ready with
  | reference row code captured => exact .closure row code captured
  | value ready value => exact ready

theorem SpineHeadReady.extends {book : Book} {program : Program} {old next : Heap}
    {pointer : Nat} {source : Term} (extension : Extends old next)
    (ready : SpineHeadReady book program old pointer source) : SpineHeadReady book program next pointer source := by
  cases ready with
  | reference row code captured => exact .reference (extension _ _ row) code (captured.extends extension)
  | value ready value => exact .value (ready.extends extension) value

abbrev RetainedArguments (book : Book) (program : Program) (heap : Heap) :=
  All₂ (fun (pointer : Quan × Nat) (source : Arg) =>
    pointer.1 = source.1 ∧ RetainedReady book program heap pointer.2 source.2)

theorem RetainedArguments.denotes {book : Book} {program : Program} {heap : Heap}
    {args : List (Quan × Nat)} {sources : List Arg}
    (ready : RetainedArguments book program heap args sources) : ArgumentsDenote program heap args sources := by
  induction ready with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.1,head.2.denotes⟩ ih

theorem RetainedArguments.extends {book : Book} {program : Program} {old next : Heap}
    {args : List (Quan × Nat)} {sources : List Arg} (extension : Extends old next)
    (ready : RetainedArguments book program old args sources) : RetainedArguments book program next args sources := by
  induction ready with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.1,head.2.extends extension⟩ ih

inductive ReadyControl (book : Book) (program : Program) (heap : Heap) : Control → Term → Prop
  | basic {control : Control} {source : Term} :
      RetainedFocus book program heap control source → ReadyControl book program heap control source
  | lookupValue {index environment : Nat} {values : Env} :
      CapturedReady book program heap environment values →
      ReadyControl book program heap (.lookup index environment .evaluateValue) (Env.sub values index)
  | unspine {pointer original : Nat} {args : List (Quan × Nat)}
      {head origin : Term} {arguments : List Arg} :
      SpineHeadReady book program heap pointer head → PendingCall book program heap original origin →
      RetainedArguments book program heap args arguments →
      origin = Term.spine head arguments → Values book arguments →
      ReadyControl book program heap (.unspine pointer original args) origin
  | walk {pc environment original : Nat} {args : List (Quan × Nat)}
      {source origin : Term} {values : Env} {arguments : List Arg} :
      CodeDenotes program pc source → CapturedReady book program heap environment values →
      PendingCall book program heap original origin → RetainedArguments book program heap args arguments →
      WalkPrefix book origin source values arguments →
      ReadyControl book program heap (.walk pc environment original args) origin
  | classify {pc environment original cursor : Nat} {args : List (Quan × Nat)}
      {source cursorSource origin : Term} {values : Env} {arguments : List Arg} :
      CodeDenotes program pc source → CodeDenotes program cursor cursorSource →
      (∃ q f index, source = .App q f (.Var index)) →
      Term.node source = Term.takes (Term.unspine cursorSource []).1 →
      CapturedReady book program heap environment values → PendingCall book program heap original origin →
      RetainedArguments book program heap args arguments → WalkPrefix book origin source values arguments →
      ReadyControl book program heap (.classify pc environment original cursor args) origin
  | lookupWalk {index cursor function environment original : Nat} {q : Quan}
      {args : List (Quan × Nat)} {source origin : Term} {values remaining : Env} {arguments : List Arg} :
      CodeDenotes program function source → CapturedReady book program heap environment values →
      CapturedReady book program heap cursor remaining → PendingCall book program heap original origin →
      RetainedArguments book program heap args arguments →
      WalkPrefix book origin source values ((q,Env.sub remaining index) :: arguments) →
      ReadyControl book program heap (.lookup index cursor (.walkArgument q function environment original args)) origin
  | reverseArguments {pc environment : Nat} {remaining reversed : List (Quan × Nat)}
      {source : Term} {values : Env} {left right : List Arg} :
      CodeDenotes program pc source → CapturedReady book program heap environment values →
      RetainedArguments book program heap remaining left → RetainedArguments book program heap reversed right →
      ReadyControl book program heap (.reverseArguments pc environment remaining reversed)
        (Term.spine (Term.sub (Env.sub values) source) (right.reverse ++ left))
  | installArguments {pc environment : Nat} {remaining : List (Quan × Nat)}
      {source : Term} {values : Env} {arguments : List Arg} :
      CodeDenotes program pc source → CapturedReady book program heap environment values →
      RetainedArguments book program heap remaining arguments →
      ReadyControl book program heap (.installArguments pc environment remaining)
        (Term.spine (Term.sub (Env.sub values) source) arguments.reverse)

theorem ReadyControl.denotes {book : Book} {program : Program} {heap : Heap}
    {control : Control} {source : Term} (ready : ReadyControl book program heap control source) :
    ControlDenotes book program heap control source := by
  cases ready with
  | basic ready => exact ready.denotes
  | lookupValue captured => exact .lookupValue captured.denotes
  | unspine head original args identity values =>
    exact .unspine head.retained.denotes original.denotes args.denotes identity values
  | walk code captured original args walkPrefix =>
    exact .walk code captured.denotes original.denotes args.denotes walkPrefix
  | classify code cursor application classifier captured original args walkPrefix =>
    exact .classify code cursor classifier captured.denotes original.denotes args.denotes walkPrefix
  | lookupWalk code captured cursor original args walkPrefix =>
    exact .lookupWalk code captured.denotes cursor.denotes original.denotes args.denotes walkPrefix
  | reverseArguments code captured left right =>
    exact .reverseArguments (.exact code captured.denotes) left.denotes right.denotes
  | installArguments code captured args =>
    exact .installArguments (.exact code captured.denotes) args.denotes

theorem ReadyControl.extends {book : Book} {program : Program} {old next : Heap}
    {control : Control} {source : Term} (extension : Extends old next)
    (ready : ReadyControl book program old control source) : ReadyControl book program next control source := by
  cases ready with
  | basic ready => exact .basic (ready.extends extension)
  | lookupValue captured => exact .lookupValue (captured.extends extension)
  | unspine head original args identity values =>
    exact .unspine (head.extends extension) (original.extends extension) (args.extends extension) identity values
  | walk code captured original args walkPrefix =>
    exact .walk code (captured.extends extension) (original.extends extension) (args.extends extension) walkPrefix
  | classify code cursor application classifier captured original args walkPrefix =>
    exact .classify code cursor application classifier (captured.extends extension)
      (original.extends extension) (args.extends extension) walkPrefix
  | lookupWalk code captured cursor original args walkPrefix =>
    exact .lookupWalk code (captured.extends extension) (cursor.extends extension)
      (original.extends extension) (args.extends extension) walkPrefix
  | reverseArguments code captured left right =>
    exact .reverseArguments code (captured.extends extension) (left.extends extension) (right.extends extension)
  | installArguments code captured args =>
    exact .installArguments code (captured.extends extension) (args.extends extension)

inductive ReadyState (book : Book) (program : Program) : State → Term → Prop
  | exact {state : State} {focus : Term} {contexts : List (Context book)} :
      ReadyControl book program state.heap state.control focus →
      RetainedStack book program state.heap state.stack contexts →
      CacheCertified program state.heap state.data → state.heap.get? 0 = some .nil →
      (∀ pointer, state.control = .complete pointer → state.stack = []) →
      ReadyState book program state (plug contexts focus)

theorem ReadyState.denotes {book : Book} {program : Program} {state : State} {source : Term}
    (ready : ReadyState book program state source) : StateDenotes book program state source := by
  cases ready with
  | exact control stack cache empty complete => exact .exact control.denotes stack.denotes complete

theorem ReadyState.start {book : Book} (limits : Limits) (library : Library) (entry : Nat)
    (state : State) (source : Term) (started : start limits library entry = .ok state)
    (entryExact : CodeDenotes library.program entry source) : ReadyState book library.program state source := by
  obtain ⟨_,focus,stack,cache,_,_⟩ := start_ready (book := book) limits library entry state source started entryExact
  obtain ⟨empty,_,_,control,_⟩ := start_fields limits library entry state started
  exact ReadyState.exact (contexts := []) (.basic focus) stack cache empty
    (by intro pointer impossible; rw [control] at impossible; cases impossible)

#assert_axioms SpineHeadReady.retained
#assert_axioms SpineHeadReady.extends
#assert_axioms RetainedArguments.denotes
#assert_axioms RetainedArguments.extends
#assert_axioms ReadyControl.denotes
#assert_axioms ReadyControl.extends
#assert_axioms ReadyState.denotes
#assert_axioms ReadyState.start
end Minidregg.Theory.BendClosureSimulation
