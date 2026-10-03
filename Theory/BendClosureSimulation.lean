/- Exact source contexts for the actual bounded Bend closure controller.
This file is a proof seam, not a second evaluator. Runtime frames omit dead
motives, so exact reification is relational and retains those motives as ghosts.
The whole step/run simulation is not asserted by these context lemmas.
-/
import Theory.BendClosureMachine
import Theory.BendClosureReification

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

/-- One source evaluation context corresponding to a runtime continuation.
The argument/second constructors carry the CBV guards required by Eval. -/
inductive Context (book : Book) where
  | function (q : Quan) (argument : Term)
  | argument (q : Quan) (function : Term)
      (functionValue : Value book function) (live : q.live = true)
  | lett (q : Quan) (body : Term) (live : q.live = true)
  | first (q : Quan) (second : Term) (live : q.live = true)
  | second (q : Quan) (first : Term)
      (firstValue : q.live = true → Value book first)
  | rewrite (motive body : Term)

def Context.plug {book : Book} : Context book → Term → Term
  | .function q x, hole => .App q hole x
  | .argument q f _ _, hole => .App q f hole
  | .lett q body _, hole => .Let q hole body
  | .first q b _, hole => .Tup q hole b
  | .second q a _, hole => .Tup q a hole
  | .rewrite motive body, hole => .Rwt hole motive body

/-- Every represented context is an actual upstream live CBV context. -/
theorem Context.eval {book : Book} (context : Context book)
    {first last : Term} (transition : Eval book first last) :
    Eval book (context.plug first) (context.plug last) := by
  cases context with
  | function q argument => exact .app_f transition
  | argument q function value live => exact .app_x value live transition
  | lett q body live => exact .lett live transition
  | first q second live => exact .tup_a live transition
  | second q first value => exact .tup_b value transition
  | rewrite motive body => exact .rwt transition

def plug {book : Book} : List (Context book) → Term → Term
  | [], hole => hole
  | context :: rest, hole => plug rest (context.plug hole)

theorem plug_eval {book : Book} (contexts : List (Context book))
    {first last : Term} (transition : Eval book first last) :
    Eval book (plug contexts first) (plug contexts last) := by
  induction contexts generalizing first last with
  | nil => exact transition
  | cons context rest ih => exact ih (context.eval transition)

theorem plug_trace {book : Book} (contexts : List (Context book))
    {count : Nat} {first last : Term}
    (trace : BendLiveMachine.Trace book count first last) :
    BendLiveMachine.Trace book count (plug contexts first) (plug contexts last) := by
  induction trace with
  | refl term => exact .refl _
  | step transition rest ih => exact .step (plug_eval contexts transition) ih

/-- A code closure before it has been allocated as a heap row. -/
inductive ClosureDenotes (program : Program) (heap : Heap) :
    Nat → Nat → Term → Prop
  | exact {pc environment : Nat} {source : Term} {values : List Term} :
      CodeDenotes program pc source →
      EnvironmentDenotes program heap environment values →
      ClosureDenotes program heap pc environment (Term.sub (Env.sub values) source)

theorem ClosureDenotes.extends {program : Program} {old next : Heap}
    (extension : Extends old next) {pc environment : Nat} {term : Term}
    (exact : ClosureDenotes program old pc environment term) :
    ClosureDenotes program next pc environment term := by
  cases exact with
  | exact code captured => exact .exact code (captured.extends extension)

/-- The body of a pending let is still under its binder. Substituting with
Env.sub directly would capture/decrement the bound variable incorrectly. -/
inductive BodyDenotes (program : Program) (heap : Heap) :
    Nat → Nat → Term → Prop
  | exact {pc environment : Nat} {source : Term} {values : List Term} :
      CodeDenotes program pc source →
      EnvironmentDenotes program heap environment values →
      BodyDenotes program heap pc environment (Term.sub (Subst.up (Env.sub values)) source)

theorem BodyDenotes.extends {program : Program} {old next : Heap}
    (extension : Extends old next) {pc environment : Nat} {term : Term}
    (exact : BodyDenotes program old pc environment term) :
    BodyDenotes program next pc environment term := by
  cases exact with
  | exact code captured => exact .exact code (captured.extends extension)

/-- Exact interpretation of all seven actual Frame constructors.
KnownArgument is a function context: its retained argument may still be a Q0
thunk, and is not asserted to be a Value merely because it is heap-resident.
The rewrite motive is erased runtime information, retained only by this relation.
-/
inductive FrameDenotes (book : Book) (program : Program) (heap : Heap) :
    BendClosureMachine.Frame → Context book → Prop
  | function {q : Quan} {argument environment : Nat} {term : Term} :
      ClosureDenotes program heap argument environment term →
      FrameDenotes book program heap (.function q argument environment) (.function q term)
  | argument {q : Quan} {function : Nat} {term : Term}
      (exact : Denotes program heap function term)
      (value : Value book term) (live : q.live = true) :
      FrameDenotes book program heap (.argument q function) (.argument q term value live)
  | knownArgument {q : Quan} {argument : Nat} {term : Term} :
      Denotes program heap argument term →
      FrameDenotes book program heap (.knownArgument q argument) (.function q term)
  | lett {q : Quan} {body environment : Nat} {term : Term}
      (exact : BodyDenotes program heap body environment term) (live : q.live = true) :
      FrameDenotes book program heap (.lett q body environment) (.lett q term live)
  | first {q : Quan} {second environment : Nat} {term : Term}
      (exact : ClosureDenotes program heap second environment term) (live : q.live = true) :
      FrameDenotes book program heap (.first q second environment) (.first q term live)
  | second {q : Quan} {first : Nat} {term : Term}
      (exact : Denotes program heap first term)
      (value : q.live = true → Value book term) :
      FrameDenotes book program heap (.second q first) (.second q term value)
  | rewrite {body environment : Nat} {motive term : Term} :
      ClosureDenotes program heap body environment term →
      FrameDenotes book program heap (.rewrite body environment) (.rewrite motive term)

theorem FrameDenotes.extends {book : Book} {program : Program} {old next : Heap}
    (extension : Extends old next) {frame : BendClosureMachine.Frame} {context : Context book}
    (exact : FrameDenotes book program old frame context) :
    FrameDenotes book program next frame context := by
  cases exact with
  | function exact => exact .function (exact.extends extension)
  | argument exact value live => exact .argument (exact.extends extension) value live
  | knownArgument exact => exact .knownArgument (exact.extends extension)
  | lett exact live => exact .lett (exact.extends extension) live
  | first exact live => exact .first (exact.extends extension) live
  | second exact value => exact .second (exact.extends extension) value
  | rewrite exact => exact .rewrite (exact.extends extension)

abbrev StackDenotes (book : Book) (program : Program) (heap : Heap) :=
  All₂ (FrameDenotes book program heap)

theorem StackDenotes.extends {book : Book} {program : Program} {old next : Heap}
    (extension : Extends old next)
    {frames : List BendClosureMachine.Frame} {contexts : List (Context book)}
    (exact : StackDenotes book program old frames contexts) :
    StackDenotes book program next frames contexts := by
  induction exact with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.extends extension) ih

/-- Decoded argument spines keep order and quantities, including dead entries. -/
abbrev ArgumentsDenote (program : Program) (heap : Heap) :=
  All₂ (fun (pointer : Quan × Nat) (source : Arg) =>
    pointer.1 = source.1 ∧ Denotes program heap pointer.2 source.2)

/-- An unfinished walk retains the original call. The implication is built by
the individual Walk constructors; it is not permission to assume an Eval step.
Finishing a leaf or discovering underapplication consumes it below. -/
structure WalkPrefix (book : Book) (origin current : Term)
    (environment : Env) (arguments : List Arg) where
  name : String
  definition : Def
  originalArguments : List Arg
  origin_eq : origin = Term.spine (.Ref name) originalArguments
  found : Book.get book name = some definition
  values : Values book originalArguments
  resume : ∀ output, Walk book current environment arguments output →
    Walk book definition.v [] originalArguments output

theorem WalkPrefix.leaf {book : Book} {origin current : Term}
    {environment : Env} {arguments : List Arg}
    (walkPrefix : WalkPrefix book origin current environment arguments)
    (leaf : Term.node current = false) :
    Eval book origin (Term.spine (Term.sub (Env.sub environment) current) arguments) := by
  rw [walkPrefix.origin_eq]
  exact .call walkPrefix.found walkPrefix.values (walkPrefix.resume _ (.done leaf))

theorem WalkPrefix.need {book : Book} {origin current : Term} {environment : Env}
    (walkPrefix : WalkPrefix book origin current environment [])
    (need : Term.takes current = true) : Value book origin := by
  rw [walkPrefix.origin_eq]
  exact .call walkPrefix.found walkPrefix.values (walkPrefix.resume _ (.need need))

def WalkPrefix.lam {book : Book} {origin body argument : Term}
    {environment : Env} {arguments : List Arg} {p q : Quan}
    (walkPrefix : WalkPrefix book origin (.Lam p body) environment ((q, argument) :: arguments))
    (compatible : p.live = q.live) (copyable : p = .Q2 → Data argument) :
    WalkPrefix book origin body (argument :: environment) arguments :=
  {walkPrefix with resume := fun output next => walkPrefix.resume output (.lam compatible copyable next)}

def WalkPrefix.prj {book : Book} {origin handler first second : Term}
    {environment : Env} {arguments : List Arg} {q r : Quan}
    (walkPrefix : WalkPrefix book origin (.Prj handler) environment
      ((q, .Tup r first second) :: arguments))
    (live : q.live = true) :
    WalkPrefix book origin handler environment
      ((Quan.fld r q, first) :: (q, second) :: arguments) :=
  {walkPrefix with resume := fun output next => walkPrefix.resume output (.prj live next)}

def WalkPrefix.hit {book : Book} {origin yes no : Term} {label : String}
    {environment : Env} {arguments : List Arg} {q : Quan}
    (walkPrefix : WalkPrefix book origin (.Mat label yes no) environment
      ((q, .Lab label) :: arguments)) (live : q.live = true) :
    WalkPrefix book origin yes environment arguments :=
  {walkPrefix with resume := fun output next => walkPrefix.resume output (.hit live next)}

def WalkPrefix.miss {book : Book} {origin yes no : Term} {label actual : String}
    {environment : Env} {arguments : List Arg} {q : Quan}
    (walkPrefix : WalkPrefix book origin (.Mat label yes no) environment
      ((q, .Lab actual) :: arguments)) (live : q.live = true) (different : actual ≠ label) :
    WalkPrefix book origin no environment ((q, .Lab actual) :: arguments) :=
  {walkPrefix with resume := fun output next => walkPrefix.resume output (.miss live different next)}

def WalkPrefix.app {book : Book} {origin function : Term} {index : Nat}
    {environment : Env} {arguments : List Arg} {q : Quan}
    (walkPrefix : WalkPrefix book origin (.App q function (.Var index)) environment arguments)
    (node : Term.node (.App q function (.Var index)) = true) :
    WalkPrefix book origin function environment ((q, Env.sub environment index) :: arguments) :=
  {walkPrefix with resume := fun output next => walkPrefix.resume output (.app node next)}

#assert_axioms Context.eval
#assert_axioms plug_eval
#assert_axioms plug_trace
#assert_axioms ClosureDenotes.extends
#assert_axioms BodyDenotes.extends
#assert_axioms FrameDenotes.extends
#assert_axioms StackDenotes.extends
#assert_axioms WalkPrefix.leaf
#assert_axioms WalkPrefix.need
#assert_axioms WalkPrefix.lam
#assert_axioms WalkPrefix.prj
#assert_axioms WalkPrefix.hit
#assert_axioms WalkPrefix.miss
#assert_axioms WalkPrefix.app

/-- A retained closure can be an unevaluated Q0 thunk. Pair/application fast
return additionally requires a Value witness at the evaluatePointer consumer. -/
def ReadyPointer (book : Book) (program : Program) (heap : Heap)
    (pointer : Nat) (source : Term) : Prop :=
  Denotes program heap pointer source ∧
    ((∃ pc environment, heap.get? pointer = some (.closure pc environment)) ∨
      Value book source)

/-- Allocation must preserve this before Q2 bind may consume a true bit. -/
def DataCacheSound (program : Program) (state : State) : Prop :=
  ∀ pointer source, state.data[pointer]? = some true →
    Denotes program state.heap pointer source → Data source

/-- Exact source focus for actual Control. Case traversal keeps the original
call until a whole Walk finishes. Refusal is absent: it must retain the source
walkPrefix established before failure, not manufacture a fresh interpretation. -/
inductive ControlDenotes (book : Book) (program : Program) (heap : Heap) :
    Control → Term → Prop
  | evaluate {pc environment : Nat} {source : Term} :
      ClosureDenotes program heap pc environment source →
      ControlDenotes book program heap (.evaluate pc environment) source
  | lookupValue {index environment : Nat} {values : Env} :
      EnvironmentDenotes program heap environment values →
      ControlDenotes book program heap (.lookup index environment .evaluateValue)
        (Env.sub values index)
  | returned {pointer : Nat} {source : Term} :
      Denotes program heap pointer source → Value book source →
      ControlDenotes book program heap (.returned pointer) source
  | apply {q : Quan} {function argument : Nat} {f x : Term} :
      Denotes program heap function f → Denotes program heap argument x →
      Value book f → (q.live = true → Value book x) →
      ControlDenotes book program heap (.apply q function argument) (.App q f x)
  | unspine {pointer original : Nat} {args : List (Quan × Nat)}
      {head origin : Term} {arguments : List Arg} :
      Denotes program heap pointer head → Denotes program heap original origin →
      ArgumentsDenote program heap args arguments →
      origin = Term.spine head arguments → Values book arguments →
      ControlDenotes book program heap (.unspine pointer original args) origin
  | walk {pc environment original : Nat} {args : List (Quan × Nat)}
      {source origin : Term} {values : Env} {arguments : List Arg} :
      CodeDenotes program pc source →
      EnvironmentDenotes program heap environment values →
      Denotes program heap original origin →
      ArgumentsDenote program heap args arguments →
      WalkPrefix book origin source values arguments →
      ControlDenotes book program heap (.walk pc environment original args) origin
  | classify {pc environment original cursor : Nat} {args : List (Quan × Nat)}
      {source cursorSource origin : Term} {values : Env} {arguments : List Arg} :
      CodeDenotes program pc source → CodeDenotes program cursor cursorSource →
      Term.node source = Term.takes (Term.unspine cursorSource []).1 →
      EnvironmentDenotes program heap environment values →
      Denotes program heap original origin →
      ArgumentsDenote program heap args arguments →
      WalkPrefix book origin source values arguments →
      ControlDenotes book program heap (.classify pc environment original cursor args) origin
  | lookupWalk {index cursor function environment original : Nat}
      {quantity : Quan} {args : List (Quan × Nat)}
      {source origin : Term} {values remaining : Env} {arguments : List Arg} :
      CodeDenotes program function source →
      EnvironmentDenotes program heap environment values →
      EnvironmentDenotes program heap cursor remaining →
      Denotes program heap original origin →
      ArgumentsDenote program heap args arguments →
      WalkPrefix book origin source values
        ((quantity, Env.sub remaining index) :: arguments) →
      ControlDenotes book program heap
        (.lookup index cursor (.walkArgument quantity function environment original args)) origin
  | reverseArguments {pc environment : Nat} {remaining reversed : List (Quan × Nat)}
      {source : Term} {remainingSource reversedSource : List Arg} :
      ClosureDenotes program heap pc environment source →
      ArgumentsDenote program heap remaining remainingSource →
      ArgumentsDenote program heap reversed reversedSource →
      ControlDenotes book program heap (.reverseArguments pc environment remaining reversed)
        (Term.spine source (reversedSource.reverse ++ remainingSource))
  | installArguments {pc environment : Nat} {remaining : List (Quan × Nat)}
      {source : Term} {remainingSource : List Arg} :
      ClosureDenotes program heap pc environment source →
      ArgumentsDenote program heap remaining remainingSource →
      ControlDenotes book program heap (.installArguments pc environment remaining)
        (Term.spine source remainingSource.reverse)
  | complete {pointer : Nat} {source : Term} :
      Denotes program heap pointer source → Value book source →
      ControlDenotes book program heap (.complete pointer) source

/-- Exact stack/focus reification, with no pending frames allowed at complete.
Book.Live, Data cache soundness, and retained pointer readiness are additional
reachable-state invariants; this relation alone does not establish them. -/
inductive StateDenotes (book : Book) (program : Program) : State → Term → Prop
  | exact {state : State} {focus : Term} {contexts : List (Context book)} :
      ControlDenotes book program state.heap state.control focus →
      StackDenotes book program state.heap state.stack contexts →
      (∀ pointer, state.control = .complete pointer → state.stack = []) →
      StateDenotes book program state (plug contexts focus)

/-- Final extraction consumes the invariant. It does not assert that run has
established it: whole-controller preservation remains a separate obligation. -/
theorem StateDenotes.complete {book : Book} {program : Program}
    {state : State} {source : Term} {pointer : Nat}
    (exact : StateDenotes book program state source)
    (done : state.control = .complete pointer) :
    Denotes program state.heap pointer source ∧ Value book source := by
  cases exact with
  | exact control stack empty =>
    have noFrames := empty pointer done
    rw [noFrames] at stack
    cases stack
    rw [done] at control
    cases control with
    | complete term value => exact ⟨term, value⟩

/-- Binding retains every environment position, including Q0. -/
theorem captured_body_inst (body value : Term) (environment : Env) :
    Term.sub (Env.sub (value :: environment)) body =
      Term.inst (Term.sub (Subst.up (Env.sub environment)) body) value :=
  BendTT.env_inst

#assert_axioms StateDenotes.complete
#assert_axioms captured_body_inst


/-- These equations reduce the actual Work/StateT implementation; they are not
a second transition relation. Each is independent of semantic admission. -/
theorem step_annotation (limits : Limits) (library : Library) (state : State)
    (pc environment value type : Nat)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.ann value type)) :
    step limits library state =
      {state with control := .evaluate value environment, sourceSteps := state.sourceSteps + 1} := by
  simp [step, control, evaluate, code, found, sourceStep, go]
  rfl

theorem step_lookup_succ (limits : Limits) (library : Library) (state : State)
    (index environment value tail : Nat) (resume : LookupResume)
    (control : state.control = .lookup (index + 1) environment resume)
    (found : state.heap.get? environment = some (.environment value tail)) :
    step limits library state = {state with control := .lookup index tail resume} := by
  simp [step, control, lookup, row, found, go]
  rfl

theorem step_return_empty (limits : Limits) (library : Library) (state : State)
    (pointer : Nat) (control : state.control = .returned pointer)
    (empty : state.stack = []) :
    step limits library state = {state with control := .complete pointer} := by
  simp [step, control, returnValue, empty, go]
  rfl

/-- Exact operational/source join for an annotation microstep in any represented
continuation. It performs one source Eval, retaining exact source substitution. -/
theorem annotation_source {book : Book} (contexts : List (Context book))
    (value type : Term) (environment : Env) :
    Eval book
      (plug contexts (Term.sub (Env.sub environment) (.Ann value type)))
      (plug contexts (Term.sub (Env.sub environment) value)) :=
  plug_eval contexts .ann

/-- An environment successor lookup is administrative: no Q0 entry is skipped
and the exact substituted variable is unchanged after advancing one row. -/
theorem lookup_succ_source (index : Nat) (head : Term) (tail : Env) :
    Env.sub (head :: tail) (index + 1) = Env.sub tail index := rfl

#assert_axioms step_annotation
#assert_axioms step_lookup_succ
#assert_axioms step_return_empty
#assert_axioms annotation_source
#assert_axioms lookup_succ_source


/-- Correspondence is ordered, so duplicate names preserve the same first
definition semantics as Book.get rather than merely proving membership. -/
private theorem lookup_source_list (program : Program)
    {entries : List (Nat × Nat)} {definitions : Book}
    (correspondence : All₂ (fun entry definition =>
      program.names[entry.1]? = some definition.k ∧
      CodeDenotes program entry.2 definition.v) entries definitions) :
    ∀ name pointer,
      (entries.find? (fun entry => program.names[entry.1]? == some name)).map Prod.snd =
        some pointer →
      ∃ definition, definitions.find? (fun definition => definition.k == name) = some definition ∧
        CodeDenotes program pointer definition.v := by
  induction correspondence with
  | nil =>
    intro name pointer found
    simp at found
  | @cons entry definition entries definitions paired rest ih =>
    intro name pointer found
    by_cases same : definition.k = name
    · simp [List.find?, paired.1, same] at found
      subst pointer
      exact ⟨definition, by simp [List.find?, same], paired.2⟩
    · have different : (definition.k == name) = false := by
        cases equal : (definition.k == name) with
        | false => rfl
        | true => exact False.elim (same (beq_iff_eq.mp equal))
      have tailFound :
          (entries.find? (fun entry => program.names[entry.1]? == some name)).map Prod.snd =
            some pointer := by
        simpa [List.find?, paired.1, different] using found
      obtain ⟨result, selected, exact⟩ := ih name pointer tailFound
      exact ⟨result, by simpa [List.find?, different] using selected, exact⟩

theorem lookup_source {library : Library} {book : Book} {name : String} {pointer : Nat}
    (correspondence : library.SourceCorrespondence book)
    (found : library.lookupName name = some pointer) :
    ∃ definition, Book.get book name = some definition ∧
      CodeDenotes library.program pointer definition.v :=
  lookup_source_list library.program correspondence name pointer found

/-- Literal heap edges traversed by the implementation's lookup control. -/
inductive LookupPath (heap : Heap) : Nat → Nat → Nat → Prop
  | zero {environment value tail : Nat} :
      heap.get? environment = some (.environment value tail) →
      LookupPath heap 0 environment value
  | succ {index environment value tail result : Nat} :
      heap.get? environment = some (.environment value tail) →
      LookupPath heap index tail result →
      LookupPath heap (index + 1) environment result

theorem environment_lookup {program : Program} {heap : Heap} (index : Nat)
    {environment : Nat} {values : Env} {source : Term}
    (captured : EnvironmentDenotes program heap environment values)
    (found : values[index]? = some source) :
    ∃ pointer, LookupPath heap index environment pointer ∧
      Denotes program heap pointer source := by
  induction index generalizing environment values with
  | zero =>
    cases captured with
    | nil row => simp at found
    | cons row head tail =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst source
      exact ⟨_, .zero row, head⟩
  | succ index ih =>
    cases captured with
    | nil row => simp at found
    | cons row head tail =>
      simp only [List.getElem?_cons_succ] at found
      obtain ⟨pointer, path, exact⟩ := ih tail found
      exact ⟨pointer, .succ row path, exact⟩

theorem ReadyPointer.extends {book : Book} {program : Program} {old next : Heap}
    (extension : Extends old next) {pointer : Nat} {source : Term}
    (ready : ReadyPointer book program old pointer source) :
    ReadyPointer book program next pointer source := by
  obtain ⟨exact, closure | value⟩ := ready
  · obtain ⟨pc, environment, row⟩ := closure
    exact ⟨exact.extends extension, Or.inl ⟨pc, environment, extension _ _ row⟩⟩
  · exact ⟨exact.extends extension, Or.inr value⟩

/-- Actual annotation step with its exact next control denotation and the
upstream Eval edge. No source oracle is run to obtain the transition. -/
theorem annotation_microstep {book : Book}
    (limits : Limits) (library : Library) (state : State)
    (pc environment value type : Nat) (source sourceType : Term) (values : Env)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.ann value type))
    (codeExact : CodeDenotes library.program value source)
    (typeExact : CodeDenotes library.program type sourceType)
    (captured : EnvironmentDenotes library.program state.heap environment values) :
    let next := {state with control := .evaluate value environment, sourceSteps := state.sourceSteps + 1}
    step limits library state = next ∧
      ControlDenotes book library.program state.heap state.control
        (Term.sub (Env.sub values) (.Ann source sourceType)) ∧
      ControlDenotes book library.program next.heap next.control
        (Term.sub (Env.sub values) source) ∧
      Eval book (Term.sub (Env.sub values) (.Ann source sourceType))
        (Term.sub (Env.sub values) source) :=
  ⟨step_annotation limits library state pc environment value type control found,
    by rw [control]; exact .evaluate (.exact (.ann found codeExact typeExact) captured),
    .evaluate (.exact codeExact captured), .ann⟩

#assert_axioms lookup_source
#assert_axioms environment_lookup
#assert_axioms ReadyPointer.extends
#assert_axioms annotation_microstep

end Minidregg.Theory.BendClosureSimulation

