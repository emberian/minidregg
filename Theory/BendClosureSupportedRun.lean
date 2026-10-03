/- Source refinement of explicitly handled runs of the ACTUAL closure machine.
This module assembles branch proofs into Machine.run traces. Handled is a
concrete derivation of branch preconditions, not an assumed Eval or assumed
postcondition. Covered is an explicit boundary: this file does not establish
that every reachable machine branch has a Handled derivation. In particular,
call-walk, projection/matching, lookup and refusal coverage remain open. -/
import Theory.BendClosureBeta
import Theory.BendClosureValueSteps
import Theory.BendClosureReturnSteps
import Theory.BendClosureSpineSteps
import Theory.BendExecutionTrace

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

/-- A local branch is supported only from its exact operational and source
premises. No constructor accepts the refinement theorem as a premise. -/
inductive Handled (book : Book) (limits : Limits) (library : Library) : State → Term → Prop
  | reverseCons   
    (state : State) (pc environment : Nat) (argument : Quan × Nat)
    (remaining reversed : List (Quan × Nat)) (sourceArgument : Arg)
    (remainingSource reversedSource : List Arg) (source : Term)
    (contexts : List (Context book))
    (control : state.control = .reverseArguments pc environment (argument :: remaining) reversed)
    (leaf : ClosureDenotes library.program state.heap pc environment source)
    (head : argument.1 = sourceArgument.1 ∧
      Denotes library.program state.heap argument.2 sourceArgument.2)
    (left : ArgumentsDenote library.program state.heap remaining remainingSource)
    (right : ArgumentsDenote library.program state.heap reversed reversedSource)
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
      Handled book limits library state (plug contexts (Term.spine source (reversedSource.reverse ++ sourceArgument :: remainingSource)))
  | reverseNil   
    (state : State) (pc environment : Nat) (reversed : List (Quan × Nat))
    (reversedSource : List Arg) (source : Term) (contexts : List (Context book))
    (control : state.control = .reverseArguments pc environment [] reversed)
    (leaf : ClosureDenotes library.program state.heap pc environment source)
    (right : ArgumentsDenote library.program state.heap reversed reversedSource)
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
      Handled book limits library state (plug contexts (Term.spine source reversedSource.reverse))
  | installCons   
    (state : State) (pc environment : Nat) (q : Quan) (pointer : Nat)
    (remaining : List (Quan × Nat)) (argument : Term)
    (remainingSource : List Arg) (source : Term) (contexts : List (Context book))
    (control : state.control = .installArguments pc environment ((q,pointer) :: remaining))
    (leaf : ClosureDenotes library.program state.heap pc environment source)
    (head : Denotes library.program state.heap pointer argument)
    (tail : ArgumentsDenote library.program state.heap remaining remainingSource)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : state.stack.length < limits.frames) :
      Handled book limits library state (plug contexts (Term.spine source ((q,argument) :: remainingSource).reverse))
  | installNil   
    (state : State) (pc environment : Nat) (source : Term) (contexts : List (Context book))
    (control : state.control = .installArguments pc environment [])
    (leaf : ClosureDenotes library.program state.heap pc environment source)
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
      Handled book limits library state (plug contexts source)
  | application   
    (state : State) (pc environment function argument : Nat) (q : Quan)
    (f x : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.app q function argument))
    (functionExact : CodeDenotes library.program function f)
    (argumentExact : CodeDenotes library.program argument x)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : state.stack.length < limits.frames) :
      Handled book limits library state (plug contexts (Term.sub (Env.sub values) (.App q f x)))
  | liveLet   
    (state : State) (pc environment value body : Nat) (q : Quan)
    (v f : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.lett q value body))
    (valueExact : CodeDenotes library.program value v)
    (bodyExact : CodeDenotes library.program body f)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (live : q.live = true) (room : state.stack.length < limits.frames) :
      Handled book limits library state (plug contexts (Term.sub (Env.sub values) (.Let q v f)))
  | livePair   
    (state : State) (pc environment first second : Nat) (q : Quan)
    (a b : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.tup q first second))
    (firstExact : CodeDenotes library.program first a)
    (secondExact : CodeDenotes library.program second b)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (live : q.live = true) (room : state.stack.length < limits.frames) :
      Handled book limits library state (plug contexts (Term.sub (Env.sub values) (.Tup q a b)))
  | rewrite   
    (state : State) (pc environment evidence motive body : Nat)
    (e p f : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.rwt evidence motive body))
    (evidenceExact : CodeDenotes library.program evidence e)
    (motiveExact : CodeDenotes library.program motive p)
    (bodyExact : CodeDenotes library.program body f)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : state.stack.length < limits.frames) :
      Handled book limits library state (plug contexts (Term.sub (Env.sub values) (.Rwt e p f)))
  | directValue   
    (state : State) (pc environment pointer : Nat) (instruction : Code) (heap : Heap)
    (source : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some instruction)
    (direct : directValue instruction = true)
    (sourceExact : CodeDenotes library.program pc source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure pc environment) = .ok (pointer, heap)) :
      Handled book limits library state (plug contexts (Term.sub (Env.sub values) source))
  | beta   
    (state : State) (function argument pc environment body nextEnvironment : Nat)
    (heap : Heap) (source argumentSource : Term) (values : Env)
    (contexts : List (Context book)) (binder quantity : Quan)
    (control : state.control = .apply quantity function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.lam binder body))
    (bodyExact : CodeDenotes library.program body source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (argumentExact : Denotes library.program state.heap argument argumentSource)
    (argumentValue : quantity.live = true → Value book argumentSource)
    (compatible : binder.live = quantity.live)
    (copied : binder = .Q2 → state.data[argument]?.getD false = true)
    (cache : CacheCertified library.program state.heap state.data)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.environment argument environment) = .ok (nextEnvironment, heap)) :
      Handled book limits library state (plug contexts (.App quantity (Term.sub (Env.sub values) (.Lam binder source)) argumentSource))
  | returnArgument   
    (state : State) (pointer function : Nat) (q : Quan)
    (rest : List BendClosureMachine.Frame) (contexts : List (Context book))
    (argumentSource functionSource : Term)
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .argument q function :: rest)
    (argumentExact : Denotes library.program state.heap pointer argumentSource)
    (argumentValue : Value book argumentSource)
    (functionExact : Denotes library.program state.heap function functionSource)
    (functionValue : Value book functionSource) (live : q.live = true)
    (stack : StackDenotes book library.program state.heap rest contexts) :
      Handled book limits library state (plug contexts (.App q functionSource argumentSource))
  | returnFunction   
    (state : State) (pointer argument environment : Nat) (q : Quan)
    (rest : List BendClosureMachine.Frame) (contexts : List (Context book))
    (functionSource argumentSource : Term)
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .function q argument environment :: rest)
    (live : q.live = true) (room : rest.length < limits.frames)
    (functionExact : Denotes library.program state.heap pointer functionSource)
    (functionValue : Value book functionSource)
    (argumentExact : ClosureDenotes library.program state.heap argument environment argumentSource)
    (stack : StackDenotes book library.program state.heap rest contexts) :
      Handled book limits library state (plug contexts (.App q functionSource argumentSource))
  | returnEmpty   
    (state : State) (pointer : Nat) (source : Term)
    (control : state.control = .returned pointer) (empty : state.stack = [])
    (exact : Denotes library.program state.heap pointer source) (value : Value book source) :
      Handled book limits library state (source)

  | complete (state : State) (source : Term) (pointer : Nat)
      (done : state.control = .complete pointer)
      (represented : StateDenotes book library.program state source) :
      Handled book limits library state source

  | annotation (state : State) (pc environment value type : Nat)
      (source sourceType : Term) (values : Env) (contexts : List (Context book))
      (control : state.control = .evaluate pc environment)
      (found : library.program.code[pc]? = some (.ann value type))
      (codeExact : CodeDenotes library.program value source)
      (typeExact : CodeDenotes library.program type sourceType)
      (captured : EnvironmentDenotes library.program state.heap environment values)
      (stack : StackDenotes book library.program state.heap state.stack contexts) :
      Handled book limits library state
        (plug contexts (Term.sub (Env.sub values) (.Ann source sourceType)))
  | lookupSuccessor (state : State) (index environment value tail : Nat)
      (head : Term) (values : Env) (contexts : List (Context book))
      (control : state.control = .lookup (index + 1) environment .evaluateValue)
      (found : state.heap.get? environment = some (.environment value tail))
      (headExact : Denotes library.program state.heap value head)
      (captured : EnvironmentDenotes library.program state.heap tail values)
      (stack : StackDenotes book library.program state.heap state.stack contexts) :
      Handled book limits library state (plug contexts (Env.sub values index))

/-- One physical tick either leaves the represented source unchanged or
performs exactly one upstream Eval. The diagnostic source count follows it. -/
theorem Handled.refines {book : Book} {limits : Limits} {library : Library}
    {state : State} {source : Term} (handled : Handled book limits library state source) :
    ∃ nextSource, StateDenotes book library.program (step limits library state) nextSource ∧
      ((nextSource = source ∧ (step limits library state).sourceSteps = state.sourceSteps) ∨
       (Eval book source nextSource ∧ (step limits library state).sourceSteps = state.sourceSteps + 1)) := by
  cases handled with
  | annotation pc environment value type source sourceType values contexts control found codeExact typeExact captured stack =>
    have transition := step_annotation limits library state pc environment value type control found
    refine ⟨plug contexts (Term.sub (Env.sub values) source), ?_, Or.inr ⟨?_, ?_⟩⟩
    · rw [transition]
      exact evaluate_state rfl (.exact codeExact captured) stack
    · exact plug_eval contexts .ann
    · rw [transition]
  | lookupSuccessor index environment value tail head values contexts control found headExact captured stack =>
    have transition := step_lookup_succ limits library state index environment value tail .evaluateValue control found
    refine ⟨plug contexts (Env.sub values index), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · rw [transition]
      exact StateDenotes.exact (contexts := contexts) (.lookupValue captured) stack
        (by intro pointer impossible; cases impossible)
    · rw [transition]

  | complete source pointer done represented =>
    have stable := complete_absorbing limits library state pointer done
    exact ⟨source, by simpa only [stable] using represented, Or.inl ⟨rfl, by rw [stable]⟩⟩

  | @reverseCons pc environment argument remaining reversed sourceArgument remainingSource reversedSource source contexts control leaf head left right stack =>
    have result := reverse_cons_stutter limits library state pc environment argument remaining reversed sourceArgument remainingSource reversedSource source contexts control leaf head left right stack
    exact ⟨plug contexts (Term.spine source (reversedSource.reverse ++ sourceArgument :: remainingSource)), result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @reverseNil pc environment reversed reversedSource source contexts control leaf right stack =>
    have result := reverse_nil_stutter limits library state pc environment reversed reversedSource source contexts control leaf right stack
    exact ⟨plug contexts (Term.spine source reversedSource.reverse), result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @installCons pc environment q pointer remaining argument remainingSource source contexts control leaf head tail stack room =>
    have result := install_cons_stutter limits library state pc environment q pointer remaining argument remainingSource source contexts control leaf head tail stack room
    exact ⟨plug contexts (Term.spine source ((q,argument) :: remainingSource).reverse), result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @installNil pc environment source contexts control leaf stack =>
    have result := install_nil_stutter limits library state pc environment source contexts control leaf stack
    exact ⟨plug contexts source, result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @application pc environment function argument q f x values contexts control found functionExact argumentExact captured stack room =>
    have result := application_stutter limits library state pc environment function argument q f x values contexts control found functionExact argumentExact captured stack room
    exact ⟨plug contexts (Term.sub (Env.sub values) (.App q f x)), result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @liveLet pc environment value body q v f values contexts control found valueExact bodyExact captured stack live room =>
    have result := live_let_stutter limits library state pc environment value body q v f values contexts control found valueExact bodyExact captured stack live room
    exact ⟨plug contexts (Term.sub (Env.sub values) (.Let q v f)), result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @livePair pc environment first second q a b values contexts control found firstExact secondExact captured stack live room =>
    have result := live_pair_stutter limits library state pc environment first second q a b values contexts control found firstExact secondExact captured stack live room
    exact ⟨plug contexts (Term.sub (Env.sub values) (.Tup q a b)), result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @rewrite pc environment evidence motive body e p f values contexts control found evidenceExact motiveExact bodyExact captured stack room =>
    have result := rewrite_stutter limits library state pc environment evidence motive body e p f values contexts control found evidenceExact motiveExact bodyExact captured stack room
    exact ⟨plug contexts (Term.sub (Env.sub values) (.Rwt e p f)), result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @directValue pc environment pointer instruction heap source values contexts control found direct sourceExact captured stack allocated =>
    have result := direct_value_stutter limits library state pc environment pointer instruction heap source values contexts control found direct sourceExact captured stack allocated
    exact ⟨plug contexts (Term.sub (Env.sub values) source), result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @beta function argument pc environment body nextEnvironment heap source argumentSource values contexts binder quantity control functionRow instruction bodyExact captured argumentExact argumentValue compatible copied cache stack allocated =>
    have result := beta_source limits library state function argument pc environment body nextEnvironment heap source argumentSource values contexts binder quantity control functionRow instruction bodyExact captured argumentExact argumentValue compatible copied cache stack allocated
    exact ⟨plug contexts (Term.sub (Env.sub (argumentSource :: values)) source), result.2.1, Or.inr ⟨result.2.2.1, result.2.2.2⟩⟩
  | @returnArgument pointer function q rest contexts argumentSource functionSource control stackShape argumentExact argumentValue functionExact functionValue live stack =>
    have result := return_argument_stutter limits library state pointer function q rest contexts argumentSource functionSource control stackShape argumentExact argumentValue functionExact functionValue live stack
    exact ⟨plug contexts (.App q functionSource argumentSource), result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @returnFunction pointer argument environment q rest contexts functionSource argumentSource control stackShape live room functionExact functionValue argumentExact stack =>
    have result := return_function_live_stutter limits library state pointer argument environment q rest contexts functionSource argumentSource control stackShape live room functionExact functionValue argumentExact stack
    exact ⟨plug contexts (.App q functionSource argumentSource), result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩
  | @returnEmpty pointer source control empty exact value =>
    have result := return_empty_stutter limits library state pointer source control empty exact value
    exact ⟨source, result.2.1, Or.inl ⟨rfl, result.2.2⟩⟩

/-- Coverage is about concrete branches along the actual deterministic run.
It contains no source Eval, Trace, or successor StateDenotes conclusion.
Its universal quantifier preserves erased source contexts such as motives. -/
def Covered (book : Book) (limits : Limits) (library : Library) : Nat → State → Prop
  | 0, _ => True
  | ticks + 1, state =>
      (∀ source, StateDenotes book library.program state source →
        Handled book limits library state source) ∧
      Covered book limits library ticks (step limits library state)

theorem Covered.complete {book : Book} {limits : Limits} {library : Library}
    (ticks : Nat) (state : State) (pointer : Nat)
    (done : state.control = .complete pointer) : Covered book limits library ticks state := by
  induction ticks with
  | zero => trivial
  | succ ticks ih =>
    refine ⟨fun source represented => .complete state source pointer done represented, ?_⟩
    simpa only [complete_absorbing limits library state pointer done] using ih

/-- Coverage splits at the same actual state as Machine.run_add, allowing a
persisted segment to resume without changing its source origin or count. -/
theorem covered_add {book : Book} {limits : Limits} {library : Library}
    (first second : Nat) (state : State) :
    Covered book limits library (first + second) state ↔
      Covered book limits library first state ∧
      Covered book limits library second (run limits library first state) := by
  induction first generalizing state with
  | zero => simp [Covered, run]
  | succ first ih => simp [Nat.succ_add, Covered, run, ih, and_assoc]

/-- Actual run-level source trace, conditional on the explicit handled boundary.
This is not a whole-controller coverage or sufficient-capacity theorem. -/
theorem covered_run {book : Book} {limits : Limits} {library : Library}
    (ticks : Nat) (state : State) (source : Term)
    (represented : StateDenotes book library.program state source)
    (coverage : Covered book limits library ticks state) :
    ∃ count result, BendLiveMachine.Trace book count source result ∧
      StateDenotes book library.program (run limits library ticks state) result ∧
      (run limits library ticks state).sourceSteps = state.sourceSteps + count := by
  induction ticks generalizing state source with
  | zero => exact ⟨0, source, .refl source, represented, by simp [run]⟩
  | succ ticks ih =>
    obtain ⟨localCoverage, remaining⟩ := coverage
    obtain ⟨nextSource, nextExact, stutter | advance⟩ := (localCoverage source represented).refines
    · obtain ⟨same, counter⟩ := stutter
      subst nextSource
      obtain ⟨count, result, trace, exact, total⟩ := ih _ source nextExact remaining
      refine ⟨count, result, trace, exact, ?_⟩
      simpa only [run, counter] using total
    · obtain ⟨sourceStep, counter⟩ := advance
      obtain ⟨count, result, trace, exact, total⟩ := ih _ nextSource nextExact remaining
      refine ⟨count + 1, result, .step sourceStep trace, exact, ?_⟩
      dsimp only [run]
      omega

/-- A completed covered run returns exactly the final source Value. -/
theorem covered_run_complete {book : Book} {limits : Limits} {library : Library}
    (ticks : Nat) (state : State) (source : Term) (pointer : Nat)
    (represented : StateDenotes book library.program state source)
    (coverage : Covered book limits library ticks state)
    (complete : (run limits library ticks state).control = .complete pointer) :
    ∃ count result, BendLiveMachine.Trace book count source result ∧
      Denotes library.program (run limits library ticks state).heap pointer result ∧
      Value book result ∧
      (run limits library ticks state).sourceSteps = state.sourceSteps + count := by
  obtain ⟨count, result, trace, exact, counter⟩ := covered_run ticks state source represented coverage
  obtain ⟨denotes, value⟩ := exact.complete complete
  exact ⟨count, result, trace, denotes, value, counter⟩

/-- The central source invariant records a real source prefix and exact current
reification. Cache and recursive heap readiness are additional coverage
obligations; this definition does not claim their global preservation. -/
def SourceInvariant (book : Book) (program : Program) (origin : Term)
    (initialCount : Nat) (state : State) : Prop :=
  ∃ count residual, BendLiveMachine.Trace book count origin residual ∧
    StateDenotes book program state residual ∧ state.sourceSteps = initialCount + count

theorem SourceInvariant.initial {book : Book} {program : Program}
    {state : State} {source : Term} (represented : StateDenotes book program state source) :
    SourceInvariant book program source state.sourceSteps state :=
  ⟨0, source, .refl source, represented, by simp⟩

theorem SourceInvariant.run {book : Book} {limits : Limits} {library : Library}
    {origin : Term} {initialCount : Nat} {state : State} (ticks : Nat)
    (invariant : SourceInvariant book library.program origin initialCount state)
    (coverage : Covered book limits library ticks state) :
    SourceInvariant book library.program origin initialCount (run limits library ticks state) := by
  obtain ⟨prefixCount, residual, prefixTrace, represented, prefixCounter⟩ := invariant
  obtain ⟨count, result, trace, exact, counter⟩ := covered_run ticks state residual represented coverage
  refine ⟨prefixCount + count, result, BendExecutionTrace.append prefixTrace trace, exact, ?_⟩
  omega

/-- Completion extraction works after any number of saved/resumed covered
segments because the invariant retains the original source and initial count. -/
theorem SourceInvariant.complete {book : Book} {program : Program}
    {origin : Term} {initialCount : Nat} {state : State} (pointer : Nat)
    (invariant : SourceInvariant book program origin initialCount state)
    (done : state.control = .complete pointer) :
    ∃ count result, BendLiveMachine.Trace book count origin result ∧
      Denotes program state.heap pointer result ∧ Value book result ∧
      state.sourceSteps = initialCount + count := by
  obtain ⟨count, result, trace, represented, counter⟩ := invariant
  obtain ⟨exact, value⟩ := represented.complete done
  exact ⟨count, result, trace, exact, value, counter⟩

#assert_axioms SourceInvariant.complete
/-- The source admissibility premises are real upstream Book/Term judgments.
They are preserved through the actual covered machine run via its derived
Trace, rather than inferred from CodeDenotes or from diagnostic success. -/
theorem covered_run_admissible {book : Book} {limits : Limits} {library : Library}
    (ticks : Nat) (state : State) (source type : Term)
    (represented : StateDenotes book library.program state source)
    (coverage : Covered book limits library ticks state)
    (wellTyped : Book.WellTyped book) (closedBook : Book.Closed book)
    (liveBook : Book.Live book) (typed : Typed book [] source type)
    (closed : Term.Closed source) (live : Term.Live book source) :
    ∃ count result, BendLiveMachine.Trace book count source result ∧
      StateDenotes book library.program (run limits library ticks state) result ∧
      Typed book [] result type ∧ Term.Closed result ∧ Term.Live book result ∧
      (run limits library ticks state).sourceSteps = state.sourceSteps + count := by
  obtain ⟨count, result, trace, exact, counter⟩ := covered_run ticks state source represented coverage
  obtain ⟨closedResult, liveResult⟩ := BendExecutionTrace.closed_live liveBook closed live trace
  exact ⟨count, result, trace, exact, BendExecutionTrace.typed wellTyped closedBook typed trace,
    closedResult, liveResult, counter⟩

#assert_axioms covered_run_admissible
#assert_axioms SourceInvariant.initial
#assert_axioms SourceInvariant.run
#assert_axioms Covered.complete
#assert_axioms covered_add
#assert_axioms Handled.refines
#assert_axioms covered_run
#assert_axioms covered_run_complete
end Minidregg.Theory.BendClosureSimulation
