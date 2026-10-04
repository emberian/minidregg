/- Finite completion for the Core4 lazy demand machine.

From ONLY a closed source (`Scoped 0`) and an independent reference
evaluation (`Evaluates`), the actual unbounded raw machine reaches `complete`
in finitely many `stepRaw` transitions, with the source's ground observation.
The proof is a lexicographic descent on (whole residual source cost,
stutter rank): every raw transition either performs a genuine reference
reduction of the WHOLE residual program (strict cost descent), or preserves
it up to `Steps` while strictly decreasing `stutterRank`, a syntactic potential
of the machine state that needs no termination premise. Sharing is handled by
the permanent address meanings of `GraphRepresentsBy`; Fix by its tied origin.

Lemmas marked "(leaf intake)" are copied verbatim from the unlanded lane source
/tank/dregg-build/codex-objective-demand-bool-20261003/src/Theory/
ObjectiveBendDemandAdequacy.lean (sha256 489b1527…ed1fcd, hbox leaf78 log). -/
import Theory.ObjectiveBendDemandAdequacy
namespace Minidregg.Theory.ObjectiveBendDemandCompleteness
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandInvariant
open Minidregg.Theory.ObjectiveBendDemandAdequacy
set_option autoImplicit false

/-! ## Leaf intake: name congruence, contextual source steps, three executions -/

 theorem stackMeaning_names_congr {bound : Nat} {meaning next : AddressMeaning} {frames : List Frame} {focus : Term}
    (valid : ∀ frame ∈ frames, FrameValid bound frame)
    (same : ∀ address, address < bound → meaning address = next address) :
    stackMeaning meaning frames focus = stackMeaning next frames focus := by
  induction frames generalizing focus with
  | nil => rfl
  | cons frame rest ih =>
      have frameEq := frameMeaning_congr (valid frame (List.mem_cons_self ..)) same (hole := focus)
      have restValid : ∀ frame ∈ rest, FrameValid bound frame := fun frame member => valid frame (List.mem_cons_of_mem _ member)
      simp only [stackMeaning,List.foldl_cons]
      rw [←frameEq]
      exact ih restValid

 theorem sourceStep_frame (meaning : AddressMeaning) (frame : Frame) {before after : Term} (step : Step before after) :
    Step (frameMeaning meaning frame before) (frameMeaning meaning frame after) := by
  cases frame with
  | argument term environment => exact .application _ step
  | update _ => exact step
  | field name => exact .target _ step
  | reflect => exact .reflectStep step
  | metadata => exact .metadataStep step
  | project => exact .projectStep step
  | extend fields environment => exact .extendTarget _ step
  | condition zero successorBody environment => exact .condition _ _ step
  | binaryLeft primitive right environment => exact .binaryLeft _ _ step
  | binaryRight primitive left => exact .binaryRight _ _ (valueMeaning_value _ _) step
  | case arms environment => exact .caseTarget _ step
  | ifBool whenTrue whenFalse environment => exact .ifCondition _ _ step

 theorem sourceStep_stack (meaning : AddressMeaning) (frames : List Frame) {before after : Term} (step : Step before after) :
    Step (stackMeaning meaning frames before) (stackMeaning meaning frames after) := by
  induction frames generalizing before after with
  | nil => exact step
  | cons frame rest ih => exact ih (sourceStep_frame meaning frame step)

 theorem controlMeaning_names_congr {meaning next : AddressMeaning} {state : State}
    (lexical : LexicalInvariant state) (same : ∀ address, address < state.heap.size → meaning address = next address) :
    controlMeaning meaning state.control = controlMeaning next state.control := by
  cases control : state.control with
  | evaluate term environment =>
      have valid : ClosureValid state.heap.size ⟨term,environment⟩ := by simpa [control,ControlValid] using lexical.2.1
      simp only [control,controlMeaning,closeTerm_meaning_congr valid.2 valid.1 same]
  | returned value | complete value =>
      have valid : RuntimeValueValid state.heap.size value := by simpa [control,ControlValid] using lexical.2.1
      simp only [control,controlMeaning,valueMeaning_congr valid same]
  | refused reason | blackhole address => simp [control,controlMeaning]
  | enter address =>
      have allocated : address < state.heap.size := by simpa [control,ControlValid] using lexical.2.1
      simp [control,controlMeaning,same address allocated]

 theorem graphBy_names_congr {meaning next : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source)
    (same : ∀ address, address < state.heap.size → meaning address = next address) :
    GraphRepresentsBy next state source := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  refine ⟨lexical,busy,final,?_,heapRealizes_congr lexical.1 same heap,focus,?_,stackRealizes_congr lexical.2.2 same stack⟩
  · intro address allocated; rw [←same address allocated]; exact names address allocated
  · rw [←controlMeaning_names_congr lexical same]; exact control

 theorem budgetFocus_result_exists (meaning : AddressMeaning) {state : State}
    (successful : ResultControl state.control) : ∃ focus, budgetFocus meaning state = some focus := by
  cases control : state.control with
  | evaluate term environment | returned value | complete value => simp [budgetFocus,control,controlMeaning]
  | enter address =>
      cases found : state.heap[address]? with
      | none => simp [budgetFocus,control,found]
      | some cell => cases cell <;> simp [budgetFocus,control,found]
  | refused reason | blackhole address => simp [ResultControl,control] at successful

 theorem rawRun_add (first second : Nat) (state : State) : rawRun (first+second) state = rawRun second (rawRun first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add,rawRun]
  | succ first ih => simpa only [Nat.succ_add,rawRun] using ih (stepRaw state)

 theorem graph_primitive_return_execution {meaning : AddressMeaning} {state : State} {source result : Term} {primitive : Primitive}
    {left right next : RuntimeValue} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned right)
    (head : state.stack = .binaryRight primitive left::rest)
    (dispatch : (valueTerm left).bind (fun l => (valueTerm right).bind (primitiveResult primitive l)) = some result)
    (scalar : scalarValue result = some next) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  obtain ⟨leftTerm,leftFound,rightResult⟩ := Option.bind_eq_some_iff.mp dispatch
  obtain ⟨rightTerm,rightFound,primitiveFound⟩ := Option.bind_eq_some_iff.mp rightResult
  have reduce : Step (.binary primitive (valueMeaning meaning left) (valueMeaning meaning right)) (valueMeaning meaning next) := by
    have rule := Step.primitive primitive _ _ result (valueMeaning_value meaning left) (valueMeaning_value meaning right)
      (by simpa only [valueTerm_meaning leftFound meaning,valueTerm_meaning rightFound meaning] using primitiveFound)
    simpa only [scalarValue_meaning scalar meaning] using rule
  have before : StackRealizes meaning source (.binary primitive (valueMeaning meaning left) (valueMeaning meaning right)) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next reduce (Steps.refl _))
  refine ⟨meaning,(fun _ _ => rfl),?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,valueMeaning meaning next,?_,?_⟩
    · simpa [stepRaw,returned,head,dispatch,scalar] using names
    · simpa [stepRaw,returned,head,dispatch,scalar] using heap
    · simp [stepRaw,returned,head,dispatch,scalar,controlMeaning]
    · simpa [stepRaw,returned,head,dispatch,scalar] using advanced
  · refine ⟨[.binaryRight primitive left],valueMeaning meaning right,valueMeaning meaning next,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned]
    · simp [stepRaw,returned,head,dispatch,scalar,controlMeaning]
    · simp [stepRaw,returned,head,dispatch,scalar,controlMeaning]
    · exact reduce

 theorem graph_extend_record_execution {meaning : AddressMeaning} {state : State} {source : Term} {inherited : List (String × Address)}
    {fields : List (String × Term)} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (returned : state.control = .returned (.record inherited))
    (head : state.stack = .extend fields environment::rest) : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ SourceDispatch meaning next state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have validFrame : FrameValid state.heap.size (.extend fields environment) :=
    lexical.2.2 _ (head ▸ List.mem_cons_self ..)
  have validInherited : RuntimeValueValid state.heap.size (.record inherited) := by
    simpa only [returned,ControlValid] using lexical.2.1
  have restValid : ∀ frame ∈ rest, FrameValid state.heap.size frame := by
    intro frame member
    apply lexical.2.2 frame
    rw [head]
    exact List.mem_cons_of_mem _ member
  obtain ⟨extended,newNames,newHeap,same,fieldsEq⟩ :=
    allocateFields_realizes lexical.1 names heap validFrame.1 validFrame.2
  let retained := inherited.filter (fun prior => !(fields.any fun field => field.1 == prior.1))
  let newValue := RuntimeValue.record ((allocateFields state.heap environment fields).2++retained)
  have inheritedEq : inherited.map (fun field => (field.1,extended field.2)) =
      inherited.map (fun field => (field.1,meaning field.2)) := by
    apply List.map_congr_left
    intro field member
    exact Prod.ext rfl (same _ (validInherited field member)).symm
  have denotes : valueMeaning extended newValue =
      .record (extendFields (inherited.map fun field => (field.1,meaning field.2))
        (fields.map fun field => (field.1,closeTerm meaning environment field.2))) := by
    simp only [newValue,valueMeaning,List.map_append,fieldsEq,extendFields]
    congr 2
    have filtered := List.filter_map (f := fun field : String × Address => (field.1,extended field.2))
      (p := fun prior => !((fields.map fun field => (field.1,closeTerm meaning environment field.2)).any fun field => field.1 == prior.1))
      (l := inherited)
    simpa [retained,List.any_map,Function.comp_def,inheritedEq] using filtered.symm
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source
      (.extend (valueMeaning meaning (.record inherited))
        (fields.map fun field => (field.1,closeTerm meaning environment field.2))) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have consumers := stackRealizes_congr restValid same before
  have reduce : Step
      (.extend (valueMeaning meaning (.record inherited))
        (fields.map fun field => (field.1,closeTerm meaning environment field.2))) (valueMeaning extended newValue) := by
    rw [denotes]
    exact Step.extendRecord _ _
  have advanced := stackRealizes_steps consumers (Steps.next reduce (Steps.refl _))
  refine ⟨extended,same,?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,valueMeaning extended newValue,?_,?_⟩
    · simpa [stepRaw,returned,head] using newNames
    · simpa [stepRaw,returned,head] using newHeap
    · simp [stepRaw,returned,head,controlMeaning,newValue,retained]
    · simpa [stepRaw,returned,head] using advanced
  · refine ⟨[.extend fields environment],valueMeaning meaning (.record inherited),valueMeaning extended newValue,?_,?_,?_,?_⟩
    · simp [controlMeaning,returned]
    · simp [stepRaw,returned,head,controlMeaning,newValue,retained]
    · simp [stepRaw,returned,head,controlMeaning,newValue,retained]
    · exact reduce

 theorem graph_evaluate_fix_execution {meaning : AddressMeaning} {state : State} {source spec inherited : Term} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.fix spec inherited) environment) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ (GraphRepresentsBy next (stepRaw state) source ∧ Step (closeTerm meaning environment (.fix spec inherited))
      (closeOrigin next ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),state.heap.size::environment⟩)) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.fix spec inherited,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length spec ∧ Scoped environment.length inherited := by
    simpa using valid.1
  let fixSource := closeTerm meaning environment (.fix spec inherited)
  let extended := extendMeaning meaning state.heap.size fixSource
  have same : ∀ address, address < state.heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended state.heap.size = fixSource := by simp [extended,extendMeaning]
  have closed : Scoped 0 fixSource := closeTerm_scoped names valid.2 valid.1
  have newNames : MeaningsScoped (state.heap.size+1) extended := by
    intro address allocated
    by_cases eq : address = state.heap.size
    · subst address; simpa only [fresh] using closed
    · have old : address < state.heap.size := by omega
      simpa only [←same address old] using names address old
  have newHeap := heapRealizes_congr lexical.1 same heap
  let body := Term.app (Term.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ)
  have originEq : closeTerm extended (state.heap.size::environment) body =
      .app (.app (closeTerm meaning environment spec) fixSource) (closeTerm meaning environment inherited) := by
    simp only [body,closeTerm_app,closeTerm_weaken valid.2 scopes.1 same,
      closeTerm_weaken valid.2 scopes.2 same]
    simp [closeTerm,Term.substitute,environmentSubstitution,fresh]
  have newCell : CellRealizes extended state.heap.size (.suspended ⟨body,state.heap.size::environment⟩) := by
    refine ⟨?_,True.intro⟩
    simp only [cellOrigin,closeOrigin,fresh,originEq]
    simpa only [fixSource,closeTerm_fix] using
      Steps.next (Step.fix (closeTerm meaning environment spec) (closeTerm meaning environment inherited)) (Steps.refl _)
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  refine ⟨extended,same,?_,?_⟩
  ·
    refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
      stepRaw_finalStackInvariant final,?_,?_,fixSource,?_,?_⟩
    · simpa [stepRaw,evaluate] using newNames
    · simpa [stepRaw,evaluate,body] using heapRealizes_push newHeap newCell
    · simp [stepRaw,evaluate,controlMeaning,fresh]
    · simpa [stepRaw,evaluate,fixSource] using consumers
  · change Step fixSource (closeTerm extended (state.heap.size::environment) body)
    rw [originEq]
    simpa only [fixSource,closeTerm_fix] using Step.fix
      (closeTerm meaning environment spec) (closeTerm meaning environment inherited)

/-! ## The whole residual program and the stutter potential -/

/-- The whole residual source program at a state: the phase-sensitive demand
focus closed under the actual continuation (update frames are transparent). -/
def budgetWhole (meaning : AddressMeaning) (state : State) : Option Term :=
  (budgetFocus meaning state).map (stackMeaning meaning state.stack)

noncomputable def cellPotential : Cell → Nat
  | .suspended origin => 3 * sizeOf origin.term + 1
  | .evaluating _ | .cached _ _ => 0

noncomputable def controlPotential : Control → Nat
  | .evaluate term _ => 3 * sizeOf term + 1
  | .enter _ => 2
  | .returned _ => 1
  | .complete _ | .refused _ | .blackhole _ => 0

noncomputable def framePotential : Frame → Nat
  | .argument term _ => 3 * sizeOf term
  | .binaryLeft _ right _ => 3 * sizeOf right + 2
  | .condition zero body _ => 3 * (sizeOf zero + sizeOf body)
  | .extend fields _ => 3 * sizeOf fields
  | .case arms _ => 3 * sizeOf arms
  | .ifBool whenTrue whenFalse _ => 3 * (sizeOf whenTrue + sizeOf whenFalse)
  | .update _ | .field _ | .reflect | .metadata | .project | .binaryRight _ _ => 0

noncomputable def heapPotential (heap : Array Cell) : Nat := (heap.toList.map cellPotential).sum

/-- Raw syntax still to be traversed (suspended thunks, the control term,
pending operands) plus continuation depth. Every non-semantic raw transition
strictly decreases it, for every state, terminating or not. -/
noncomputable def stutterRank (state : State) : Nat :=
  2 * (heapPotential state.heap + controlPotential state.control +
    (state.stack.map framePotential).sum) + state.stack.length

 theorem heapPotential_push (heap : Array Cell) (cell : Cell) :
    heapPotential (heap.push cell) = heapPotential heap + cellPotential cell := by
  simp [heapPotential,Array.toList_push]

 theorem cellPotential_list_set {cells : List Cell} {index : Nat} {old new : Cell}
    (found : cells[index]? = some old) :
    ((cells.set index new).map cellPotential).sum + cellPotential old =
      (cells.map cellPotential).sum + cellPotential new := by
  induction cells generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst found
          simp only [List.set_cons_zero,List.map_cons,List.sum_cons]
          omega
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          have step := ih found
          simp only [List.set_cons_succ,List.map_cons,List.sum_cons]
          omega

 theorem heapPotential_set {heap : Array Cell} {address : Nat} {old new : Cell}
    (found : heap[address]? = some old) :
    heapPotential (heap.set! address new) + cellPotential old = heapPotential heap + cellPotential new := by
  have listFound : heap.toList[address]? = some old := by simpa using found
  simp only [heapPotential,Array.set!,Array.toList_setIfInBounds]
  exact cellPotential_list_set listFound

 theorem heapPotential_allocateFields (heap : Array Cell) (environment : Environment)
    (fields : List (String × Term)) :
    heapPotential (allocateFields heap environment fields).1 =
      heapPotential heap + (fields.map fun field => 3 * sizeOf field.2 + 1).sum := by
  induction fields generalizing heap with
  | nil => simp [allocateFields]
  | cons field fields ih =>
      rw [allocateFields_cons,ih,heapPotential_push]
      simp [cellPotential]
      omega

 theorem fields_potential_lt (fields : List (String × Term)) :
    (fields.map fun field => 3 * sizeOf field.2 + 1).sum + 1 ≤ 3 * sizeOf fields := by
  induction fields with
  | nil => simp
  | cons field fields ih =>
      obtain ⟨key,term⟩ := field
      simp
      omega

/-- One raw transition advances the whole residual program: either a genuine
reference reduction (then possibly a demand-focus unfolding), or a `Steps`
(often identity) together with a strict stutter-rank descent. -/
def WholeAdvance (meaning next : AddressMeaning) (state successor : State) : Prop :=
  ∃ before after, budgetWhole meaning state = some before ∧ budgetWhole next successor = some after ∧
    ((∃ middle, Step before middle ∧ Steps middle after) ∨
      (Steps before after ∧ stutterRank successor < stutterRank state))

 theorem budgetFocus_of_controlMeaning {meaning : AddressMeaning} {state : State} {focus : Term}
    (noEnter : ∀ address, state.control ≠ .enter address)
    (current : controlMeaning meaning state.control = some focus) : budgetFocus meaning state = some focus := by
  cases control : state.control with
  | enter address => exact False.elim (noEnter address control)
  | evaluate _ _ | returned _ | complete _ | refused _ | blackhole _ =>
      simpa [budgetFocus,control] using current

 theorem graphBy_same_size {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source)
    (successful : ResultControl (stepRaw state).control)
    (size : (stepRaw state).heap.size = state.heap.size) : GraphRepresentsBy meaning (stepRaw state) source := by
  obtain ⟨next,same,current⟩ := graph_stepRaw_names represented successful
  apply graphBy_names_congr current
  intro address allocated
  rw [size] at allocated
  exact (same address allocated).symm

/-- Every SourceDispatch transition is a genuine whole-program reduction. -/
 theorem dispatch_advance {meaning next : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source) (same : SourceNamesAgree state meaning next)
    (current : GraphRepresentsBy next (stepRaw state) source)
    (noEnter : ∀ address, state.control ≠ .enter address)
    (dispatch : SourceDispatch meaning next state) : WholeAdvance meaning next state (stepRaw state) := by
  obtain ⟨consumed,before,after,control,newControl,head,reduce⟩ := dispatch
  have valid : ∀ frame ∈ (stepRaw state).stack, FrameValid state.heap.size frame := by
    intro frame member
    apply represented.1.2.2 frame
    rw [head]
    exact List.mem_append_right _ member
  have previous : stackMeaning meaning state.stack before =
      stackMeaning next (stepRaw state).stack (stackMeaning meaning consumed before) := by
    rw [head]
    simp only [stackMeaning,List.foldl_append]
    exact stackMeaning_names_congr valid same
  have successful : ResultControl (stepRaw state).control := by
    cases c : (stepRaw state).control <;> simp_all [controlMeaning,ResultControl]
  obtain ⟨focus,nextFocus⟩ := budgetFocus_result_exists next successful
  have focused := budgetFocus_control_steps current.2.2.2.2.1 newControl nextFocus
  refine ⟨stackMeaning meaning state.stack before,stackMeaning next (stepRaw state).stack focus,?_,?_,
    Or.inl ⟨_,?_,sourceSteps_stack next _ focused⟩⟩
  · simp [budgetWhole,budgetFocus_of_controlMeaning noEnter control]
  · simp [budgetWhole,nextFocus]
  · rw [previous]; exact sourceStep_stack next (stepRaw state).stack reduce

/-! ## Per-transition whole-program advance -/

 theorem closeTerm_nat (meaning : AddressMeaning) (environment : Environment) (n : Nat) :
    closeTerm meaning environment (.nat n) = .nat n := by
  cases environment <;> simp [closeTerm,Term.substitute]

 theorem closeTerm_boolean (meaning : AddressMeaning) (environment : Environment) (b : Bool) :
    closeTerm meaning environment (.boolean b) = .boolean b := by
  cases environment <;> simp [closeTerm,Term.substitute]

 theorem closeTerm_label (meaning : AddressMeaning) (environment : Environment) (s : String) :
    closeTerm meaning environment (.label s) = .label s := by
  cases environment <;> simp [closeTerm,Term.substitute]

/-- A stutter with an unchanged meaning and an identical whole program. -/
 theorem stutter_advance {meaning : AddressMeaning} {state : State} {whole : Term}
    (old : budgetWhole meaning state = some whole) (new : budgetWhole meaning (stepRaw state) = some whole)
    (rank : stutterRank (stepRaw state) < stutterRank state) :
    WholeAdvance meaning meaning state (stepRaw state) :=
  ⟨whole,whole,old,new,Or.inr ⟨.refl _,rank⟩⟩

 theorem bound_advance {meaning : AddressMeaning} {state : State} {source : Term}
    {environment : Environment} {index address : Nat}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (control : state.control = .evaluate (.bound index) environment) (found : environment[index]? = some address) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  have current := graphBy_same_size represented successful (by simp [stepRaw,control,found])
  refine ⟨meaning,current,?_⟩
  have closes : closeTerm meaning environment (.bound index) = meaning address := by
    cases environment with
    | nil => simp at found
    | cons _ _ => simp [closeTerm,Term.substitute,environmentSubstitution,found]
  have nextEnter : (stepRaw state).control = .enter address := by simp [stepRaw,control,found]
  obtain ⟨focus,nextFocus⟩ := budgetFocus_result_exists meaning successful
  have steps := budgetFocus_enter_steps current.2.2.2.2.1 nextEnter nextFocus
  have stack : (stepRaw state).stack = state.stack := by simp [stepRaw,control,found]
  refine ⟨stackMeaning meaning state.stack (meaning address),stackMeaning meaning (stepRaw state).stack focus,
    by simp [budgetWhole,budgetFocus,control,controlMeaning,closes],by simp [budgetWhole,nextFocus],Or.inr ⟨?_,?_⟩⟩
  · rw [stack]; exact sourceSteps_stack meaning state.stack steps
  · simp [stutterRank,stepRaw,control,found,controlPotential]
    omega

 theorem immediate_advance {meaning : AddressMeaning} {state : State} {source : Term}
    {immediate : ImmediateValue} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (control : state.control = .evaluate immediate.term environment) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  have current := graphBy_same_size represented successful (by cases immediate <;> simp [stepRaw,control,ImmediateValue.term])
  refine ⟨meaning,current,stutter_advance (whole := stackMeaning meaning state.stack (closeTerm meaning environment immediate.term))
    (by simp [budgetWhole,budgetFocus,control,controlMeaning]) ?_ ?_⟩
  · cases immediate <;>
      simp [budgetWhole,budgetFocus,stepRaw,control,controlMeaning,valueMeaning,ImmediateValue.term,
        closeTerm_nat,closeTerm_boolean,closeTerm_label]
  · cases immediate <;> simp [stutterRank,stepRaw,control,controlPotential,ImmediateValue.term] <;> omega

 theorem context_advance {meaning : AddressMeaning} {state : State} {source hole : Term}
    {context : DemandContext} {environment : Environment}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (control : state.control = .evaluate (context.term hole) environment) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  have dispatched := demandContext_dispatch control
  have current := graphBy_same_size represented successful (by rw [dispatched])
  have scope : Scoped environment.length (context.term hole) := by
    have valid := represented.1.2.1
    rw [control] at valid
    exact valid.1
  refine ⟨meaning,current,stutter_advance (whole := stackMeaning meaning state.stack (closeTerm meaning environment (context.term hole)))
    (by simp [budgetWhole,budgetFocus,control,controlMeaning]) ?_ ?_⟩
  · rw [dispatched,demandContext_closes context meaning environment hole scope]
    simp [budgetWhole,budgetFocus,controlMeaning,stackMeaning]
  · rw [dispatched]
    cases context <;>
      simp [stutterRank,control,controlPotential,framePotential,DemandContext.term,DemandContext.frame] <;> omega

 theorem pair_advance {meaning : AddressMeaning} {state : State} {source first second : Term}
    {environment : Environment} {kind : PairObject} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (kind.term first second) environment) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨kind.term first second,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length first ∧ Scoped environment.length second := by
    cases kind <;> simpa [PairObject.term] using valid.1
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes lexical.1 names heap scopes.1 valid.2
  have oneValid := heapValid_push lexical.1
    (show CellValid (state.heap.size+1) (.suspended ⟨first,environment⟩) from
      ⟨scopes.1,environmentValid_mono valid.2 (Nat.le_succ _)⟩)
  have capturesOne : EnvironmentValid (state.heap.push (.suspended ⟨first,environment⟩)).size environment :=
    environmentValid_mono valid.2 (by simp)
  obtain ⟨two,twoNames,twoHeap,twoSame,twoFresh⟩ :=
    allocateClosure_realizes oneValid oneNames oneHeap scopes.2 capturesOne
  have same : ∀ address, address < state.heap.size → meaning address = two address := by
    intro address allocated
    exact (oneSame address allocated).trans (twoSame address (by simpa using Nat.lt_succ_of_lt allocated))
  have firstEq : two state.heap.size = closeTerm meaning environment first := by
    rw [←twoSame state.heap.size (by simp),oneFresh]
  have secondEq : two (state.heap.size+1) = closeTerm meaning environment second := by
    have closeEq := closeTerm_meaning_congr valid.2 scopes.2 oneSame
    simpa only [Array.size_push,←closeEq] using twoFresh
  have sourceEq : valueMeaning two (kind.value state.heap.size (state.heap.size+1)) =
      closeTerm meaning environment (kind.term first second) := by
    cases kind <;> cases environment <;> simp [PairObject.term,PairObject.value,valueMeaning,firstEq,secondEq,closeTerm,Term.substitute]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  have stackEq := stackMeaning_names_congr lexical.2.2 same (focus := closeTerm meaning environment (kind.term first second))
  refine ⟨two,⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,
    valueMeaning two (kind.value state.heap.size (state.heap.size+1)),?_,?_⟩,
    stackMeaning meaning state.stack (closeTerm meaning environment (kind.term first second)),
    stackMeaning meaning state.stack (closeTerm meaning environment (kind.term first second)),?_,?_,Or.inr ⟨.refl _,?_⟩⟩
  · cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using twoNames
  · cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using twoHeap
  · cases kind <;> simp [stepRaw,evaluate,PairObject.term,PairObject.value,controlMeaning]
  · rw [sourceEq]
    cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using consumers
  · simp [budgetWhole,budgetFocus,evaluate,controlMeaning]
  · have nextValue : budgetFocus two (stepRaw state) =
        some (valueMeaning two (kind.value state.heap.size (state.heap.size+1))) := by
      cases kind <;> simp [budgetFocus,stepRaw,evaluate,PairObject.term,PairObject.value,controlMeaning]
    have nextStack : (stepRaw state).stack = state.stack := by
      cases kind <;> simp [stepRaw,evaluate,PairObject.term]
    simp only [budgetWhole,nextValue,nextStack,Option.map_some,sourceEq,stackEq]
  · cases kind <;>
      simp [stutterRank,stepRaw,evaluate,PairObject.term,heapPotential_push,cellPotential,controlPotential] <;> omega

 theorem inject_advance {meaning : AddressMeaning} {state : State} {source payload : Term}
    {tag : String} {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.inject tag payload) environment) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.inject tag payload,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scope : Scoped environment.length payload := by simpa using valid.1
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes lexical.1 names heap scope valid.2
  have sourceEq : valueMeaning one (.variant tag state.heap.size) =
      closeTerm meaning environment (.inject tag payload) := by
    simp [valueMeaning,oneFresh,closeTerm_inject]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 oneSame stack
  have stackEq := stackMeaning_names_congr lexical.2.2 oneSame (focus := closeTerm meaning environment (.inject tag payload))
  refine ⟨one,⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,valueMeaning one (.variant tag state.heap.size),?_,?_⟩,
    stackMeaning meaning state.stack (closeTerm meaning environment (.inject tag payload)),
    stackMeaning meaning state.stack (closeTerm meaning environment (.inject tag payload)),?_,?_,Or.inr ⟨.refl _,?_⟩⟩
  · simpa [stepRaw,evaluate] using oneNames
  · simpa [stepRaw,evaluate] using oneHeap
  · simp [stepRaw,evaluate,controlMeaning]
  · rw [sourceEq]
    simpa [stepRaw,evaluate] using consumers
  · simp [budgetWhole,budgetFocus,evaluate,controlMeaning]
  · have nextValue : budgetFocus one (stepRaw state) = some (valueMeaning one (.variant tag state.heap.size)) := by
      simp [budgetFocus,stepRaw,evaluate,controlMeaning]
    have nextStack : (stepRaw state).stack = state.stack := by simp [stepRaw,evaluate]
    simp only [budgetWhole,nextValue,nextStack,Option.map_some,sourceEq,stackEq]
  · simp [stutterRank,stepRaw,evaluate,heapPotential_push,cellPotential,controlPotential]
    omega

 theorem record_advance {meaning : AddressMeaning} {state : State} {source : Term}
    {fields : List (String × Term)} {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.record fields) environment) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  obtain ⟨lexical,busy,final,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.record fields,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : ∀ field ∈ fields, Scoped environment.length field.2 := by simpa using valid.1
  obtain ⟨extended,newNames,newHeap,same,fieldsEq⟩ := allocateFields_realizes lexical.1 names heap valid.2 scopes
  have denotes : valueMeaning extended (.record (allocateFields state.heap environment fields).2) =
      closeTerm meaning environment (.record fields) := by simp only [valueMeaning,fieldsEq,closeTerm_record]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  have stackEq := stackMeaning_names_congr lexical.2.2 same (focus := closeTerm meaning environment (.record fields))
  refine ⟨extended,⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,?_,?_,
    valueMeaning extended (.record (allocateFields state.heap environment fields).2),?_,?_⟩,
    stackMeaning meaning state.stack (closeTerm meaning environment (.record fields)),
    stackMeaning meaning state.stack (closeTerm meaning environment (.record fields)),?_,?_,Or.inr ⟨.refl _,?_⟩⟩
  · simpa [stepRaw,evaluate] using newNames
  · simpa [stepRaw,evaluate] using newHeap
  · simp [stepRaw,evaluate,controlMeaning]
  · rw [denotes]
    simpa [stepRaw,evaluate] using consumers
  · simp [budgetWhole,budgetFocus,evaluate,controlMeaning]
  · have nextValue : budgetFocus extended (stepRaw state) =
        some (valueMeaning extended (.record (allocateFields state.heap environment fields).2)) := by
      simp [budgetFocus,stepRaw,evaluate,controlMeaning]
    have nextStack : (stepRaw state).stack = state.stack := by simp [stepRaw,evaluate]
    simp only [budgetWhole,nextValue,nextStack,Option.map_some,denotes,stackEq]
  · have bound := fields_potential_lt fields
    simp [stutterRank,stepRaw,evaluate,heapPotential_allocateFields,controlPotential]
    omega

 theorem fix_advance {meaning : AddressMeaning} {state : State} {source spec inherited : Term}
    {environment : Environment} (represented : GraphRepresentsBy meaning state source)
    (evaluate : state.control = .evaluate (.fix spec inherited) environment) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  obtain ⟨next,same,current,reduce⟩ := graph_evaluate_fix_execution represented evaluate
  let origin : Closure := ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),state.heap.size::environment⟩
  have focus : budgetFocus next (stepRaw state) = some (closeOrigin next origin) := by
    simp [budgetFocus,stepRaw,evaluate,origin]
  have stackSame : (stepRaw state).stack = state.stack := by simp [stepRaw,evaluate]
  have stackEq := stackMeaning_names_congr represented.1.2.2 same (focus := closeTerm meaning environment (.fix spec inherited))
  refine ⟨next,current,stackMeaning meaning state.stack (closeTerm meaning environment (.fix spec inherited)),
    stackMeaning next state.stack (closeOrigin next origin),?_,?_,Or.inl ⟨_,?_,.refl _⟩⟩
  · simp [budgetWhole,budgetFocus,evaluate,controlMeaning]
  · simp only [budgetWhole,focus,stackSame,Option.map_some]
  · rw [stackEq]; exact sourceStep_stack next state.stack reduce

 theorem enter_suspended_advance {meaning : AddressMeaning} {state : State} {source : Term}
    {address : Address} {origin : Closure}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (control : state.control = .enter address) (found : state.heap[address]? = some (.suspended origin)) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  have current := graphBy_same_size represented successful (by simp [stepRaw,control,found])
  have potential := heapPotential_set found (new := .evaluating origin)
  refine ⟨meaning,current,stutter_advance (whole := stackMeaning meaning state.stack (closeOrigin meaning origin))
    (by simp [budgetWhole,budgetFocus,control,found]) ?_ ?_⟩
  · simp [budgetWhole,budgetFocus,stepRaw,control,found,controlMeaning,stackMeaning,frameMeaning,closeOrigin]
  · simp [cellPotential] at potential
    simp [stutterRank,stepRaw,control,found,controlPotential,framePotential,cellPotential]
    omega

 theorem enter_cached_advance {meaning : AddressMeaning} {state : State} {source : Term}
    {address : Address} {origin : Closure} {value : RuntimeValue}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (control : state.control = .enter address) (found : state.heap[address]? = some (.cached origin value)) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  have current := graphBy_same_size represented successful (by simp [stepRaw,control,found])
  refine ⟨meaning,current,stutter_advance (whole := stackMeaning meaning state.stack (valueMeaning meaning value))
    (by simp [budgetWhole,budgetFocus,control,found]) ?_ ?_⟩
  · simp [budgetWhole,budgetFocus,stepRaw,control,found,controlMeaning]
  · simp [stutterRank,stepRaw,control,found,controlPotential]

 theorem complete_return_advance {meaning : AddressMeaning} {state : State} {source : Term} {value : RuntimeValue}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (control : state.control = .returned value) (frames : state.stack = []) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  have current := graphBy_same_size represented successful (by simp [stepRaw,control,frames])
  refine ⟨meaning,current,stutter_advance (whole := valueMeaning meaning value)
    (by simp [budgetWhole,budgetFocus,control,controlMeaning,frames,stackMeaning]) ?_ ?_⟩
  · simp [budgetWhole,budgetFocus,stepRaw,control,frames,controlMeaning,stackMeaning]
  · simp [stutterRank,stepRaw,control,frames,controlPotential]

 theorem update_return_advance {meaning : AddressMeaning} {state : State} {source : Term} {value : RuntimeValue}
    {address : Address} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (control : state.control = .returned value) (frames : state.stack = .update address::rest) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  obtain ⟨origin,found⟩ := busy_update_exists represented.2.1 frames
  have current := graphBy_same_size represented successful (by simp [stepRaw,control,frames,found])
  have potential := heapPotential_set found (new := .cached origin value)
  refine ⟨meaning,current,stutter_advance (whole := stackMeaning meaning rest (valueMeaning meaning value))
    (by simp [budgetWhole,budgetFocus,control,controlMeaning,frames,stackMeaning,frameMeaning]) ?_ ?_⟩
  · simp [budgetWhole,budgetFocus,stepRaw,control,frames,found,controlMeaning]
  · simp [cellPotential] at potential
    simp [stutterRank,stepRaw,control,frames,found,framePotential,potential]

 theorem binaryLeft_advance {meaning : AddressMeaning} {state : State} {source right : Term} {value : RuntimeValue}
    {primitive : Primitive} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (control : state.control = .returned value) (frames : state.stack = .binaryLeft primitive right environment::rest) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  have current := graphBy_same_size represented successful (by simp [stepRaw,control,frames])
  refine ⟨meaning,current,stutter_advance
    (whole := stackMeaning meaning rest (.binary primitive (valueMeaning meaning value) (closeTerm meaning environment right)))
    (by simp [budgetWhole,budgetFocus,control,controlMeaning,frames,stackMeaning,frameMeaning]) ?_ ?_⟩
  · simp [budgetWhole,budgetFocus,stepRaw,control,frames,controlMeaning,stackMeaning,frameMeaning]
  · simp [stutterRank,stepRaw,control,frames,controlPotential,framePotential]
    omega

 theorem specification_call_advance {meaning : AddressMeaning} {state : State} {source argument : Term}
    {descriptor extension : Address} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresentsBy meaning state source) (successful : ResultControl (stepRaw state).control)
    (control : state.control = .returned (.specification descriptor extension))
    (frames : state.stack = .argument argument environment::rest) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧ WholeAdvance meaning next state (stepRaw state) := by
  have current := graphBy_same_size represented successful (by simp [stepRaw,control,frames])
  have enter : (stepRaw state).control = .enter extension := by simp [stepRaw,control,frames]
  have nextStack : (stepRaw state).stack = state.stack := by simp [stepRaw,control,frames]
  obtain ⟨focus,nextFocus⟩ := budgetFocus_result_exists meaning successful
  have focused := budgetFocus_enter_steps current.2.2.2.2.1 enter nextFocus
  refine ⟨meaning,current,
    stackMeaning meaning rest (.app (.specification (meaning descriptor) (meaning extension)) (closeTerm meaning environment argument)),
    stackMeaning meaning state.stack focus,?_,?_,Or.inl ⟨stackMeaning meaning state.stack (meaning extension),?_,?_⟩⟩
  · simp [budgetWhole,budgetFocus,control,controlMeaning,frames,stackMeaning,frameMeaning,valueMeaning]
  · simp [budgetWhole,nextFocus,nextStack]
  · rw [frames]
    simpa [stackMeaning,frameMeaning] using sourceStep_stack meaning rest (Step.applySpecification (meaning descriptor) (meaning extension) (closeTerm meaning environment argument))
  · exact sourceSteps_stack meaning state.stack focused

/-! ## Every raw transition advances the whole program -/

 theorem graph_stepRaw_whole {meaning : AddressMeaning} {state : State} {source : Term}
    (represented : GraphRepresentsBy meaning state source)
    (successful : ResultControl (stepRaw state).control)
    (running : ∀ value, state.control ≠ .complete value) :
    ∃ next : AddressMeaning, GraphRepresentsBy next (stepRaw state) source ∧
      WholeAdvance meaning next state (stepRaw state) := by
  cases control : state.control with
  | complete value => exact False.elim (running value control)
  | refused reason | blackhole address => simp [stepRaw,control,ResultControl] at successful
  | enter address =>
      cases found : state.heap[address]? with
      | none => simp [stepRaw,control,found,ResultControl] at successful
      | some cell =>
          cases cell with
          | suspended origin => exact enter_suspended_advance represented successful control found
          | cached origin value => exact enter_cached_advance represented successful control found
          | evaluating origin => simp [stepRaw,control,found,ResultControl] at successful
  | evaluate term environment =>
      have noEnter : ∀ address, state.control ≠ .enter address := by intro address; simp [control]
      cases term with
      | bound index =>
          cases found : environment[index]? with
          | none => simp [stepRaw,control,found,ResultControl] at successful
          | some address => exact bound_advance represented successful control found
      | lam body => exact immediate_advance (immediate := .closure body) represented successful control
      | nat number => exact immediate_advance (immediate := .natural number) represented successful control
      | boolean value => exact immediate_advance (immediate := .boolean value) represented successful control
      | label name => exact immediate_advance (immediate := .label name) represented successful control
      | app function argument => exact context_advance (context := .argument argument) represented successful control
      | mix lower upper =>
          obtain ⟨next,same,current,dispatch⟩ := graph_evaluate_mix_execution represented control
          exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
      | fix spec inherited => exact fix_advance represented control
      | specification descriptor extension => exact pair_advance (kind := .specification) represented control
      | prototype spec target => exact pair_advance (kind := .prototype) represented control
      | record fields => exact record_advance represented control
      | reflect term => exact context_advance (context := .reflect) represented successful control
      | metadata term => exact context_advance (context := .metadata) represented successful control
      | project term => exact context_advance (context := .project) represented successful control
      | get target name => exact context_advance (context := .field name) represented successful control
      | extend inherited fields => exact context_advance (context := .extend fields) represented successful control
      | ifZero value zero body => exact context_advance (context := .condition zero body) represented successful control
      | binary primitive left right => exact context_advance (context := .binary primitive right) represented successful control
      | inject tag payload => exact inject_advance represented control
      | case scrutinee arms => exact context_advance (context := .case arms) represented successful control
      | ifBool condition whenTrue whenFalse =>
          exact context_advance (context := .ifBool whenTrue whenFalse) represented successful control
  | returned value =>
      have noEnter : ∀ address, state.control ≠ .enter address := by intro address; simp [control]
      cases frames : state.stack with
      | nil => exact complete_return_advance represented successful control frames
      | cons frame rest =>
          cases frame with
          | update address => exact update_return_advance represented successful control frames
          | argument argument environment =>
              cases value with
              | closure body captured =>
                  obtain ⟨next,same,current,dispatch⟩ := graph_closure_call_execution represented control frames
                  exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
              | specification descriptor extension =>
                  exact specification_call_advance represented successful control frames
              | natural _ | boolean _ | label _ | record _ | prototype _ _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | reflect =>
              cases value with
              | prototype spec target =>
                  obtain ⟨next,same,current,dispatch⟩ := graph_object_access_execution (access := .reflect) represented control frames
                  exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
              | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | metadata =>
              cases value with
              | specification descriptor extension =>
                  obtain ⟨next,same,current,dispatch⟩ := graph_object_access_execution (access := .metadata) represented control frames
                  exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
              | closure _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | project =>
              cases value with
              | prototype spec target =>
                  obtain ⟨next,same,current,dispatch⟩ := graph_object_access_execution (access := .project) represented control frames
                  exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
              | closure _ _ | specification _ _ | natural _ | boolean _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | field name =>
              cases value with
              | record fields =>
                  cases found : fields.find? (fun field => field.1 == name) with
                  | none => simp [stepRaw,control,frames,found,ResultControl] at successful
                  | some field =>
                      obtain ⟨key,address⟩ := field
                      obtain ⟨next,same,current,dispatch⟩ := graph_field_return_execution represented control frames found
                      exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | extend fields environment =>
              cases value with
              | record inherited =>
                  obtain ⟨next,same,current,dispatch⟩ := graph_extend_record_execution represented control frames
                  exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | condition zero body environment =>
              cases value with
              | natural number =>
                  cases number with
                  | zero =>
                      obtain ⟨next,same,current,dispatch⟩ := graph_condition_zero_execution represented control frames
                      exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
                  | succ number =>
                      obtain ⟨next,same,current,dispatch⟩ := graph_condition_successor_execution represented control frames
                      exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
              | closure _ _ | specification _ _ | prototype _ _ | record _ | boolean _ | label _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | binaryLeft primitive right environment => exact binaryLeft_advance represented successful control frames
          | binaryRight primitive left =>
              cases dispatch : (valueTerm left).bind (fun l => (valueTerm value).bind (primitiveResult primitive l)) with
              | none => simp [stepRaw,control,frames,dispatch,ResultControl] at successful
              | some result =>
                  cases scalar : scalarValue result with
                  | none => simp [stepRaw,control,frames,dispatch,scalar,ResultControl] at successful
                  | some next =>
                      obtain ⟨meaning',same,current,sourceDispatch⟩ :=
                        graph_primitive_return_execution represented control frames dispatch scalar
                      exact ⟨meaning',current,dispatch_advance represented same current noEnter sourceDispatch⟩
          | case arms environment =>
              cases value with
              | variant tag payload =>
                  cases found : arms.find? (fun arm => arm.1 == tag) with
                  | none => simp [stepRaw,control,frames,found,ResultControl] at successful
                  | some arm =>
                      obtain ⟨key,body⟩ := arm
                      obtain ⟨next,same,current,dispatch⟩ := graph_case_return_execution represented control frames found
                      exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | boolean _ | label _ | record _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful
          | ifBool whenTrue whenFalse environment =>
              cases value with
              | boolean value =>
                  obtain ⟨next,same,current,dispatch⟩ := graph_ifBool_return_execution represented control frames
                  exact ⟨next,current,dispatch_advance represented same current noEnter dispatch⟩
              | closure _ _ | specification _ _ | prototype _ _ | natural _ | label _ | record _ | variant _ _ =>
                  simp [stepRaw,control,frames,ResultControl] at successful

/-! ## Finite completion -/

 theorem rawRun_succ (ticks : Nat) (state : State) : rawRun (ticks+1) state = stepRaw (rawRun ticks state) := by
  rw [rawRun_add]; rfl

 theorem graphBy_whole_derivation {meaning : AddressMeaning} {state : State} {source result whole : Term}
    (represented : GraphRepresentsBy meaning state source) (terminates : Evaluates source result)
    (current : budgetWhole meaning state = some whole) : ∃ cost, SourceDerivation whole result cost := by
  obtain ⟨_,_,_,_,heap,before,control,stack⟩ := represented
  cases focusEq : budgetFocus meaning state with
  | none => simp [budgetWhole,focusEq] at current
  | some focus =>
      simp only [budgetWhole,focusEq,Option.map_some,Option.some.injEq] at current
      subst whole
      have focusSteps := budgetFocus_control_steps heap control focusEq
      have wholeSteps := sourceSteps_trans (stackRealizes_erases stack) (sourceSteps_stack meaning state.stack focusSteps)
      exact source_evaluates_derivation (sourceSteps_evaluates_tail wholeSteps terminates)

/-- Lexicographic descent on (whole residual source cost, stutter rank). -/
 theorem rawRun_terminating_completes_from {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) :
    ∀ (cost rank ticks : Nat) (meaning : AddressMeaning) (whole : Term),
      GraphRepresentsBy meaning (rawRun ticks (initial source)) source →
      budgetWhole meaning (rawRun ticks (initial source)) = some whole →
      SourceDerivation whole result cost → stutterRank (rawRun ticks (initial source)) = rank →
      ∃ count value, (rawRun count (initial source)).control = .complete value := by
  intro cost
  induction cost using Nat.strongRecOn with
  | ind cost costIH =>
  intro rank
  induction rank using Nat.strongRecOn with
  | ind rank rankIH =>
  intro ticks meaning whole represented current derivation ranked
  by_cases done : ∃ value, (rawRun ticks (initial source)).control = .complete value
  · obtain ⟨value,eq⟩ := done
    exact ⟨ticks,value,eq⟩
  · have running : ∀ value, (rawRun ticks (initial source)).control ≠ .complete value :=
      fun value eq => done ⟨value,eq⟩
    have successful : ResultControl (stepRaw (rawRun ticks (initial source))).control := by
      rw [←rawRun_succ]
      exact rawRun_terminating_resultControl closed terminates (ticks+1)
    obtain ⟨next,nextRepresented,before,after,old,new,advance⟩ :=
      graph_stepRaw_whole represented successful running
    have beforeEq : before = whole := Option.some.inj (old.symm.trans current)
    subst beforeEq
    rw [←rawRun_succ] at nextRepresented new
    rcases advance with ⟨middle,step,steps⟩ | ⟨steps,smaller⟩
    · obtain ⟨middleCost,middleDerivation,middleLt⟩ := sourceStep_derivation_tail step derivation
      obtain ⟨newCost,newDerivation,newLe⟩ := sourceSteps_derivation_tail steps middleDerivation
      exact costIH newCost (by omega) _ (ticks+1) next after nextRepresented new newDerivation rfl
    · obtain ⟨newCost,newDerivation,newLe⟩ := sourceSteps_derivation_tail steps derivation
      rcases Nat.lt_or_eq_of_le newLe with lt | eq
      · exact costIH newCost lt _ (ticks+1) next after nextRepresented new newDerivation rfl
      · subst eq
        rw [←rawRun_succ] at smaller
        exact rankIH _ (by omega) (ticks+1) next after nextRepresented new newDerivation rfl

/-- Termination: a closed source with an independent reference evaluation
drives the actual raw machine to `complete` in finitely many transitions. -/
 theorem rawRun_terminating_complete {source result : Term} (closed : Scoped 0 source)
    (terminates : Evaluates source result) :
    ∃ count value, (rawRun count (initial source)).control = .complete value := by
  obtain ⟨cost,derivation⟩ := source_evaluates_derivation terminates
  exact rawRun_terminating_completes_from closed terminates cost _ 0 (fun _ => .bound 0) source
    (graphBy_initializes closed)
    (by simp [budgetWhole,budgetFocus,initial,controlMeaning,closeTerm,stackMeaning,rawRun]) derivation rfl

/-- FINITE COMPLETION (B §7 gap 1). Closed source + independent evaluation to
a ground value ⇒ the actual unbounded raw run completes with that observation. -/
 theorem rawRun_finite_completion {source value : Term} {result : Observation}
    (closed : Scoped 0 source) (evaluates : Evaluates source value) (observes : Observes value result) :
    ∃ count, (rawRun count (initial source)).control = .complete (observationRuntime result) := by
  obtain ⟨count,final,complete⟩ := rawRun_terminating_complete closed evaluates
  have graph := rawRun_graph (graph_initializes closed) (by rw [complete]; trivial)
  obtain ⟨meaning,_,_,sound⟩ := graph_complete_value_sound graph complete
  have eq := source_evaluates_unique sound evaluates
  refine ⟨count,?_⟩
  rw [complete]
  cases observes <;> cases final <;> simp_all [valueMeaning,observationRuntime,closeTerm_lam_form]

/-- The same completion through the bounded executor at the trace's own
heap/stack maxima (`adequate_trace_completion`). -/
 theorem runBounded_finite_completion {source value : Term} {result : Observation}
    (closed : Scoped 0 source) (evaluates : Evaluates source value) (observes : Observes value result) :
    ∃ ticks final, runBounded (traceLimits ticks (initial source)) ticks (initial source) =
      .finished (observationRuntime result) final := by
  obtain ⟨count,complete⟩ := rawRun_finite_completion closed evaluates observes
  exact ⟨count,_,adequate_trace_completion complete⟩

/-! ## The Representation contract, inhabited

`Supported` is closedness (`Scoped 0`), the real admission predicate of the
edition: every elaborated program is closed, and nothing narrower is assumed.
The step is the machine's own bounded `step`, run at limits that admit the next
transition, read through an explicit Outcome → Transition adapter. -/

def groundObservation : RuntimeValue → Option Observation
  | .natural number => some (.natural number)
  | .boolean value => some (.boolean value)
  | .label name => some (.label name)
  | .closure _ _ | .record _ | .specification _ _ | .prototype _ _ | .variant _ _ => none

/-- Adapter: a tick suspension is an advance, unless it advanced into a fault
or blackhole (refusal); capacity suspension retains the exact state; only a
GROUND completion is a finished observation. -/
def outcomeTransition : Outcome → Transition State
  | .suspended .ticks next => match next.control with
      | .refused _ => .refused "refused"
      | .blackhole _ => .refused "blackhole"
      | _ => .advanced next
  | .suspended .capacity retained => .suspended retained
  | .finished value _ => match groundObservation value with
      | some result => .finished result
      | none => .refused "non-ground result"
  | .divergent _ _ => .refused "blackhole"
  | .refused _ _ => .refused "refused"

def machineTransition (state : State) : Transition State :=
  outcomeTransition (step (traceLimits 1 state) state)

 theorem machineTransition_running {state : State}
    (running : ∀ value, state.control ≠ .complete value)
    (noFault : ResultControl state.control) (successful : ResultControl (stepRaw state).control) :
    machineTransition state = .advanced (stepRaw state) := by
  have fits : step (traceLimits 1 state) state = .suspended .ticks (stepRaw state) := by
    cases control : state.control with
    | complete value => exact False.elim (running value control)
    | refused _ | blackhole _ => simp [control,ResultControl] at noFault
    | evaluate _ _ | enter _ | returned _ => simp [step,control,traceLimits]
  simp only [machineTransition,fits,outcomeTransition]
  cases next : (stepRaw state).control <;> simp_all [ResultControl]

 theorem machineTransition_advanced {state successor : State}
    (advanced : machineTransition state = .advanced successor) :
    successor = stepRaw state ∧ ResultControl successor.control ∧ ∀ value, state.control ≠ .complete value := by
  cases control : state.control with
  | complete value =>
      cases ground : groundObservation value <;>
        simp [machineTransition,step,control,outcomeTransition,ground] at advanced
  | refused _ | blackhole _ => simp [machineTransition,step,control,outcomeTransition] at advanced
  | evaluate _ _ | enter _ | returned _ =>
      have fits : step (traceLimits 1 state) state = .suspended .ticks (stepRaw state) := by
        simp [step,control,traceLimits]
      simp only [machineTransition,fits,outcomeTransition] at advanced
      cases next : (stepRaw state).control <;> simp [next] at advanced <;> subst advanced <;>
        simp [next,control,ResultControl]

 theorem machineTransition_finished {state : State} {result : Observation}
    (finished : machineTransition state = .finished result) :
    ∃ value, state.control = .complete value ∧ groundObservation value = some result := by
  cases control : state.control with
  | complete value =>
      cases ground : groundObservation value <;>
        simp [machineTransition,step,control,outcomeTransition,ground] at finished
      subst finished
      exact ⟨value,rfl,ground⟩
  | refused _ | blackhole _ => simp [machineTransition,step,control,outcomeTransition] at finished
  | evaluate _ _ | enter _ | returned _ =>
      have fits : step (traceLimits 1 state) state = .suspended .ticks (stepRaw state) := by
        simp [step,control,traceLimits]
      simp only [machineTransition,fits,outcomeTransition] at finished
      cases next : (stepRaw state).control <;> simp [next] at finished

 theorem machineTransition_suspension_exact {state retained : State}
    (suspended : machineTransition state = .suspended retained) : retained = state := by
  cases control : state.control with
  | complete value =>
      cases ground : groundObservation value <;>
        simp [machineTransition,step,control,outcomeTransition,ground] at suspended
  | refused _ | blackhole _ => simp [machineTransition,step,control,outcomeTransition] at suspended
  | evaluate _ _ | enter _ | returned _ =>
      have fits : step (traceLimits 1 state) state = .suspended .ticks (stepRaw state) := by
        simp [step,control,traceLimits]
      simp only [machineTransition,fits,outcomeTransition] at suspended
      cases next : (stepRaw state).control <;> simp [next] at suspended

def Represents (state : State) (whole : Term) : Prop :=
  ∃ meaning source, GraphRepresentsBy meaning state source ∧ budgetWhole meaning state = some whole

open Classical in
noncomputable def startSource (source : Term) : Option State :=
  if Scoped 0 source then some (initial source) else none

 theorem machine_simulation {state successor : State} {whole : Term}
    (represented : Represents state whole) (advanced : machineTransition state = .advanced successor) :
    ∃ next, Represents successor next ∧
      ((next = whole ∧ stutterRank successor < stutterRank state) ∨ PositiveSteps whole next) := by
  obtain ⟨rfl,successful,running⟩ := machineTransition_advanced advanced
  obtain ⟨meaning,source,graph,current⟩ := represented
  obtain ⟨next,nextGraph,before,after,old,new,advance⟩ := graph_stepRaw_whole graph successful running
  have beforeEq : before = whole := Option.some.inj (old.symm.trans current)
  subst beforeEq
  refine ⟨after,⟨next,source,nextGraph,new⟩,?_⟩
  rcases advance with ⟨middle,step,steps⟩ | ⟨steps,smaller⟩
  · exact Or.inr (.begin step steps)
  · cases steps with
    | refl => exact Or.inl ⟨rfl,smaller⟩
    | next step rest => exact Or.inr (.begin step rest)

 theorem machine_value_adequacy {state : State} {whole : Term} {result : Observation}
    (represented : Represents state whole) (finished : machineTransition state = .finished result) :
    ∃ value, Steps whole value ∧ Value value ∧ Observes value result := by
  obtain ⟨value,control,ground⟩ := machineTransition_finished finished
  obtain ⟨meaning,source,graph,current⟩ := represented
  have empty := graph.2.2.1 value control
  simp [budgetWhole,budgetFocus,control,controlMeaning,empty,stackMeaning] at current
  subst whole
  refine ⟨valueMeaning meaning value,.refl _,valueMeaning_value _ _,?_⟩
  cases value <;> simp [groundObservation] at ground <;> subst ground <;> simp [valueMeaning] <;> constructor

 theorem machine_steps_of_rawRun {count : Nat} {state : State} {value : RuntimeValue}
    (progress : ∀ ticks, ResultControl (rawRun ticks state).control)
    (complete : (rawRun count state).control = .complete value) :
    ∃ final, MachineSteps machineTransition state final ∧ final.control = .complete value := by
  induction count generalizing state with
  | zero => exact ⟨state,.refl _,complete⟩
  | succ count ih =>
      by_cases done : ∃ other, state.control = .complete other
      · obtain ⟨other,eq⟩ := done
        have absorbs : stepRaw state = state := by simp [stepRaw,eq]
        have same : rawRun (count+1) state = state := rawRun_absorbs (count+1) absorbs
        rw [same] at complete
        exact ⟨state,.refl _,complete⟩
      · have running : ∀ other, state.control ≠ .complete other := fun other eq => done ⟨other,eq⟩
        have advanced := machineTransition_running running (progress 0) (progress 1)
        obtain ⟨final,steps,last⟩ := ih (fun ticks => progress (ticks+1)) complete
        exact ⟨final,.next advanced steps,last⟩

 theorem machine_evaluation_complete {source value : Term} {result : Observation}
    (closed : Scoped 0 source) (evaluates : Evaluates source value) (observes : Observes value result) :
    ∃ initialState final, startSource source = some initialState ∧
      MachineSteps machineTransition initialState final ∧ machineTransition final = .finished result := by
  obtain ⟨count,complete⟩ := rawRun_finite_completion closed evaluates observes
  obtain ⟨final,steps,last⟩ := machine_steps_of_rawRun
    (rawRun_terminating_resultControl closed evaluates) complete
  refine ⟨initial source,final,by simp [startSource,closed],steps,?_⟩
  cases result <;> simp [machineTransition,step,last,outcomeTransition,groundObservation,observationRuntime]

/-- The Core4 demand machine inhabits the reference Representation contract
for EVERY closed source. Nothing here restricts the domain below closedness. -/
noncomputable def coreRepresentation : Representation State (Scoped 0) where
  represents := Represents
  start := startSource
  initializesSupported := fun source closed => ⟨initial source,by simp [startSource,closed]⟩
  initialized := by
    intro source state started
    by_cases closed : Scoped 0 source
    · simp [startSource,closed] at started
      subst state
      exact ⟨fun _ => .bound 0,source,graphBy_initializes closed,
        by simp [budgetWhole,budgetFocus,initial,controlMeaning,closeTerm,stackMeaning]⟩
    · simp [startSource,closed] at started
  step := machineTransition
  administrativeRank := stutterRank
  simulation := fun _ _ _ represented advanced => machine_simulation represented advanced
  valueAdequacy := fun _ _ _ represented finished => machine_value_adequacy represented finished
  suspensionExact := fun _ _ suspended => machineTransition_suspension_exact suspended
  evaluationComplete := fun _ _ _ closed evaluates observes => machine_evaluation_complete closed evaluates observes

/-! ## Non-vacuity -/

/-- A closed Fix program with a ground answer: `fix (λself λinh. inh) 7`. -/
def lazyFixedSeed : Term := .fix (.lam (.lam (.bound 0))) (.nat 7)

theorem lazyFixedSeed_closed : Scoped 0 lazyFixedSeed :=
  .fix (.lam (.lam (.bound (by decide)))) (.natural 7)

theorem lazyFixedSeed_evaluates : Evaluates lazyFixedSeed (.nat 7) := by
  constructor
  · refine .next (.fix _ _) ?_
    have first : Step
        (.app (.app (.lam (.lam (.bound 0))) (.fix (.lam (.lam (.bound 0))) (.nat 7))) (.nat 7))
        (.app (.lam (.bound 0)) (.nat 7)) := by
      simpa [instantiate,Term.substitute,liftSubstitution,Term.rename,liftRename] using
        (Step.application (.nat 7) (Step.beta (.lam (.bound 0)) (.fix (.lam (.lam (.bound 0))) (.nat 7))))
    have second : Step (.app (.lam (.bound 0)) (.nat 7)) (.nat 7) := by
      simpa [instantiate,Term.substitute] using (Step.beta (.bound 0) (.nat 7))
    exact .next first (.next second (.refl _))
  · exact .natural 7

theorem lazyFixedSeed_completes :
    ∃ count, (rawRun count (initial lazyFixedSeed)).control = .complete (.natural 7) :=
  rawRun_finite_completion (result := .natural 7) lazyFixedSeed_closed lazyFixedSeed_evaluates (.natural 7)

theorem lazyFixedSeed_supported_by_representation :
    ∃ initialState final, coreRepresentation.start lazyFixedSeed = some initialState ∧
      MachineSteps coreRepresentation.step initialState final ∧
      coreRepresentation.step final = .finished (.natural 7) :=
  coreRepresentation.evaluationComplete _ _ _ lazyFixedSeed_closed lazyFixedSeed_evaluates (.natural 7)

/-- Supported is not empty and not trivial: an open term is not started. -/
theorem open_term_not_started : startSource (.bound 0) = none := by
  have notClosed : ¬ Scoped 0 (.bound 0) := by simp
  simp [startSource,notClosed]

/-! Axiom pins. -/
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.stackMeaning_names_congr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms stackMeaning_names_congr
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.sourceStep_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms sourceStep_frame
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.sourceStep_stack' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms sourceStep_stack
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.controlMeaning_names_congr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms controlMeaning_names_congr
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.graphBy_names_congr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms graphBy_names_congr
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.budgetFocus_result_exists' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms budgetFocus_result_exists
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.rawRun_add' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms rawRun_add
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.graph_primitive_return_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms graph_primitive_return_execution
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.graph_extend_record_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms graph_extend_record_execution
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.graph_evaluate_fix_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms graph_evaluate_fix_execution
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.heapPotential_push' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms heapPotential_push
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.cellPotential_list_set' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms cellPotential_list_set
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.heapPotential_set' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms heapPotential_set
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.heapPotential_allocateFields' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms heapPotential_allocateFields
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.fields_potential_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fields_potential_lt
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.budgetFocus_of_controlMeaning' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms budgetFocus_of_controlMeaning
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.graphBy_same_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms graphBy_same_size
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.dispatch_advance' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms dispatch_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.closeTerm_nat' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms closeTerm_nat
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.closeTerm_boolean' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms closeTerm_boolean
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.closeTerm_label' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms closeTerm_label
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.stutter_advance' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms stutter_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.bound_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms bound_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.immediate_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms immediate_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.context_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms context_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.pair_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pair_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.record_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms record_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.fix_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fix_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.enter_suspended_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms enter_suspended_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.enter_cached_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms enter_cached_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.complete_return_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms complete_return_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.update_return_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms update_return_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.binaryLeft_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms binaryLeft_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.specification_call_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms specification_call_advance
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.graph_stepRaw_whole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms graph_stepRaw_whole
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.rawRun_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms rawRun_succ
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.graphBy_whole_derivation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms graphBy_whole_derivation
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.rawRun_terminating_completes_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rawRun_terminating_completes_from
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.rawRun_terminating_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rawRun_terminating_complete
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.rawRun_finite_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rawRun_finite_completion
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.runBounded_finite_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms runBounded_finite_completion
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.machineTransition_running' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms machineTransition_running
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.machineTransition_advanced' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms machineTransition_advanced
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.machineTransition_finished' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms machineTransition_finished
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.machineTransition_suspension_exact' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms machineTransition_suspension_exact
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.machine_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms machine_simulation
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.machine_value_adequacy' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms machine_value_adequacy
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.machine_steps_of_rawRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms machine_steps_of_rawRun
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.machine_evaluation_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms machine_evaluation_complete
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.lazyFixedSeed_closed' does not depend on any axioms
-/
#guard_msgs in
#print axioms lazyFixedSeed_closed
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.lazyFixedSeed_evaluates' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms lazyFixedSeed_evaluates
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.lazyFixedSeed_completes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lazyFixedSeed_completes
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.lazyFixedSeed_supported_by_representation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lazyFixedSeed_supported_by_representation
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.open_term_not_started' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms open_term_not_started
/--
info: 'Minidregg.Theory.ObjectiveBendDemandCompleteness.inject_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms inject_advance

end Minidregg.Theory.ObjectiveBendDemandCompleteness
