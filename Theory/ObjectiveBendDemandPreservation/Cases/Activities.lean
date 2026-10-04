/- Preservation cases: Activities. Imports only the shared Base; the dispatcher in
Theory/ObjectiveBendDemandPreservation.lean assembles every case module. -/
import Theory.ObjectiveBendDemandPreservation.Base
namespace Minidregg.Theory.ObjectiveBendDemandPreservation
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandTyping
set_option autoImplicit false

/-- A perform's derivation: its plan is typed at a Plan sum and its activity
type reaches the derivation's type along a finite conversion path. -/
def PerformDerivation (assumptions : Assumptions) (context : Context) (plan : Term) (type : Ty) (uses : Uses) : Prop :=
  ∃ planType response, PartialTyping assumptions context plan planType uses ∧
    planType.isPlan = true ∧ response.isData = true ∧
    ConversionPath assumptions (.computation planType response response) type

def DoneDerivation (assumptions : Assumptions) (context : Context) (value : Term) (type : Ty) (uses : Uses) : Prop :=
  ∃ planType response result, PartialTyping assumptions context value result uses ∧
    result.isComputation = false ∧ ConversionPath assumptions (.computation planType response result) type

theorem source_perform_decomposition {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .perform plan => PerformDerivation assumptions context plan type uses
    | _ => True := by
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .perform plan => PerformDerivation assumptions context plan type uses
      | _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro context term actual expected uses prior agreement ih
    cases term <;> try trivial
    obtain ⟨planType,response,planTyped,isPlan,isData,path⟩ := ih
    exact ⟨planType,response,planTyped,isPlan,isData,.step path agreement⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro context plan planType response uses planTyped isPlan isData ih
    exact ⟨planType,response,planTyped,isPlan,isData,.refl _⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

theorem source_done_decomposition {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .done value => DoneDerivation assumptions context value type uses
    | _ => True := by
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .done value => DoneDerivation assumptions context value type uses
      | _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro context term actual expected uses prior agreement ih
    cases term <;> try trivial
    obtain ⟨planType,response,result,valueTyped,pure,path⟩ := ih
    exact ⟨planType,response,result,valueTyped,pure,.step path agreement⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro context value planType response result uses valueTyped pure ih
    exact ⟨planType,response,result,valueTyped,pure,.refl _⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- An activity continuation contains no update frame anywhere: forcing a
shared cell never sits under an activity, so a perform is never refused. -/
theorem stack_activity_no_update {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty}
    (typed : StackTyping assumptions types stack input result) :
    input.isComputation = true → forcingShared stack = false := by
  induction typed with
  | nil => intro _; rfl
  | cons frameTyped restTyped ih =>
      intro activity
      cases frameTyped with
      | argument argument callable copy =>
          simp [callable_arrow_not_computation callable] at activity
      | update assigned pure => simp_all
      | field lookup => simp [lookup_not_computation _ _ _ _ _ lookup] at activity
      | extend _ _ _ _ isRow => simp [isRow_not_computation _ _ _ isRow] at activity
      | binaryLeft right => rename_i primitive _ _; cases primitive <;> simp_all [primitiveTypes,Ty.isComputation]
      | binaryRight left => rename_i primitive _; cases primitive <;> simp_all [primitiveTypes,Ty.isComputation]
      | effectCase =>
          have rest := ih rfl
          simpa [forcingShared] using rest
      | _ => simp_all [Ty.isComputation]
  | conversion agreement restTyped ih =>
      intro activity; exact ih ((sameType_isComputation agreement) ▸ activity)
  | returns pure restTyped ih => intro activity; simp_all

/-- A perform outside every shared cell allocates its plan cell at the Plan
type and yields at its exact activity type; the stack is untouched. -/
theorem typed_perform_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {plan : Term} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.perform plan) environment) :
    ∃ after, TypeExtension types after ∧ Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    have decomposition : PerformDerivation assumptions origin.context plan typed.current origin.uses :=
      source_perform_decomposition origin.source
    obtain ⟨planType,response,planTyped,isPlan,isData,path⟩ := decomposition
    have activity : typed.current.isComputation = true := by
      rw [← conversionPath_isComputation path]; rfl
    have direct : forcingShared state.stack = false := stack_activity_no_update typed.stack activity
    have planPure : planType.isComputation = false := by
      cases planType <;> simp_all [Ty.isPlan,Ty.isComputation]
    let after := types ++ [planType]
    have extension : TypeExtension types after := type_extension_append types [planType]
    let planOrigin : ClosureTyping assumptions after ⟨plan,environment⟩ planType :=
      ⟨origin.context,origin.uses,origin.environment.weaken extension,planTyped,origin.safe,origin.contextValid⟩
    have assigned : after[state.heap.size]? = some planType := by
      rw [← typed.heap.length]
      simp [after]
    refine ⟨after,extension,⟨step_alloc_certificate typed after (.computation planType response response) ?_ ?_ ?_⟩⟩
    · simpa [stepRaw,evaluate,direct,after] using heap_typed_push typed.heap (CellTyping.suspended planOrigin planPure)
    · simpa [stepRaw,evaluate,direct] using (ControlTyping.yielded assigned isPlan isData : ControlTyping assumptions after _ _)
    · simpa [stepRaw,evaluate,direct] using StackTyping.weaken extension (stack_convert_path path typed.stack)

/-- `done v` continues with `v` at its pure type: the continuation, which
awaits an activity of that type, accepts it by `returns`. -/
theorem typed_done_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : Term} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.done value) environment) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    have decomposition : DoneDerivation assumptions origin.context value typed.current origin.uses :=
      source_done_decomposition origin.source
    obtain ⟨planType,response,valueType,valueTyped,pure,path⟩ := decomposition
    let valueOrigin : ClosureTyping assumptions types ⟨value,environment⟩ valueType :=
      ⟨origin.context,origin.uses,origin.environment,valueTyped,origin.safe,origin.contextValid⟩
    refine ⟨step_certificate typed valueType ?_ ?_ ?_⟩
    · simpa [stepRaw,evaluate] using typed.heap
    · simpa [stepRaw,evaluate] using ControlTyping.evaluate valueOrigin
    · simpa [stepRaw,evaluate] using StackTyping.returns pure (stack_convert_path path typed.stack)

/-! ## Activities: yields are quiescent; a typed response resumes a typed state -/

theorem forcingShared_false_updates {stack : List Frame} (direct : forcingShared stack = false) :
    ObjectiveBendDemandInvariant.stackUpdates stack = [] := by
  induction stack with
  | nil => rfl
  | cons frame rest ih =>
      cases frame <;> simp_all [forcingShared,ObjectiveBendDemandInvariant.stackUpdates]

theorem yielded_control_type {assumptions : Assumptions} {types : AddressTypes} {plan : Address} {type : Ty}
    (typed : ControlTyping assumptions types (.yielded plan) type) :
    ∃ planType response, type = .computation planType response response ∧
      types[plan]? = some planType ∧ planType.isPlan = true ∧ response.isData = true := by
  cases typed with
  | yielded assigned isPlan isData => exact ⟨_,_,rfl,assigned,isPlan,isData⟩

/-- A typed yielded state awaits no shared cell: no frame forces one, and no
cell is half-evaluated. Every yield is a quiescent safe point. -/
theorem typed_yield_quiescent {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {plan : Address}
    (typed : StateTyping assumptions types state result) (yielded : state.control = .yielded plan) :
    forcingShared state.stack = false ∧
      ∀ (address : Address) (origin : Closure), state.heap[address]? ≠ some (Cell.evaluating origin) := by
  obtain ⟨planType,response,currentEq,_,_,_⟩ := yielded_control_type (yielded ▸ typed.control)
  have direct := stack_activity_no_update typed.stack (by rw [currentEq]; rfl)
  refine ⟨direct,?_⟩
  intro address origin found
  have member := (typed.busy.2 address).mpr ⟨origin,found⟩
  simp [forcingShared_false_updates direct] at member

/-- The checked program's own activity signature reaches every yield: the
continuation of a yield passes activities only through effect cases, which
keep the Plan and Response types. -/
theorem stack_activity_signature {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty}
    (typed : StackTyping assumptions types stack input result) :
    ∀ plan response produced, input.canonical = (Ty.computation plan response produced).canonical →
      ∃ final, result.canonical = (Ty.computation plan response final).canonical := by
  induction typed with
  | nil => intro plan response produced equal; exact ⟨produced,equal⟩
  | cons frameTyped restTyped ih =>
      intro plan response produced equal
      have activity := congrArg Ty.isComputation equal
      rw [Ty.canonical_isComputation,Ty.canonical_isComputation] at activity
      change _ = true at activity
      cases frameTyped with
      | argument argument callable copy =>
          simp [callable_arrow_not_computation callable] at activity
      | update assigned pure => simp_all
      | field lookup => simp [lookup_not_computation _ _ _ _ _ lookup] at activity
      | extend _ _ _ _ isRow => simp [isRow_not_computation _ _ _ isRow] at activity
      | binaryLeft right => rename_i primitive _ _; cases primitive <;> simp_all [primitiveTypes,Ty.isComputation]
      | binaryRight left => rename_i primitive _; cases primitive <;> simp_all [primitiveTypes,Ty.isComputation]
      | effectCase environmentTyped armsTyped valid pure =>
          obtain ⟨planEq,responseEq,_⟩ := computation_canonical_inj equal
          obtain ⟨final,finalEq⟩ := ih _ _ _ rfl
          refine ⟨final,?_⟩
          rw [finalEq]
          simp only [Ty.canonical,planEq,responseEq]
      | _ => simp_all [Ty.isComputation,Ty.canonical]
  | conversion agreement restTyped ih =>
      intro plan response produced equal
      exact ih plan response produced (sameType_activity_canonical agreement equal)
  | returns pure restTyped ih =>
      intro plan response produced equal
      rw [← Ty.canonical_isComputation,equal] at pure
      simp [Ty.canonical,Ty.isComputation] at pure

/-- Resuming a typed yield with a closed response typed at the PROGRAM's
declared response type yields a typed state: the response is evaluated at the
yield's response type and the untouched continuation takes it by `returns`. -/
theorem typed_resume_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state next : State} {plan : Address} {response : Term}
    {entryPlan entryResponse entryResult : Ty} {uses : Uses}
    (typed : StateTyping assumptions types state (.computation entryPlan entryResponse entryResult))
    (yielded : state.control = .yielded plan)
    (responseTyped : PartialTyping assumptions [] response entryResponse uses)
    (resumed : resume response state = some next) :
    Nonempty (StateTyping assumptions types next (.computation entryPlan entryResponse entryResult)) := by
  obtain ⟨heapEq,stackEq,controlEq⟩ := resume_keeps_heap_and_stack response state next resumed
  obtain ⟨planType,responseType,currentEq,assigned,isPlan,isData⟩ := yielded_control_type (yielded ▸ typed.control)
  have stackTyped := typed.stack
  rw [currentEq] at stackTyped
  obtain ⟨final,finalEq⟩ := stack_activity_signature stackTyped planType responseType responseType rfl
  obtain ⟨_,responseAgree,_⟩ := computation_canonical_inj finalEq
  have responsePure : responseType.isComputation = false := by
    cases responseType <;> simp_all [Ty.isData,Ty.isComputation]
  have uses0 : uses = [] := by simpa using source_uses_length responseTyped
  subst uses0
  let origin : ClosureTyping assumptions types ⟨response,[]⟩ responseType :=
    ⟨[],[],EnvironmentTyping.empty types,
      .conversion responseTyped (canonical_same_type assumptions _ _ responseAgree),rfl,rfl⟩
  have closedResponse := source_scoped responseTyped
  refine ⟨⟨responseType,heapEq ▸ typed.heap,?_,?_,typed.assumptionsValid,?_,?_,?_⟩⟩
  · rw [controlEq]; exact .evaluate origin
  · rw [stackEq]; exact .returns responsePure stackTyped
  · obtain ⟨cells,_,frames⟩ := typed.lexical
    refine ⟨by rw [heapEq]; exact cells,?_,by rw [stackEq,heapEq]; exact frames⟩
    rw [controlEq]
    exact ⟨by simpa using closedResponse,by intro address member; simp at member⟩
  · unfold ObjectiveBendDemandInvariant.BusyInvariant
    rw [heapEq,stackEq]; exact typed.busy
  · intro value complete
    rw [controlEq] at complete
    cases complete

/-- A concrete inhabitant of the response premise: the counter's `written`
outcome, as the closed data term a kernel resumes with, is typed at the
counter's declared Response sum. -/
theorem written_response_typed :
    PartialTyping {} [] (.inject "written" (.record [])) responseType [] :=
  .inject (fuel := 1) (.record (.nil [])) (by decide) rfl

end Minidregg.Theory.ObjectiveBendDemandPreservation
