/- Preservation cases: Arithmetic. Imports only the shared Base; the dispatcher in
Theory/ObjectiveBendDemandPreservation.lean assembles every case module. -/
import Theory.ObjectiveBendDemandPreservation.Base
namespace Minidregg.Theory.ObjectiveBendDemandPreservation
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandTyping
set_option autoImplicit false

/-- Conversion boundaries retain the primitive's operand typing while the
left operand is moved from control into the actual continuation. -/
theorem stack_binary_left_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ primitive right environment rest, stack = .binaryLeft primitive right environment :: rest →
      ∃ _origin : ClosureTyping assumptions types ⟨right,environment⟩ (primitiveTypes primitive).1,
        ValueTyping assumptions types value (primitiveTypes primitive).1 ∧
        StackTyping assumptions types rest (primitiveTypes primitive).2 result := by
  induction continuation with
  | nil type => intro primitive right environment rest impossible; simp at impossible
  | cons frame restTyped =>
      intro primitive right environment rest same
      cases same
      cases frame with
      | binaryLeft origin => exact ⟨origin,valueTyped,restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro primitive right environment rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

/-- Finishing the left primitive operand preserves its type as a stored value,
and evaluates the same typed lexical right origin. This covers every primitive
and arbitrarily many source conversion boundaries. -/
theorem typed_binary_left_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {primitive : Primitive}
    {right : Term} {environment : Environment} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .binaryLeft primitive right environment :: rest) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨origin,leftTyped,restTyped⟩ :=
    stack_binary_left_value typed.stack valueTyped primitive right environment rest stack
  refine ⟨step_certificate typed (primitiveTypes primitive).1 ?_ ?_ ?_⟩
  · simpa [stepRaw,returned,stack] using typed.heap
  · simpa [stepRaw,returned,stack] using (ControlTyping.evaluate origin)
  · simpa [stepRaw,returned,stack] using (StackTyping.cons (.binaryRight leftTyped) restTyped)

/-- Actual Core4 primitive execution produces the promised typed scalar for
all typed operands. Bool is a distinct constructor, never a reserved String. -/
theorem primitive_result_typed {assumptions : Assumptions} {types : AddressTypes}
    (primitive : Primitive) {left right : RuntimeValue}
    (leftTyped : ValueTyping assumptions types left (primitiveTypes primitive).1)
    (rightTyped : ValueTyping assumptions types right (primitiveTypes primitive).1) :
    ∃ term next,
      (valueTerm left).bind (fun l => (valueTerm right).bind (primitiveResult primitive l)) = some term ∧
      scalarValue term = some next ∧ ValueTyping assumptions types next (primitiveTypes primitive).2 := by
  cases primitive with
  | add =>
      obtain ⟨first,rfl⟩ := natural_value_form leftTyped
      obtain ⟨second,rfl⟩ := natural_value_form rightTyped
      exact ⟨.nat (first+second),.natural (first+second),rfl,rfl,.natural _⟩
  | multiply =>
      obtain ⟨first,rfl⟩ := natural_value_form leftTyped
      obtain ⟨second,rfl⟩ := natural_value_form rightTyped
      exact ⟨.nat (first*second),.natural (first*second),rfl,rfl,.natural _⟩
  | equal =>
      obtain ⟨first,rfl⟩ := natural_value_form leftTyped
      obtain ⟨second,rfl⟩ := natural_value_form rightTyped
      exact ⟨.boolean (first==second),.boolean (first==second),rfl,rfl,.boolean _⟩
  | conjunction =>
      obtain ⟨first,rfl⟩ := boolean_value_form leftTyped
      obtain ⟨second,rfl⟩ := boolean_value_form rightTyped
      exact ⟨.boolean (first&&second),.boolean (first&&second),rfl,rfl,.boolean _⟩
  | labelEqual =>
      obtain ⟨first,rfl⟩ := label_value_form leftTyped
      obtain ⟨second,rfl⟩ := label_value_form rightTyped
      exact ⟨.boolean (first==second),.boolean (first==second),rfl,rfl,.boolean _⟩

theorem stack_binary_right_values {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {right : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (rightTyped : ValueTyping assumptions types right input) :
    ∀ primitive left rest, stack = .binaryRight primitive left :: rest →
      ValueTyping assumptions types left (primitiveTypes primitive).1 ∧
      ValueTyping assumptions types right (primitiveTypes primitive).1 ∧
      StackTyping assumptions types rest (primitiveTypes primitive).2 result := by
  induction continuation with
  | nil type => intro primitive left rest impossible; simp at impossible
  | cons frame restTyped =>
      intro primitive left rest same
      cases same
      cases frame with
      | binaryRight leftTyped => exact ⟨leftTyped,rightTyped,restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion rightTyped agreement)
  | returns pure restTyped ih =>
      intro primitive left rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

/-- The final primitive return branch both preserves typing and excludes its
semantic wrong-value refusal, with arbitrary retained source conversions. -/
theorem typed_binary_right_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {right left : RuntimeValue} {primitive : Primitive} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned right)
    (stack : state.stack = .binaryRight primitive left :: rest) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types right typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨leftTyped,rightTyped,restTyped⟩ :=
    stack_binary_right_values typed.stack valueTyped primitive left rest stack
  obtain ⟨term,next,primitiveRun,scalarRun,nextTyped⟩ := primitive_result_typed primitive leftTyped rightTyped
  refine ⟨step_certificate typed (primitiveTypes primitive).2 ?_ ?_ ?_⟩
  · simpa [stepRaw,returned,stack,primitiveRun,scalarRun] using typed.heap
  · simpa [stepRaw,returned,stack,primitiveRun,scalarRun] using (ControlTyping.returned nextTyped)
  · simpa [stepRaw,returned,stack,primitiveRun,scalarRun] using restTyped

theorem typed_binary_right_no_wrong_value {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {right left : RuntimeValue} {primitive : Primitive} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned right)
    (stack : state.stack = .binaryRight primitive left :: rest) :
    (stepRaw state).control ≠ .refused .wrongValue := by
  obtain ⟨next⟩ := typed_binary_right_preserved typed returned stack
  exact typed_control_not_refused next.control .wrongValue

theorem stack_condition_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ zero successor environment rest, stack = .condition zero successor environment :: rest →
      ∃ branchType context uses, ∃ _zeroOrigin : ClosureTyping assumptions types ⟨zero,environment⟩ branchType,
        EnvironmentTyping types context environment ∧
        PartialTyping assumptions (⟨.natural,.unrestricted⟩ :: context) successor branchType uses ∧
        safeUses (⟨.natural,.unrestricted⟩ :: context) uses = true ∧
        validContext assumptions.shareableVariables (⟨.natural,.unrestricted⟩ :: context) = true ∧
        ValueTyping assumptions types value .natural ∧
        StackTyping assumptions types rest branchType result := by
  induction continuation with
  | nil type => intro zero successor environment rest impossible; simp at impossible
  | cons frame restTyped =>
      intro zero successor environment rest same
      cases same
      cases frame with
      | condition zero environment successor safe valid =>
          exact ⟨_,_,_,zero,environment,successor,safe,valid,valueTyped,restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro zero successor environment rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

/-- Both conditional return branches preserve typing. The successor allocates
a typed cached predecessor, extends every old assignment monotonically, and
connects the actual lexical binder to that new address. -/
theorem typed_condition_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {zero successor : Term}
    {environment : Environment} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .condition zero successor environment :: rest) :
    ∃ after, TypeExtension types after ∧
      Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨branchType,context,uses,zeroTyped,environmentTyped,successorTyped,safe,valid,naturalTyped,restTyped⟩ :=
    stack_condition_value typed.stack valueTyped zero successor environment rest stack
  obtain ⟨number,rfl⟩ := natural_value_form naturalTyped
  cases number with
  | zero =>
      refine ⟨types,type_extension_refl types,⟨step_certificate typed branchType ?_ ?_ ?_⟩⟩
      · simpa [stepRaw,returned,stack] using typed.heap
      · simpa [stepRaw,returned,stack] using (ControlTyping.evaluate zeroTyped)
      · simpa [stepRaw,returned,stack] using restTyped
  | succ number =>
      let after := types ++ [.natural]
      have extension : TypeExtension types after := type_extension_append types [.natural]
      have assigned : after[state.heap.size]? = some .natural := by
        rw [← typed.heap.length]
        simp [after]
      let predecessor : ClosureTyping assumptions after ⟨.nat number,[]⟩ .natural :=
        ⟨[],[],EnvironmentTyping.empty after,.natural [] number,rfl,rfl⟩
      let next : ClosureTyping assumptions after ⟨successor,state.heap.size :: environment⟩ branchType :=
        ⟨⟨.natural,.unrestricted⟩ :: context,uses,
          (environmentTyped.weaken extension).cons assigned,successorTyped,safe,valid⟩
      refine ⟨after,extension,⟨step_alloc_certificate typed after branchType ?_ ?_ ?_⟩⟩
      · simpa [stepRaw,returned,stack] using
          heap_typed_push typed.heap (CellTyping.cached predecessor (.natural number) rfl)
      · simpa [stepRaw,returned,stack] using (ControlTyping.evaluate next)
      · simpa [stepRaw,returned,stack] using (StackTyping.weaken extension restTyped)

theorem typed_condition_no_wrong_value {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {zero successor : Term}
    {environment : Environment} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .condition zero successor environment :: rest) :
    (stepRaw state).control ≠ .refused .wrongValue := by
  obtain ⟨after,extension,⟨next⟩⟩ := typed_condition_preserved typed returned stack
  exact typed_control_not_refused next.control .wrongValue

end Minidregg.Theory.ObjectiveBendDemandPreservation
