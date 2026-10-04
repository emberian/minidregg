/- Preservation lemmas over the frozen demand graph and actual source typing.
All-constructor preservation connects the checker derivation to every actual
raw transition; termination, liveness and native authority are separate. -/
import Theory.ObjectiveBendDemandPreservation.Cases.Functions
import Theory.ObjectiveBendDemandPreservation.Cases.Pairs
import Theory.ObjectiveBendDemandPreservation.Cases.Records
import Theory.ObjectiveBendDemandPreservation.Cases.Arithmetic
import Theory.ObjectiveBendDemandPreservation.Cases.Sums
import Theory.ObjectiveBendDemandPreservation.Cases.Activities
import Theory.ObjectiveBendStepCases
namespace Minidregg.Theory.ObjectiveBendDemandPreservation
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandTyping
set_option autoImplicit false

/-- Every raw-machine constructor preserves typing over a monotonically
extended address assignment. Captured quantities travel with lexical origins,
closures, continuation arguments and generated mix/Fix bodies. -/
theorem typed_stepRaw_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result) :
    ∃ after, TypeExtension types after ∧ Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  -- one named line per branch of `stepRaw`; the case split itself is `StepCases.apply`
  refine StepCases.apply (P := fun state => ∀ types, StateTyping assumptions types state result →
      ∃ after, TypeExtension types after ∧ Nonempty (StateTyping assumptions after (stepRaw state) result))
    { complete := fun _ _ control types typed => ⟨types, type_extension_refl types, by simpa [stepRaw, control] using (Nonempty.intro typed)⟩
      refused := fun _ reason control _ typed => False.elim (typed_control_not_refused typed.control reason control)
      blackhole := fun _ _ control types typed => ⟨types, type_extension_refl types, by simpa [stepRaw, control] using (Nonempty.intro typed)⟩
      yielded := fun _ _ control types typed => ⟨types, type_extension_refl types, by simpa [stepRaw, control] using (Nonempty.intro typed)⟩
      enter := fun _ _ control types typed => ⟨types, type_extension_refl types, typed_enter_preserved typed control⟩
      evaluate_bound := fun _ _ _ control types typed => ⟨types, type_extension_refl types, typed_bound_preserved typed control⟩
      evaluate_lam := fun _ _ _ control types typed => ⟨types, type_extension_refl types, typed_immediate_preserved typed control rfl⟩
      evaluate_nat := fun _ _ _ control types typed => ⟨types, type_extension_refl types, typed_immediate_preserved typed control rfl⟩
      evaluate_boolean := fun _ _ _ control types typed => ⟨types, type_extension_refl types, typed_immediate_preserved typed control rfl⟩
      evaluate_label := fun _ _ _ control types typed => ⟨types, type_extension_refl types, typed_immediate_preserved typed control rfl⟩
      evaluate_app := fun _ _ _ _ control types typed => ⟨types, type_extension_refl types, typed_application_focus_preserved typed control⟩
      evaluate_mix := fun _ _ _ _ control types typed => ⟨types, type_extension_refl types, typed_mix_preserved typed control⟩
      evaluate_fix := fun _ _ _ _ control _ typed => typed_fix_preserved typed control
      evaluate_record := fun _ _ _ control _ typed => typed_record_preserved typed control
      evaluate_specification := fun _ _ _ _ control _ typed => typed_pair_preserved typed true control
      evaluate_prototype := fun _ _ _ _ control _ typed => typed_pair_preserved typed false control
      evaluate_get := fun _ _ _ _ control types typed => ⟨types, type_extension_refl types, typed_source_focus_preserved typed control rfl⟩
      evaluate_extend := fun _ _ _ _ control types typed => ⟨types, type_extension_refl types, typed_source_focus_preserved typed control rfl⟩
      evaluate_reflect := fun _ _ _ control types typed => ⟨types, type_extension_refl types, typed_source_focus_preserved typed control rfl⟩
      evaluate_metadata := fun _ _ _ control types typed => ⟨types, type_extension_refl types, typed_source_focus_preserved typed control rfl⟩
      evaluate_project := fun _ _ _ control types typed => ⟨types, type_extension_refl types, typed_source_focus_preserved typed control rfl⟩
      evaluate_binary := fun _ _ _ _ _ control types typed => ⟨types, type_extension_refl types, typed_source_focus_preserved typed control rfl⟩
      evaluate_ifZero := fun _ _ _ _ _ control types typed => ⟨types, type_extension_refl types, typed_source_focus_preserved typed control rfl⟩
      evaluate_inject := fun _ _ _ _ control _ typed => typed_inject_preserved typed control
      evaluate_case := fun _ _ _ _ control types typed => ⟨types, type_extension_refl types, typed_source_focus_preserved typed control rfl⟩
      evaluate_ifBool := fun _ _ _ _ _ control types typed => ⟨types, type_extension_refl types, typed_source_focus_preserved typed control rfl⟩
      evaluate_perform := fun _ _ _ control _ typed => typed_perform_preserved typed control
      evaluate_done := fun _ _ _ control types typed => ⟨types, type_extension_refl types, typed_done_preserved typed control⟩
      return_nil := fun _ _ control stack types typed => ⟨types, type_extension_refl types, typed_completion_preserved typed control stack⟩
      return_argument := fun _ _ _ _ _ control stack _ typed => typed_argument_return_preserved typed control stack
      return_update := fun _ _ _ _ control stack types typed => ⟨types, type_extension_refl types, typed_update_preserved typed control stack⟩
      return_field := fun _ _ _ _ control stack types typed => ⟨types, type_extension_refl types, typed_field_preserved typed control stack⟩
      return_reflect := fun _ _ _ control stack types typed =>
        ⟨types, type_extension_refl types, typed_prototype_projection_preserved typed true control stack⟩
      return_metadata := fun _ _ _ control stack types typed => ⟨types, type_extension_refl types, typed_metadata_preserved typed control stack⟩
      return_project := fun _ _ _ control stack types typed =>
        ⟨types, type_extension_refl types, typed_prototype_projection_preserved typed false control stack⟩
      return_extend := fun _ _ _ _ _ control stack _ typed => typed_extend_preserved typed control stack
      return_condition := fun _ _ _ _ _ _ control stack _ typed => typed_condition_preserved typed control stack
      return_binaryLeft := fun _ _ _ _ _ _ control stack types typed =>
        ⟨types, type_extension_refl types, typed_binary_left_preserved typed control stack⟩
      return_binaryRight := fun _ _ _ _ _ control stack types typed =>
        ⟨types, type_extension_refl types, typed_binary_right_preserved typed control stack⟩
      return_case := fun _ _ _ _ _ control stack _ typed => typed_case_preserved typed control stack
      return_ifBool := fun _ _ _ _ _ _ control stack types typed =>
        ⟨types, type_extension_refl types, typed_ifBool_preserved typed control stack⟩ }
    state types typed

/-- Every finite reachable state of the SAME checked erasure has a typed heap,
control and continuation. This theorem does not assert that evaluation ends. -/
theorem checked_reachable_typed (source : AnnotatedTerm) (checked : Checked source [])
    {state : State} (reachable : ObjectiveBendDemandInvariant.Reachable (initial source.erase) state) :
    ∃ types, Nonempty (StateTyping source.assumptions types state checked.type) := by
  induction reachable with
  | start => exact ⟨[],⟨checked_initial_state source checked⟩⟩
  | next reachable ih =>
      obtain ⟨types,⟨typed⟩⟩ := ih
      obtain ⟨after,extension,next⟩ := typed_stepRaw_preserved typed
      exact ⟨after,next⟩

/-- Actual closed checker derivations exclude every raw semantic/internal
refusal along arbitrary reachable executions. Divergence, blackholes and
bounded-executor resource suspension remain allowed. -/
theorem checked_reachable_no_refusal (source : AnnotatedTerm) (checked : Checked source [])
    {state : State} (reachable : ObjectiveBendDemandInvariant.Reachable (initial source.erase) state)
    (reason : Refusal) : state.control ≠ .refused reason := by
  obtain ⟨types,⟨typed⟩⟩ := checked_reachable_typed source checked reachable
  exact typed_control_not_refused typed.control reason

theorem checked_reachable_no_wrong_value_or_missing_field (source : AnnotatedTerm)
    (checked : Checked source []) {state : State}
    (reachable : ObjectiveBendDemandInvariant.Reachable (initial source.erase) state) :
    state.control ≠ .refused .wrongValue ∧ state.control ≠ .refused .missingField :=
  ⟨checked_reachable_no_refusal source checked reachable .wrongValue,
    checked_reachable_no_refusal source checked reachable .missingField⟩

/-- The bounded executor cannot return a refusal from ANY typed machine state.
It may finish, diverge at a blackhole, or suspend with its exact continuation. -/
theorem typed_runBounded_no_refusal {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result)
    (limits : Limits) (ticks : Nat) (reason : Refusal) (retained : State) :
    runBounded limits ticks state ≠ .refused reason retained := by
  induction ticks generalizing types state with
  | zero =>
      cases control : state.control <;> simp only [runBounded,control] <;> try simp
      exact False.elim (typed_control_not_refused typed.control _ control)
  | succ ticks ih =>
      cases control : state.control <;> simp only [runBounded,step,control] <;> try simp
      all_goals try exact False.elim (typed_control_not_refused typed.control _ control)
      all_goals
        by_cases fits : (stepRaw state).heap.size ≤ limits.heap ∧ (stepRaw state).stack.length ≤ limits.stack
        · obtain ⟨after,extension,⟨next⟩⟩ := typed_stepRaw_preserved typed
          simpa [fits] using ih next
        · simp [fits]

/-- This is the SAME proof-producing checker and SAME decoded erasure consumed
by ObjectiveBendPreview: successful closed checking excludes bounded-executor
refusals at any tick, heap and stack budget. No termination claim is added. -/
theorem check_runBounded_no_refusal (source : AnnotatedTerm) (typeFuel : Nat)
    (checked : Checked source []) (_accepted : check source [] typeFuel = some checked)
    (limits : Limits) (ticks : Nat) (reason : Refusal) (retained : State) :
    runBounded limits ticks (initial source.erase) ≠ .refused reason retained := by
  exact typed_runBounded_no_refusal (checked_initial_state source checked) limits ticks reason retained

/-- The actual checker token excludes all three internal-reference refusals
through arbitrary raw-machine reachability. The stronger all-refusal theorem
above additionally covers semantic operands. Blackholes and bounds may suspend. -/
theorem checked_reachable_no_internal_refusal (source : AnnotatedTerm)
    (checked : Checked source []) {state : State}
    (reachable : ObjectiveBendDemandInvariant.Reachable (initial source.erase) state) :
    state.control ≠ .refused .unbound ∧ state.control ≠ .refused .missingCell ∧
      state.control ≠ .refused .invalidUpdate :=
  ObjectiveBendDemandInvariant.reachable_no_internalRefusal (source_scoped checked.derivation) reachable

#assert_axioms same_type_preserves_head value_head_correct typed_binary_right_no_wrong_value
  typed_condition_preserved typed_condition_no_wrong_value canonical_lookup typed_bound_preserved
  typed_application_focus_preserved typed_enter_preserved typed_update_preserved
  checked_reachable_no_internal_refusal source_insert_binding typed_mix_preserved
  typed_fix_preserved typed_record_preserved typed_field_preserved typed_extend_preserved
  typed_stepRaw_preserved checked_reachable_typed checked_reachable_no_refusal
  checked_reachable_no_wrong_value_or_missing_field typed_runBounded_no_refusal
  check_runBounded_no_refusal typed_inject_preserved typed_case_preserved typed_ifBool_preserved
  arms_typing_find value_variant_fields typed_yield_quiescent typed_resume_preserved
  typed_perform_preserved

end Minidregg.Theory.ObjectiveBendDemandPreservation
