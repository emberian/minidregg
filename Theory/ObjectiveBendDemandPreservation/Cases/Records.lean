/- Preservation cases: Records. Imports only the shared Base; the dispatcher in
Theory/ObjectiveBendDemandPreservation.lean assembles every case module. -/
import Theory.ObjectiveBendDemandPreservation.Base
namespace Minidregg.Theory.ObjectiveBendDemandPreservation
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandTyping
set_option autoImplicit false

/-- Every member demanded through an actual typed row is present in the runtime
record. Conversions retain the address's original assigned type and contribute
a checked member conversion path, including recursive alias tails. -/
theorem value_record_member {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {type : Ty} (typed : ValueTyping assumptions types value type) :
    ∀ fuel name member, type.lookup assumptions.bounds fuel name = some member →
      ∃ fields address actual,
        value = .record fields ∧ fields.find? (fun field => field.1 == name) = some (name,address) ∧
        types[address]? = some actual ∧ ConversionPath assumptions actual member := by
  induction typed with
  | record row members =>
      intro fuel name member lookup
      obtain ⟨address,actual,found,assigned,path⟩ := members fuel name member lookup
      exact ⟨_,address,actual,rfl,found,assigned,path⟩
  | conversion prior agreement ih =>
      intro fuel name member lookup
      obtain ⟨depth,actualMember,actualLookup,memberEq⟩ := same_type_lookup_transport agreement fuel name member lookup
      obtain ⟨fields,address,actual,shape,found,assigned,path⟩ := ih depth name actualMember actualLookup
      exact ⟨fields,address,actual,shape,found,assigned,.step path (canonical_same_type assumptions actualMember member memberEq)⟩
  | natural value => intro fuel name member lookup; cases fuel <;> simp [Ty.lookup] at lookup
  | boolean value => intro fuel name member lookup; cases fuel <;> simp [Ty.lookup] at lookup
  | label value => intro fuel name member lookup; cases fuel <;> simp [Ty.lookup,literalType] at lookup
  | closure environment body safe valid captures => intro fuel name member lookup; cases fuel <;> simp [Ty.lookup] at lookup
  | specification metadata ext => intro fuel name member lookup; cases fuel <;> simp [Ty.lookup] at lookup
  | prototype spec target => intro fuel name member lookup; cases fuel <;> simp [Ty.lookup] at lookup
  | variant rowLookup assigned path => intro fuel name member lookup; cases fuel <;> simp [Ty.lookup] at lookup

theorem stack_field_member {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ name rest, stack = .field name :: rest →
      ∃ fields address actual,
        value = .record fields ∧ fields.find? (fun field => field.1 == name) = some (name,address) ∧
        types[address]? = some actual ∧ StackTyping assumptions types rest actual result := by
  induction continuation with
  | nil => intro name rest impossible; simp at impossible
  | cons frame restTyped =>
      intro name rest same
      cases same
      cases frame with
      | field lookup =>
          obtain ⟨fields,address,actual,shape,found,assigned,path⟩ := value_record_member valueTyped _ name _ lookup
          exact ⟨fields,address,actual,shape,found,assigned,stack_convert_path path restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro name rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

/-- All typed field returns enter an existing correctly assigned field address.
First-field shadowing and finite alias conversions cannot cause missingField
or wrongValue; the heap's assigned member type remains unchanged. -/
theorem typed_field_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {name : String} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .field name :: rest) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨fields,address,actual,rfl,found,assigned,restTyped⟩ := stack_field_member typed.stack valueTyped name rest stack
  refine ⟨step_certificate typed actual ?_ ?_ ?_⟩
  · simpa [stepRaw,returned,stack,found] using typed.heap
  · simpa [stepRaw,returned,stack,found] using ControlTyping.enter assigned
  · simpa [stepRaw,returned,stack,found] using restTyped

theorem fields_loop_acc (environment : Environment) (fields : List (String × Term))
    (heap : Array Cell) (accumulator : List (String × Address)) :
    fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
      (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (heap,accumulator) =
    let pair := fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
      (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (heap,[])
    (pair.1,pair.2 ++ accumulator) := by
  induction fields generalizing heap accumulator with
  | nil => rfl
  | cons field fields ih =>
      simp only [List.foldl_cons]
      rw [ih (heap.push (.suspended ⟨field.2,environment⟩)) ((field.1,heap.size)::accumulator)]
      rw [ih (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]]
      simp [List.append_assoc]

theorem allocate_fields_cons (heap : Array Cell) (environment : Environment)
    (name : String) (body : Term) (fields : List (String × Term)) :
    allocateFields heap environment ((name,body)::fields) =
    let allocated := allocateFields (heap.push (.suspended ⟨body,environment⟩)) environment fields
    (allocated.1,(name,heap.size)::allocated.2) := by
  simp only [allocateFields,List.foldl_cons]
  rw [fields_loop_acc]
  simp [List.reverse_append]

/-- Every field allocation preserves old address assignments and first-name
lookup, with the field's actual source derivation and captured environment. -/
theorem typed_fields_allocation {assumptions : Assumptions} {context : Context}
    {fields : List (String × Term)} {row : Ty} {uses : Uses}
    (source : FieldsTyping assumptions context fields row uses)
    {types : AddressTypes} {heap : Array Cell} {environment : Environment}
    (heapTyped : HeapTyping assumptions types heap)
    (environmentTyped : EnvironmentTyping types context environment)
    (safe : safeUses context uses = true)
    (valid : validContext assumptions.shareableVariables context = true) :
    ∃ after, TypeExtension types after ∧ HeapTyping assumptions after (allocateFields heap environment fields).1 ∧
      ∀ fuel name member, row.lookup assumptions.bounds fuel name = some member →
        ∃ address, (allocateFields heap environment fields).2.find? (fun field => field.1 == name) = some (name,address) ∧
          after[address]? = some member := by
  induction fields generalizing row uses types heap with
  | nil =>
      cases source
      refine ⟨types,type_extension_refl types,?_,?_⟩
      · simpa [allocateFields] using heapTyped
      · intro fuel name member impossible
        cases fuel <;> simp [Ty.lookup] at impossible
  | cons field fields ih =>
      obtain ⟨name,body⟩ := field
      cases source with
      | cons bodyTyped restTyped bodyPure =>
        rename_i bodyType tailRow bodyUses restUses
        have bodyLength := source_uses_length bodyTyped
        have restLength := source_uses_length (PartialTyping.record restTyped)
        have bodySafe := safe_add_uses_left context _ _ bodyLength restLength safe
        have restSafe := safe_add_uses_right context _ _ bodyLength restLength safe
        let middle := types ++ [bodyType]
        have firstExtension : TypeExtension types middle := type_extension_append types [bodyType]
        let bodyOrigin : ClosureTyping assumptions middle ⟨body,environment⟩ _ :=
          ⟨context,_,environmentTyped.weaken firstExtension,bodyTyped,bodySafe,valid⟩
        have headHeap := heap_typed_push heapTyped (CellTyping.suspended bodyOrigin bodyPure)
        obtain ⟨after,secondExtension,tailHeap,tailMembers⟩ :=
          ih restTyped headHeap (environmentTyped.weaken firstExtension) restSafe
        refine ⟨after,type_extension_trans firstExtension secondExtension,?_,?_⟩
        · simpa only [allocate_fields_cons] using tailHeap
        · intro fuel query member lookup
          cases fuel with
          | zero => simp [Ty.lookup] at lookup
          | succ fuel =>
            by_cases hit : name = query
            · subst query
              have same : bodyType = member := by simpa [Ty.lookup] using lookup
              subst member
              refine ⟨heap.size,?_,?_⟩
              · simp [allocate_fields_cons]
              · apply secondExtension
                rw [← heapTyped.length]
                simp
            · have tailLookup : tailRow.lookup assumptions.bounds fuel query = some member := by
                simpa [Ty.lookup,hit] using lookup
              obtain ⟨address,found,assigned⟩ := tailMembers fuel query member tailLookup
              exact ⟨address,by simpa [allocate_fields_cons,hit] using found,assigned⟩

theorem allocate_fields_absent (heap : Array Cell) (environment : Environment)
    (fields : List (String × Term)) (name : String)
    (absent : fields.any (fun field => field.1 == name) = false) :
    (allocateFields heap environment fields).2.find? (fun field => field.1 == name) = none := by
  induction fields generalizing heap with
  | nil => rfl
  | cons field fields ih =>
      obtain ⟨prior,body⟩ := field
      have facts : prior ≠ name ∧ fields.any (fun field => field.1 == name) = false := by
        simpa only [List.any_cons,Bool.or_eq_false_iff,beq_eq_false_iff_ne] using absent
      simp [allocate_fields_cons,facts.1,ih _ facts.2]

theorem retained_fields_lookup (inherited : List (String × Address)) (fields : List (String × Term))
    (name : String) (absent : fields.any (fun field => field.1 == name) = false) :
    (inherited.filter (fun prior => !(fields.any fun field => field.1 == prior.1))).find? (fun field => field.1 == name) =
      inherited.find? (fun field => field.1 == name) := by
  induction inherited with
  | nil => rfl
  | cons prior inherited ih =>
      by_cases hit : prior.1 = name
      · simp [hit,absent]
      · by_cases removed : fields.any (fun field => field.1 == prior.1) = true
        · simp [removed,hit,ih]
        · have keep : fields.any (fun field => field.1 == prior.1) = false := by
            cases decision : fields.any (fun field => field.1 == prior.1) with
            | false => rfl
            | true => exact False.elim (removed decision)
          simp [keep,hit,ih]

theorem fields_overlay_lookup {assumptions : Assumptions} {context : Context}
    {fields : List (String × Term)} {row : Ty} {uses : Uses}
    (source : FieldsTyping assumptions context fields row uses) (inherited : Ty)
    (fuel : Nat) (name : String) (member : Ty)
    (lookup : (overlay row inherited).lookup assumptions.bounds fuel name = some member) :
    (∃ depth, row.lookup assumptions.bounds depth name = some member) ∨
      (fields.any (fun field => field.1 == name) = false ∧
        ∃ depth, inherited.lookup assumptions.bounds depth name = some member) := by
  induction fields generalizing row uses fuel with
  | nil => cases source; exact Or.inr ⟨rfl,fuel,lookup⟩
  | cons field fields ih =>
      obtain ⟨prior,body⟩ := field
      cases source with
      | cons bodyTyped restTyped bodyPure =>
        rename_i bodyType tailRow bodyUses restUses
        cases fuel with
        | zero => simp [Ty.lookup] at lookup
        | succ fuel =>
          by_cases hit : prior = name
          · exact Or.inl ⟨1,by simpa [Ty.lookup,overlay,hit] using lookup⟩
          · have next : (overlay tailRow inherited).lookup assumptions.bounds fuel name = some member := by
              simpa [overlay,Ty.lookup,hit] using lookup
            rcases ih restTyped fuel next with ⟨depth,lookup⟩ | ⟨absent,depth,lookup⟩
            · exact Or.inl ⟨depth+1,by simpa [Ty.lookup,hit] using lookup⟩
            · exact Or.inr ⟨by simp [hit,absent],depth,lookup⟩

theorem fields_overlay_row {assumptions : Assumptions} {context : Context}
    {fields : List (String × Term)} {row : Ty} {uses : Uses}
    (source : FieldsTyping assumptions context fields row uses) (inherited : Ty)
    (fuel : Nat) (isRow : inherited.isRow assumptions.bounds fuel = true) :
    ∃ depth, (overlay row inherited).isRow assumptions.bounds depth = true := by
  induction fields generalizing row uses with
  | nil => cases source; exact ⟨fuel,isRow⟩
  | cons field fields ih =>
      cases source with
      | cons bodyTyped restTyped bodyPure =>
        obtain ⟨depth,tailRow⟩ := ih restTyped
        exact ⟨depth+1,by simpa [overlay,Ty.isRow] using tailRow⟩

theorem source_record_decomposition {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .record fields => ∃ row, FieldsTyping assumptions context fields row uses ∧
        ConversionPath assumptions row type
    | _ => True := by
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .record fields => ∃ row, FieldsTyping assumptions context fields row uses ∧ ConversionPath assumptions row type
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
    obtain ⟨row,fields,path⟩ := ih
    exact ⟨row,fields,.step path agreement⟩
  · intros; trivial
  · intro context fields row uses fieldsTyped ihFields
    exact ⟨row,fieldsTyped,.refl row⟩
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
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- Actual record allocation preserves all typed addresses and lazy field
origins, including declaration-order first-field shadowing. Row conversion is
retained in the continuation rather than changing any allocated address type. -/
theorem typed_record_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {fields : List (String × Term)} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.record fields) environment) :
    ∃ after, TypeExtension types after ∧
      Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    obtain ⟨row,fieldsTyped,path⟩ := source_record_decomposition origin.source
    obtain ⟨after,extension,heap,members⟩ :=
      typed_fields_allocation fieldsTyped typed.heap origin.environment origin.safe origin.contextValid
    have value : ValueTyping assumptions after (.record (allocateFields state.heap environment fields).2) row :=
      .record (source_fields_row fieldsTyped) (by
        intro fuel name member lookup
        obtain ⟨address,found,assigned⟩ := members fuel name member lookup
        exact ⟨address,member,found,assigned,.refl member⟩)
    refine ⟨after,extension,⟨step_alloc_certificate typed after row ?_ ?_ ?_⟩⟩
    · simpa [stepRaw,evaluate] using heap
    · simpa [stepRaw,evaluate] using ControlTyping.returned value
    · simpa [stepRaw,evaluate] using
        StackTyping.weaken extension (stack_convert_path path typed.stack)

theorem stack_extend_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ fields environment rest, stack = .extend fields environment :: rest →
      ∃ inherited row context uses,
        EnvironmentTyping types context environment ∧ FieldsTyping assumptions context fields row uses ∧
        safeUses context uses = true ∧ validContext assumptions.shareableVariables context = true ∧
        inherited.isRow assumptions.bounds 64 = true ∧ ValueTyping assumptions types value inherited ∧
        StackTyping assumptions types rest (overlay row inherited) result := by
  induction continuation with
  | nil => intro fields environment rest impossible; simp at impossible
  | cons frame restTyped =>
      intro fields environment rest same
      cases same
      cases frame with
      | extend environment source safe valid row => exact ⟨_,_,_,_,environment,source,safe,valid,row,valueTyped,restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro fields environment rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

/-- Returning an inherited record under an overlay preserves its unknown tail
and immutable address types, while new fields shadow old names in the SAME
order as the executor. Member conversion evidence remains explicit. -/
theorem typed_extend_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {fields : List (String × Term)}
    {environment : Environment} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .extend fields environment :: rest) :
    ∃ after, TypeExtension types after ∧
      Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨inherited,row,context,uses,environmentTyped,source,safe,valid,rowValid,inheritedTyped,restTyped⟩ :=
    stack_extend_value typed.stack valueTyped fields environment rest stack
  obtain ⟨prior,rfl⟩ := record_value_form inheritedTyped 64 rowValid
  obtain ⟨after,extension,heap,newMembers⟩ := typed_fields_allocation source typed.heap environmentTyped safe valid
  let allocated := allocateFields state.heap environment fields
  let retained := prior.filter (fun old => !(fields.any fun field => field.1 == old.1))
  have newValue : ValueTyping assumptions after (.record (allocated.2 ++ retained)) (overlay row inherited) := by
    refine .record (fields_overlay_row source inherited 64 rowValid) ?_
    intro fuel name member lookup
    rcases fields_overlay_lookup source inherited fuel name member lookup with ⟨depth,newLookup⟩ | ⟨absent,depth,oldLookup⟩
    · obtain ⟨address,found,assigned⟩ := newMembers depth name member newLookup
      exact ⟨address,member,by simp [List.find?_append,allocated,found],assigned,.refl member⟩
    · obtain ⟨oldFields,address,actual,shape,found,assigned,path⟩ := value_record_member inheritedTyped depth name member oldLookup
      cases shape
      have noNew := allocate_fields_absent state.heap environment fields name absent
      exact ⟨address,actual,by simpa [List.find?_append,allocated,noNew,retained,retained_fields_lookup prior fields name absent] using found,
        extension address actual assigned,path⟩
  refine ⟨after,extension,⟨step_alloc_certificate typed after (overlay row inherited) ?_ ?_ ?_⟩⟩
  · simpa [stepRaw,returned,stack] using heap
  · simpa [stepRaw,returned,stack,allocated,retained] using ControlTyping.returned newValue
  · simpa [stepRaw,returned,stack] using StackTyping.weaken extension restTyped

end Minidregg.Theory.ObjectiveBendDemandPreservation
