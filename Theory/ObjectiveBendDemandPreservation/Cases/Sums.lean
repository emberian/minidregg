/- Preservation cases: Sums. Imports only the shared Base; the dispatcher in
Theory/ObjectiveBendDemandPreservation.lean assembles every case module. -/
import Theory.ObjectiveBendDemandPreservation.Base
namespace Minidregg.Theory.ObjectiveBendDemandPreservation
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandTyping
set_option autoImplicit false

def InjectDerivation (assumptions : Assumptions) (context : Context)
    (tag : String) (payload : Term) (type : Ty) (uses : Uses) : Prop :=
  ∃ payloadType row fuel, PartialTyping assumptions context payload payloadType uses ∧
    row.lookup assumptions.bounds fuel tag = some payloadType ∧
    ConversionPath assumptions (.variant row) type

theorem source_inject_decomposition {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .inject tag payload => InjectDerivation assumptions context tag payload type uses
    | _ => True := by
  apply PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .inject tag payload => InjectDerivation assumptions context tag payload type uses
      | _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (t := source)
  case conversion =>
    intro context term actual expected uses prior agreement ih
    cases term <;> try trivial
    obtain ⟨payloadType,row,fuel,payloadTyped,lookup,path⟩ := ih
    exact ⟨payloadType,row,fuel,payloadTyped,lookup,.step path agreement⟩
  case inject =>
    intro context tag payload payloadType row uses fuel payloadTyped lookup _ ih
    exact ⟨payloadType,row,fuel,payloadTyped,lookup,.refl _⟩
  all_goals (intros; trivial)

/-- The injection decomposition with the payload's suspendability. -/
def InjectPureDerivation (assumptions : Assumptions) (context : Context)
    (tag : String) (payload : Term) (type : Ty) (uses : Uses) : Prop :=
  ∃ payloadType row fuel, PartialTyping assumptions context payload payloadType uses ∧
    row.lookup assumptions.bounds fuel tag = some payloadType ∧ payloadType.isComputation = false ∧
    ConversionPath assumptions (.variant row) type

theorem source_inject_decomposition_pure {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .inject tag payload => InjectPureDerivation assumptions context tag payload type uses
    | _ => True := by
  apply PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .inject tag payload => InjectPureDerivation assumptions context tag payload type uses
      | _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (t := source)
  case conversion =>
    intro context term actual expected uses prior agreement ih
    cases term <;> try trivial
    obtain ⟨payloadType,row,fuel,payloadTyped,lookup,pure,path⟩ := ih
    exact ⟨payloadType,row,fuel,payloadTyped,lookup,pure,.step path agreement⟩
  case inject =>
    intro context tag payload payloadType row uses fuel payloadTyped lookup pure ih
    exact ⟨payloadType,row,fuel,payloadTyped,lookup,pure,.refl _⟩
  all_goals (intros; trivial)

/-- Injection allocates its payload thunk at the payload's source type; the
returned variant is typed at the declared row by that exact address. -/
theorem typed_inject_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {tag : String} {payload : Term} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.inject tag payload) environment) :
    ∃ after, TypeExtension types after ∧
      Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    have decomposition : InjectPureDerivation assumptions origin.context tag payload typed.current origin.uses :=
      source_inject_decomposition_pure origin.source
    obtain ⟨payloadType,row,fuel,payloadTyped,lookup,payloadPure,path⟩ := decomposition
    let after := types ++ [payloadType]
    have extension : TypeExtension types after := type_extension_append types [payloadType]
    let payloadOrigin : ClosureTyping assumptions after ⟨payload,environment⟩ payloadType :=
      ⟨origin.context,origin.uses,origin.environment.weaken extension,payloadTyped,origin.safe,origin.contextValid⟩
    have assigned : after[state.heap.size]? = some payloadType := by
      rw [← typed.heap.length]
      simp [after]
    have value : ValueTyping assumptions after (.variant tag state.heap.size) (.variant row) :=
      .variant lookup assigned (.refl _)
    refine ⟨after,extension,⟨step_alloc_certificate typed after (.variant row) ?_ ?_ ?_⟩⟩
    · simpa [stepRaw,evaluate,after] using heap_typed_push typed.heap (CellTyping.suspended payloadOrigin payloadPure)
    · simpa [stepRaw,evaluate] using ControlTyping.returned value
    · simpa [stepRaw,evaluate] using StackTyping.weaken extension (stack_convert_path path typed.stack)

/-- Arms typed in source order denote a closed row whose first visible member
for a label is exactly the binder type of the first matching arm. -/
theorem arms_row_closed {assumptions : Assumptions} {context : Context} {arms : List (String × Term)}
    {row result : Ty} {uses : Uses} (typed : ArmsTyping assumptions context arms row result uses) :
    row.tail = .emptyRow := by
  induction arms generalizing row uses with
  | nil => cases typed; rfl
  | cons arm rest ih =>
      cases typed with
      | cons bodyTyped safe shareable restTyped => simpa [Ty.tail] using ih restTyped

theorem arms_typing_find {assumptions : Assumptions} {context : Context} {arms : List (String × Term)}
    {row result : Ty} {uses : Uses} (typed : ArmsTyping assumptions context arms row result uses)
    {tag key : String} {body : Term} (found : arms.find? (fun arm => arm.1 == tag) = some (key,body)) :
    key = tag ∧ ∃ payload bodyUses, finiteLookup row tag = some payload ∧
      PartialTyping assumptions (⟨payload,.unrestricted⟩ :: context) body result bodyUses ∧
      safeUses (⟨payload,.unrestricted⟩ :: context) bodyUses = true ∧
      payload.shareableUnder assumptions.shareableVariables = true := by
  induction arms generalizing row uses with
  | nil => simp at found
  | cons arm rest ih =>
      obtain ⟨name,armBody⟩ := arm
      cases typed with
      | cons bodyTyped safe shareable restTyped =>
        by_cases hit : name = tag
        · subst hit
          simp at found
          obtain ⟨rfl,rfl⟩ := found
          exact ⟨rfl,_,_,by simp [finiteLookup],bodyTyped,safe,shareable⟩
        · have next : rest.find? (fun arm => arm.1 == tag) = some (key,body) := by simpa [hit] using found
          obtain ⟨keyEq,payload,bodyUses,lookup,typedBody,safeBody,share⟩ := ih restTyped next
          exact ⟨keyEq,payload,bodyUses,by simpa [finiteLookup,hit] using lookup,typedBody,safeBody,share⟩

theorem arms_typing_absent {assumptions : Assumptions} {context : Context} {arms : List (String × Term)}
    {row result : Ty} {uses : Uses} (typed : ArmsTyping assumptions context arms row result uses)
    {tag : String} (absent : arms.find? (fun arm => arm.1 == tag) = none) : finiteLookup row tag = none := by
  induction arms generalizing row uses with
  | nil => cases typed; rfl
  | cons arm rest ih =>
      obtain ⟨name,armBody⟩ := arm
      cases typed with
      | cons bodyTyped safe shareable restTyped =>
        have hit : name ≠ tag := by intro same; subst same; simp at absent
        have next : rest.find? (fun arm => arm.1 == tag) = none := by simpa [hit] using absent
        simpa [finiteLookup,hit] using ih restTyped next

theorem closed_lookup_finite {bounds : Bounds} {row member : Ty} {fuel : Nat} {name : String}
    (closed : row.tail = .emptyRow) (lookup : row.lookup bounds fuel name = some member) :
    finiteLookup row name = some member := by
  rcases lookup_prefix_or_alias bounds fuel row name member lookup with visible | ⟨_,index,_,_,tail,_,_⟩
  · exact visible
  · rw [closed] at tail; cases tail

theorem stack_case_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ arms environment rest, stack = .case arms environment :: rest →
      ∃ row branchType context uses, EnvironmentTyping types context environment ∧
        ArmsTyping assumptions context arms row branchType uses ∧
        validContext assumptions.shareableVariables context = true ∧
        ValueTyping assumptions types value (.variant row) ∧
        StackTyping assumptions types rest branchType result := by
  induction continuation with
  | nil type => intro arms environment rest impossible; simp at impossible
  | cons frame restTyped =>
      intro arms environment rest same
      cases same
      cases frame with
      | case environmentTyped armsTyped valid => exact ⟨_,_,_,_,environmentTyped,armsTyped,valid,valueTyped,restTyped⟩
      | effectCase => exact absurd (value_typed_not_computation valueTyped) (by simp [Ty.isComputation])
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro arms environment rest same
      obtain ⟨row,planType,responseType,branch,context,uses,environmentTyped,armsTyped,valid,produced,restTyped'⟩ :=
        stack_effect_case restTyped arms environment rest _ _ _ same rfl
      exact ⟨row,.computation planType responseType branch,context,uses,environmentTyped,armsTyped,valid,
        .conversion valueTyped (canonical_same_type assumptions _ _ produced),restTyped'⟩

/-- A typed returned variant always has its arm (no missingArm), and the arm
binder is a fresh indirection cell typed at the arm's declared payload type,
reached from the payload's own address type along a finite conversion path. -/
theorem typed_case_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {arms : List (String × Term)}
    {environment : Environment} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .case arms environment :: rest) :
    ∃ after, TypeExtension types after ∧
      Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨row,branchType,context,uses,environmentTyped,armsTyped,valid,variantTyped,restTyped⟩ :=
    stack_case_value typed.stack valueTyped arms environment rest stack
  obtain ⟨tag,address,rfl⟩ := variant_value_form variantTyped
  obtain ⟨valueRow,member,actual,fuel,lookup,assigned,path,normal⟩ := value_variant_fields variantTyped tag address rfl
  have rowsEq : valueRow.canonical = row.canonical := by
    have same := head_normalizes_unique normal (.direct (.variant row) rfl)
    simpa [Ty.canonical] using same
  obtain ⟨depth,armMember,armLookup,memberEq⟩ :=
    canonical_lookup_transport assumptions.bounds row valueRow rowsEq.symm fuel tag member lookup
  have armVisible := closed_lookup_finite (arms_row_closed armsTyped) armLookup
  cases found : arms.find? (fun arm => arm.1 == tag) with
  | none =>
      have absent := arms_typing_absent armsTyped found
      rw [absent] at armVisible
      cases armVisible
  | some arm =>
    obtain ⟨key,body⟩ := arm
    obtain ⟨_,payload,bodyUses,payloadLookup,bodyTyped,bodySafe,shareable⟩ := arms_typing_find armsTyped found
    have payloadEq : armMember = payload := Option.some.inj (armVisible.symm.trans payloadLookup)
    subst payloadEq
    have toPayload : ConversionPath assumptions actual armMember :=
      .step path (canonical_same_type assumptions member armMember memberEq.symm)
    let after := types ++ [armMember]
    have extension : TypeExtension types after := type_extension_append types [armMember]
    have addressAssigned : after[address]? = some actual := extension _ _ assigned
    have freshAssigned : after[state.heap.size]? = some armMember := by
      rw [← typed.heap.length]
      simp [after]
    let bindingContext : Context := [⟨actual,.affine⟩]
    have bindingSource : PartialTyping assumptions bindingContext (.bound 0) armMember (variableUses bindingContext 0) :=
      source_convert_path (PartialTyping.bound (context := bindingContext) (binding := ⟨actual,.affine⟩) rfl) toPayload
    have bindingSafe : safeUses bindingContext (variableUses bindingContext 0) = true := by
      simp [bindingContext,safeUses,variableUses,safeQuantity]
    have bindingValid : validContext assumptions.shareableVariables bindingContext = true := by
      simp [bindingContext,validContext]
    let binder : ClosureTyping assumptions after ⟨.bound 0,[address]⟩ armMember :=
      ⟨bindingContext,variableUses bindingContext 0,(EnvironmentTyping.empty after).cons addressAssigned,
        bindingSource,bindingSafe,bindingValid⟩
    have bodyValid : validContext assumptions.shareableVariables (⟨armMember,.unrestricted⟩ :: context) = true := by
      simp only [validContext,List.all_cons] at valid ⊢
      simp [shareable,valid]
    let next : ClosureTyping assumptions after ⟨body,state.heap.size :: environment⟩ branchType :=
      ⟨⟨armMember,.unrestricted⟩ :: context,bodyUses,(environmentTyped.weaken extension).cons freshAssigned,
        bodyTyped,bodySafe,bodyValid⟩
    refine ⟨after,extension,⟨step_alloc_certificate typed after branchType ?_ ?_ ?_⟩⟩
    · simpa [stepRaw,returned,stack,found,after] using
        heap_typed_push typed.heap (CellTyping.suspended binder (Ty.shareableUnder_not_computation _ _ shareable))
    · simpa [stepRaw,returned,stack,found] using ControlTyping.evaluate next
    · simpa [stepRaw,returned,stack,found] using StackTyping.weaken extension restTyped

theorem stack_ifBool_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ whenTrue whenFalse environment rest, stack = .ifBool whenTrue whenFalse environment :: rest →
      ∃ branchType, ∃ _trueOrigin : ClosureTyping assumptions types ⟨whenTrue,environment⟩ branchType,
        ∃ _falseOrigin : ClosureTyping assumptions types ⟨whenFalse,environment⟩ branchType,
        ValueTyping assumptions types value .boolean ∧ StackTyping assumptions types rest branchType result := by
  induction continuation with
  | nil type => intro whenTrue whenFalse environment rest impossible; simp at impossible
  | cons frame restTyped =>
      intro whenTrue whenFalse environment rest same
      cases same
      cases frame with
      | ifBool trueOrigin falseOrigin => exact ⟨_,trueOrigin,falseOrigin,valueTyped,restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro whenTrue whenFalse environment rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

/-- A typed returned Boolean selects exactly one branch, typed at the frame's
result; no wrongValue refusal is reachable. -/
theorem typed_ifBool_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {whenTrue whenFalse : Term}
    {environment : Environment} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .ifBool whenTrue whenFalse environment :: rest) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨branchType,trueOrigin,falseOrigin,booleanTyped,restTyped⟩ :=
    stack_ifBool_value typed.stack valueTyped whenTrue whenFalse environment rest stack
  obtain ⟨condition,rfl⟩ := boolean_value_form booleanTyped
  cases condition with
  | true =>
      refine ⟨step_certificate typed branchType ?_ ?_ ?_⟩
      · simpa [stepRaw,returned,stack] using typed.heap
      · simpa [stepRaw,returned,stack] using ControlTyping.evaluate trueOrigin
      · simpa [stepRaw,returned,stack] using restTyped
  | false =>
      refine ⟨step_certificate typed branchType ?_ ?_ ?_⟩
      · simpa [stepRaw,returned,stack] using typed.heap
      · simpa [stepRaw,returned,stack] using ControlTyping.evaluate falseOrigin
      · simpa [stepRaw,returned,stack] using restTyped

end Minidregg.Theory.ObjectiveBendDemandPreservation
