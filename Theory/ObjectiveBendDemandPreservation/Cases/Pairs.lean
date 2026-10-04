/- Preservation cases: Pairs. Imports only the shared Base; the dispatcher in
Theory/ObjectiveBendDemandPreservation.lean assembles every case module. -/
import Theory.ObjectiveBendDemandPreservation.Base
namespace Minidregg.Theory.ObjectiveBendDemandPreservation
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandTyping
set_option autoImplicit false

theorem stack_metadata_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ rest, stack = .metadata :: rest → ∃ metadataType extensionType,
      ValueTyping assumptions types value (.specification metadataType extensionType) ∧
      StackTyping assumptions types rest metadataType result := by
  induction continuation with
  | nil type => intro rest impossible; simp at impossible
  | cons frame restTyped =>
      intro rest same
      cases same
      cases frame with
      | metadata _ _ => exact ⟨_,_,valueTyped,restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

/-- Metadata projection enters the actual stored address representative and
carries its component conversion into the continuation. No address is retyped
and a law-bearing specification grants no native authority. -/
theorem typed_metadata_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value) (stack : state.stack = .metadata :: rest) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨metadataType,extensionType,specTyped,restTyped⟩ := stack_metadata_value typed.stack valueTyped rest stack
  obtain ⟨metadata,extension,rfl⟩ := specification_value_form specTyped
  obtain ⟨actualMetadata,actualExtension,metadataAssigned,extensionAssigned,normal⟩ :=
    value_specification_fields specTyped metadata extension rfl
  have same := head_normalizes_unique normal (.direct (.specification metadataType extensionType) rfl)
  have component : actualMetadata.canonical = metadataType.canonical := by
    simpa [Ty.canonical] using congrArg (fun type => match type with | .specification metadata _ => metadata | _ => type) same
  refine ⟨step_certificate typed actualMetadata ?_ ?_ ?_⟩
  · simpa [stepRaw,returned,stack] using typed.heap
  · simpa [stepRaw,returned,stack] using (ControlTyping.enter metadataAssigned)
  · simpa [stepRaw,returned,stack] using (StackTyping.conversion (canonical_same_type assumptions _ _ component) restTyped)

def projectionFrame (specification : Bool) : Frame := if specification then .reflect else .project

theorem stack_projection_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ specification rest, stack = projectionFrame specification :: rest → ∃ specType targetType,
      ValueTyping assumptions types value (.prototype specType targetType) ∧
      StackTyping assumptions types rest (if specification then specType else targetType) result := by
  induction continuation with
  | nil type => intro specification rest impossible; simp at impossible
  | cons frame restTyped =>
      intro specification rest same
      cases specification <;> simp only [projectionFrame,Bool.false_eq_true,if_false,if_true] at same
      · cases same
        cases frame with | project _ _ => exact ⟨_,_,valueTyped,restTyped⟩
      · cases same
        cases frame with | reflect _ _ => exact ⟨_,_,valueTyped,restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro specification rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases specification <;> simp [projectionFrame] at impossible

/-- Reflection and target projection preserve pointer identity and transport
component conversions to the continuation. The law/native-authority layer is
not part of this effect-free runtime typing judgment. -/
theorem typed_prototype_projection_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {rest : List Frame}
    (typed : StateTyping assumptions types state result) (specification : Bool)
    (returned : state.control = .returned value)
    (stack : state.stack = projectionFrame specification :: rest) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control; rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨specType,targetType,protoTyped,restTyped⟩ := stack_projection_value typed.stack valueTyped specification rest stack
  obtain ⟨spec,target,rfl⟩ := prototype_value_form protoTyped
  obtain ⟨actualSpec,actualTarget,specAssigned,targetAssigned,normal⟩ := value_prototype_fields protoTyped spec target rfl
  have same := head_normalizes_unique normal (.direct (.prototype specType targetType) rfl)
  have specComponent : actualSpec.canonical = specType.canonical := by
    simpa [Ty.canonical] using congrArg (fun type => match type with | .prototype spec _ => spec | _ => type) same
  have targetComponent : actualTarget.canonical = targetType.canonical := by
    simpa [Ty.canonical] using congrArg (fun type => match type with | .prototype _ target => target | _ => type) same
  cases specification
  · refine ⟨step_certificate typed actualTarget ?_ ?_ ?_⟩
    · simpa [stepRaw,returned,stack,projectionFrame] using typed.heap
    · simpa [stepRaw,returned,stack,projectionFrame] using (ControlTyping.enter targetAssigned)
    · simpa [stepRaw,returned,stack,projectionFrame] using
        (StackTyping.conversion (canonical_same_type assumptions _ _ targetComponent) restTyped)
  · refine ⟨step_certificate typed actualSpec ?_ ?_ ?_⟩
    · simpa [stepRaw,returned,stack,projectionFrame] using typed.heap
    · simpa [stepRaw,returned,stack,projectionFrame] using (ControlTyping.enter specAssigned)
    · simpa [stepRaw,returned,stack,projectionFrame] using
        (StackTyping.conversion (canonical_same_type assumptions _ _ specComponent) restTyped)

def pairedTerm (specification : Bool) (left right : Term) : Term :=
  if specification then .specification left right else .prototype left right

def pairedType (specification : Bool) (left right : Ty) : Ty :=
  if specification then .specification left right else .prototype left right

def PairDerivation (assumptions : Assumptions) (context : Context)
    (kind : Bool) (left right : Term) (type : Ty) (uses : Uses) : Prop :=
  ∃ leftType rightType lu ru,
    PartialTyping assumptions context left leftType lu ∧
    PartialTyping assumptions context right rightType ru ∧
    uses = addUses lu ru ∧ ConversionPath assumptions (pairedType kind leftType rightType) type

theorem source_pair_decomposition {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .specification left right => PairDerivation assumptions context true left right type uses
    | .prototype left right => PairDerivation assumptions context false left right type uses
    | _ => True := by
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .specification left right => PairDerivation assumptions context true left right type uses
      | .prototype left right => PairDerivation assumptions context false left right type uses
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
    all_goals
      obtain ⟨lt,rt,lu,ru,leftTyped,rightTyped,counts,path⟩ := ih
      exact ⟨lt,rt,lu,ru,leftTyped,rightTyped,counts,.step path agreement⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro context metadata extension metadataType extensionType mu eu metadataTyped extensionTyped _ _ ihMetadata ihExtension
    exact ⟨metadataType,extensionType,mu,eu,metadataTyped,extensionTyped,rfl,.refl _⟩
  · intro context spec target specType targetType su tu specTyped targetTyped _ _ ihSpec ihTarget
    exact ⟨specType,targetType,su,tu,specTyped,targetTyped,rfl,.refl _⟩
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

/-- The pair decomposition with its component types' suspendability (each
component becomes a shared cell). -/
def PairPureDerivation (assumptions : Assumptions) (context : Context)
    (kind : Bool) (left right : Term) (type : Ty) (uses : Uses) : Prop :=
  ∃ leftType rightType lu ru,
    PartialTyping assumptions context left leftType lu ∧
    PartialTyping assumptions context right rightType ru ∧
    leftType.isComputation = false ∧ rightType.isComputation = false ∧
    uses = addUses lu ru ∧ ConversionPath assumptions (pairedType kind leftType rightType) type

theorem source_pair_decomposition_pure {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .specification left right => PairPureDerivation assumptions context true left right type uses
    | .prototype left right => PairPureDerivation assumptions context false left right type uses
    | _ => True := by
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .specification left right => PairPureDerivation assumptions context true left right type uses
      | .prototype left right => PairPureDerivation assumptions context false left right type uses
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
    all_goals
      obtain ⟨lt,rt,lu,ru,leftTyped,rightTyped,lp,rp,counts,path⟩ := ih
      exact ⟨lt,rt,lu,ru,leftTyped,rightTyped,lp,rp,counts,.step path agreement⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro context metadata extension metadataType extensionType mu eu metadataTyped extensionTyped mp ep ihMetadata ihExtension
    exact ⟨metadataType,extensionType,mu,eu,metadataTyped,extensionTyped,mp,ep,rfl,.refl _⟩
  · intro context spec target specType targetType su tu specTyped targetTyped sp tp ihSpec ihTarget
    exact ⟨specType,targetType,su,tu,specTyped,targetTyped,sp,tp,rfl,.refl _⟩
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

/-- Specification and prototype allocation keep both authored source origins,
their independently typed pointers, and all prior heap identities. -/
theorem typed_pair_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {left right : Term} {environment : Environment}
    (typed : StateTyping assumptions types state result) (kind : Bool)
    (evaluate : state.control = .evaluate (pairedTerm kind left right) environment) :
    ∃ after, TypeExtension types after ∧
      Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    have decomposition : PairPureDerivation assumptions origin.context kind left right typed.current origin.uses := by
      cases kind <;> exact source_pair_decomposition_pure origin.source
    obtain ⟨leftType,rightType,lu,ru,leftTyped,rightTyped,leftPure,rightPure,counts,path⟩ := decomposition
    have safe : safeUses origin.context (addUses lu ru) = true := by simpa [counts] using origin.safe
    have leftSafe := safe_add_uses_left origin.context lu ru (source_uses_length leftTyped) (source_uses_length rightTyped) safe
    have rightSafe := safe_add_uses_right origin.context lu ru (source_uses_length leftTyped) (source_uses_length rightTyped) safe
    let middle := types ++ [leftType]
    let after := middle ++ [rightType]
    have firstExtension : TypeExtension types middle := type_extension_append types [leftType]
    have secondExtension : TypeExtension middle after := type_extension_append middle [rightType]
    have extension := type_extension_trans firstExtension secondExtension
    let leftOrigin : ClosureTyping assumptions middle ⟨left,environment⟩ leftType :=
      ⟨origin.context,lu,origin.environment.weaken firstExtension,leftTyped,leftSafe,origin.contextValid⟩
    let rightOrigin : ClosureTyping assumptions after ⟨right,environment⟩ rightType :=
      ⟨origin.context,ru,origin.environment.weaken extension,rightTyped,rightSafe,origin.contextValid⟩
    have heap := heap_typed_push (heap_typed_push typed.heap (CellTyping.suspended leftOrigin leftPure)) (CellTyping.suspended rightOrigin rightPure)
    have leftAssigned : after[state.heap.size]? = some leftType := by
      apply secondExtension
      rw [← typed.heap.length]
      simp [middle]
    have rightAssigned : after[state.heap.size+1]? = some rightType := by
      rw [← typed.heap.length]
      simp [after,middle,List.length_append]
    have value : ValueTyping assumptions after
        (if kind then .specification state.heap.size (state.heap.size+1) else .prototype state.heap.size (state.heap.size+1))
        (pairedType kind leftType rightType) := by
      cases kind
      · exact .prototype leftAssigned rightAssigned
      · exact .specification leftAssigned rightAssigned
    refine ⟨after,extension,⟨step_alloc_certificate typed after (pairedType kind leftType rightType) ?_ ?_ ?_⟩⟩
    · cases kind <;> simpa [stepRaw,evaluate,pairedTerm,after,middle] using heap
    · cases kind <;> simpa [stepRaw,evaluate,pairedTerm] using ControlTyping.returned value
    · cases kind <;> simpa [stepRaw,evaluate,pairedTerm] using
        StackTyping.weaken extension (stack_convert_path path typed.stack)

end Minidregg.Theory.ObjectiveBendDemandPreservation
