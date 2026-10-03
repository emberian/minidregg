/- Typed graph representation for the frozen effect-free Objective demand core.
This module carries actual source derivations and captured quantity premises.
It does not turn static use counts into a native custody/liveness theorem. -/
import Theory.ObjectiveBendTyping
import Theory.ObjectiveBendDemandInvariant
namespace Minidregg.Theory.ObjectiveBendDemandTyping
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendOpenRecursion ObjectiveBendDemandMachine
set_option autoImplicit false

abbrev AddressTypes := List Ty

/-- Allocation extends this immutable assignment; updating a cell cannot
reassign the type of an existing thunk identity. -/
def TypeExtension (before after : AddressTypes) : Prop :=
  ∀ (address : Address) (type : Ty), before[address]? = some type → after[address]? = some type

theorem type_extension_refl (types : AddressTypes) : TypeExtension types types := by
  intro _ _ typed; exact typed

theorem type_extension_trans {first second third : AddressTypes}
    (one : TypeExtension first second) (two : TypeExtension second third) :
    TypeExtension first third := by
  intro address type typed; exact two address type (one address type typed)

/-- Quantities remain on every captured binding; the environment stores address
identity, and the typing evidence connects each slot to that address's type. -/
structure EnvironmentTyping (types : AddressTypes) (context : Context) (environment : Environment) : Prop where
  length : environment.length = context.length
  binding : ∀ (index : Nat) (declared : Binding), context[index]? = some declared →
    ∃ address, environment[index]? = some address ∧ types[address]? = some declared.type

theorem EnvironmentTyping.empty (types : AddressTypes) : EnvironmentTyping types [] [] :=
  ⟨rfl, by intro index declared absent; simp at absent⟩

theorem EnvironmentTyping.weaken {before after : AddressTypes} {context : Context} {environment : Environment}
    (extension : TypeExtension before after) (typed : EnvironmentTyping before context environment) :
    EnvironmentTyping after context environment := by
  refine ⟨typed.length, ?_⟩
  intro index declared lookup
  obtain ⟨address,member,assigned⟩ := typed.binding index declared lookup
  exact ⟨address,member,extension address declared.type assigned⟩

theorem EnvironmentTyping.cons {types : AddressTypes} {context : Context} {environment : Environment}
    {address : Address} {binding : Binding}
    (typed : EnvironmentTyping types context environment)
    (assigned : types[address]? = some binding.type) :
    EnvironmentTyping types (binding :: context) (address :: environment) := by
  refine ⟨by simp [typed.length], ?_⟩
  intro index declared lookup
  cases index with
  | zero =>
    simp only [List.getElem?_cons_zero] at lookup
    cases lookup
    exact ⟨address,rfl,assigned⟩
  | succ index =>
    simp only [List.getElem?_cons_succ] at lookup
    obtain ⟨prior,member,priorAssigned⟩ := typed.binding index declared lookup
    exact ⟨prior,by simpa using member,priorAssigned⟩

structure ClosureTyping (assumptions : Assumptions) (types : AddressTypes) (closure : Closure) (type : Ty) where
  context : Context
  uses : Uses
  environment : EnvironmentTyping types context closure.environment
  source : PartialTyping assumptions context closure.term type uses
  safe : safeUses context uses = true
  contextValid : validContext assumptions.shareableVariables context = true

/-- The static capture proof and physical address environment travel together.
An immutable runtime closure has no hidden exemption for affine captures. -/
inductive ValueTyping (assumptions : Assumptions) (types : AddressTypes) : RuntimeValue → Ty → Prop where
  | natural (value : Nat) : ValueTyping assumptions types (.natural value) .natural
  | boolean (value : Bool) : ValueTyping assumptions types (.boolean value) .boolean
  | label (value : String) : ValueTyping assumptions types (.label value) (literalType value)
  | closure {body : Term} {environment : Environment} {context : Context}
      {annotation : LambdaAnnotation} {uses : Uses} :
      EnvironmentTyping types context environment →
      PartialTyping assumptions (⟨annotation.domain,annotation.parameter⟩ :: context) body annotation.codomain uses →
      safeUses (⟨annotation.domain,annotation.parameter⟩ :: context) uses = true →
      validContext assumptions.shareableVariables (⟨annotation.domain,annotation.parameter⟩ :: context) = true →
      reusableAllowed assumptions annotation.reuse context uses.tail = true →
      ValueTyping assumptions types (.closure body environment)
        (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain)
  | record {fields : List (String × Address)} {row : Ty} :
      (∃ fuel, row.isRow assumptions.bounds fuel = true) →
      (∀ (fuel : Nat) (name : String) (member : Ty), row.lookup assumptions.bounds fuel name = some member →
        ∃ address, fields.find? (fun field => field.1 == name) = some (name,address) ∧
          types[address]? = some member) →
      ValueTyping assumptions types (.record fields) row
  | specification {metadata extension : Address} {metadataType extensionType : Ty} :
      types[metadata]? = some metadataType → types[extension]? = some extensionType →
      ValueTyping assumptions types (.specification metadata extension) (.specification metadataType extensionType)
  | prototype {spec target : Address} {specType targetType : Ty} :
      types[spec]? = some specType → types[target]? = some targetType →
      ValueTyping assumptions types (.prototype spec target) (.prototype specType targetType)
  | conversion {value : RuntimeValue} {actual expected : Ty} :
      ValueTyping assumptions types value actual → sameType assumptions actual expected = true →
      ValueTyping assumptions types value expected

/-- Both origin and cached result inhabit the same assigned type. Cycles use
address assignments; the relation never unfolds a cyclic heap into a tree. -/
inductive CellTyping (assumptions : Assumptions) (types : AddressTypes) : Cell → Ty → Prop where
  | suspended {origin : Closure} {type : Ty} : ClosureTyping assumptions types origin type →
      CellTyping assumptions types (.suspended origin) type
  | evaluating {origin : Closure} {type : Ty} : ClosureTyping assumptions types origin type →
      CellTyping assumptions types (.evaluating origin) type
  | cached {origin : Closure} {value : RuntimeValue} {type : Ty} :
      ClosureTyping assumptions types origin type → ValueTyping assumptions types value type →
      CellTyping assumptions types (.cached origin value) type

structure HeapTyping (assumptions : Assumptions) (types : AddressTypes) (heap : Array Cell) : Prop where
  length : types.length = heap.size
  cell : ∀ (address : Address) (type : Ty), types[address]? = some type →
    ∃ stored, heap[address]? = some stored ∧ CellTyping assumptions types stored type

/-- Continuations describe their consumed and produced types. Update-frame
activity itself is separately enforced by the qualified BusyInvariant. -/
inductive FrameTyping (assumptions : Assumptions) (types : AddressTypes) : Frame → Ty → Ty → Prop where
  | argument {argument : Term} {environment : Environment} {functionType domain codomain : Ty}
      {reuse : Reuse} {quantity : Quantity} :
      (argumentTyped : ClosureTyping assumptions types ⟨argument,environment⟩ domain) →
      callable functionType = .arrow reuse quantity domain codomain →
      argumentAllowed assumptions quantity argumentTyped.context domain argumentTyped.uses = true →
      FrameTyping assumptions types (.argument argument environment) functionType codomain
  | update {address : Address} {type : Ty} : types[address]? = some type →
      FrameTyping assumptions types (.update address) type type
  | field {name : String} {row member : Ty} {fuel : Nat} :
      row.lookup assumptions.bounds fuel name = some member →
      FrameTyping assumptions types (.field name) row member
  | reflect (specType targetType : Ty) :
      FrameTyping assumptions types .reflect (.prototype specType targetType) specType
  | metadata (metadataType extensionType : Ty) :
      FrameTyping assumptions types .metadata (.specification metadataType extensionType) metadataType
  | project (specType targetType : Ty) :
      FrameTyping assumptions types .project (.prototype specType targetType) targetType
  | extend {fields : List (String × Term)} {environment : Environment} {row inherited : Ty}
      {context : Context} {uses : Uses} :
      EnvironmentTyping types context environment →
      FieldsTyping assumptions context fields row uses → safeUses context uses = true →
      validContext assumptions.shareableVariables context = true →
      inherited.isRow assumptions.bounds 64 = true →
      FrameTyping assumptions types (.extend fields environment) inherited (overlay row inherited)
  | condition {zero successor : Term} {environment : Environment} {result : Ty}
      {context : Context} {uses : Uses} :
      ClosureTyping assumptions types ⟨zero,environment⟩ result →
      EnvironmentTyping types context environment →
      PartialTyping assumptions (⟨.natural,.unrestricted⟩ :: context) successor result uses →
      safeUses (⟨.natural,.unrestricted⟩ :: context) uses = true →
      validContext assumptions.shareableVariables context = true →
      FrameTyping assumptions types (.condition zero successor environment) .natural result
  | binaryLeft {primitive : Primitive} {right : Term} {environment : Environment} :
      ClosureTyping assumptions types ⟨right,environment⟩ (primitiveTypes primitive).1 →
      FrameTyping assumptions types (.binaryLeft primitive right environment)
        (primitiveTypes primitive).1 (primitiveTypes primitive).2
  | binaryRight {primitive : Primitive} {left : RuntimeValue} :
      ValueTyping assumptions types left (primitiveTypes primitive).1 →
      FrameTyping assumptions types (.binaryRight primitive left)
        (primitiveTypes primitive).1 (primitiveTypes primitive).2

inductive StackTyping (assumptions : Assumptions) (types : AddressTypes) : List Frame → Ty → Ty → Prop where
  | nil (type : Ty) : StackTyping assumptions types [] type type
  | cons {frame : Frame} {rest : List Frame} {input middle result : Ty} :
      FrameTyping assumptions types frame input middle → StackTyping assumptions types rest middle result →
      StackTyping assumptions types (frame :: rest) input result
  | conversion {stack : List Frame} {actual expected result : Ty} :
      sameType assumptions actual expected = true → StackTyping assumptions types stack expected result →
      StackTyping assumptions types stack actual result

/-- A source conversion is an implicit continuation boundary. It changes
neither runtime frames nor address types; returned values cross it using the
same proof-producing finite type agreement as source derivations. -/
-- The conversion constructor belongs to StackTyping above.

inductive ControlTyping (assumptions : Assumptions) (types : AddressTypes) : Control → Ty → Prop where
  | evaluate {term : Term} {environment : Environment} {type : Ty} :
      ClosureTyping assumptions types ⟨term,environment⟩ type →
      ControlTyping assumptions types (.evaluate term environment) type
  | enter {address : Address} {type : Ty} : types[address]? = some type →
      ControlTyping assumptions types (.enter address) type
  | returned {value : RuntimeValue} {type : Ty} : ValueTyping assumptions types value type →
      ControlTyping assumptions types (.returned value) type
  | complete {value : RuntimeValue} {type : Ty} : ValueTyping assumptions types value type →
      ControlTyping assumptions types (.complete value) type
  | blackhole {address : Address} {type : Ty} : types[address]? = some type →
      ControlTyping assumptions types (.blackhole address) type

structure StateTyping (assumptions : Assumptions) (types : AddressTypes) (state : State) (result : Ty) where
  current : Ty
  heap : HeapTyping assumptions types state.heap
  control : ControlTyping assumptions types state.control current
  stack : StackTyping assumptions types state.stack current result
  assumptionsValid : assumptions.valid = true
  /-- Imported representation obligations exclude forged update frames/cells. -/
  lexical : ObjectiveBendDemandInvariant.LexicalInvariant state
  busy : ObjectiveBendDemandInvariant.BusyInvariant state
  terminalStack : ObjectiveBendDemandInvariant.FinalStackInvariant state

/-- Typing always accounts for every lexical slot, so zip-based combination
cannot truncate an affine use hidden in a shorter vector. -/
theorem source_uses_length {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping assumptions context term type uses) : uses.length = context.length := by
  refine PartialTyping.rec
    (motive_1 := fun context _ _ uses _ => uses.length = context.length)
    (motive_2 := fun context _ _ uses _ => uses.length = context.length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intros; simp [variableUses]
  · intros; simp [zeroUses]
  · intros; simp [zeroUses]
  · intros; simp [zeroUses]
  · intros; rename_i ih; simpa using congrArg (fun n => n-1) ih
  · intros; assumption
  · intros; simp_all [addUses,List.length_zipWith]
  · intros; assumption
  · intros; assumption
  · intros; simp_all [addUses,List.length_zipWith]
  · intros; simp_all [addUses,List.length_zipWith]
  · intros; simp_all [addUses,List.length_zipWith]
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; simp_all [addUses,List.length_zipWith]
  · intros; simp_all [addUses,List.length_zipWith]
  · intros; simp_all [addUses,List.length_zipWith]
  · intros; simp_all [addUses,List.length_zipWith]
  · intros; simp [zeroUses]
  · intros; simp_all [addUses,List.length_zipWith]

/-- Finite authored record rows are rows at some adequate probe depth.
The graph value relation therefore imposes no arbitrary 64-member ceiling. -/
theorem source_fields_row {assumptions : Assumptions} {context : Context}
    {fields : List (String × Term)} {row : Ty} {uses : Uses}
    (typed : FieldsTyping assumptions context fields row uses) :
    ∃ fuel, row.isRow assumptions.bounds fuel = true := by
  refine FieldsTyping.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ row _ _ => ∃ fuel, row.isRow assumptions.bounds fuel = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
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
  · intro context; exact ⟨1,rfl⟩
  · intro context name body rest type row bu ru hb hr ihBody ihRest
    obtain ⟨fuel,isRow⟩ := ihRest
    exact ⟨fuel+1,isRow⟩

/-- Every actual source derivation is lexically scoped. This connects checker
success to the independently proved graph reference/busy invariants. -/
theorem source_scoped {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping assumptions context term type uses) :
    ObjectiveBendDemandInvariant.Scoped context.length term := by
  refine PartialTyping.rec
    (motive_1 := fun context term _ _ _ => ObjectiveBendDemandInvariant.Scoped context.length term)
    (motive_2 := fun context fields _ _ _ => ∀ field ∈ fields, ObjectiveBendDemandInvariant.Scoped context.length field.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed

  · intro context index binding found
    exact .bound (List.getElem?_eq_some_iff.mp found).1
  · intro context value; exact .natural value
  · intro context value; exact .boolean value
  · intro context value; exact .label value
  · intros; rename_i ih
    exact .lam (by simpa using ih)
  · intros; assumption
  · intros; exact .app (by assumption) (by assumption)
  · intros; exact .record (by assumption)
  · intros; exact .get (by assumption)
  · intros; exact .extend (by assumption) (by assumption)
  · intros; exact .specification (by assumption) (by assumption)
  · intros; exact .prototype (by assumption) (by assumption)
  · intros; exact .reflect (by assumption)
  · intros; exact .metadata (by assumption)
  · intros; exact .project (by assumption)
  · intros; exact .mix (by assumption) (by assumption)
  · intros; exact .fix (by assumption) (by assumption)
  · intros; exact .binary (by assumption) (by assumption)
  · intros; rename_i ihValue ihZero ihSuccessor
    exact .condition ihValue ihZero (by simpa using ihSuccessor)
  · intro context field member; simp at member
  · intro context name body rest type row bu ru hb hr ihb ihr field member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ihb
    · exact ihr field member

theorem source_fields_scoped {assumptions : Assumptions} {context : Context}
    {fields : List (String × Term)} {type : Ty} {uses : Uses}
    (typed : FieldsTyping assumptions context fields type uses) :
    ∀ field ∈ fields, ObjectiveBendDemandInvariant.Scoped context.length field.2 := by
  refine FieldsTyping.rec
    (motive_1 := fun context term _ _ _ => ObjectiveBendDemandInvariant.Scoped context.length term)
    (motive_2 := fun context fields _ _ _ => ∀ field ∈ fields, ObjectiveBendDemandInvariant.Scoped context.length field.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed

  · intro context index binding found
    exact .bound (List.getElem?_eq_some_iff.mp found).1
  · intro context value; exact .natural value
  · intro context value; exact .boolean value
  · intro context value; exact .label value
  · intros; rename_i ih
    exact .lam (by simpa using ih)
  · intros; assumption
  · intros; exact .app (by assumption) (by assumption)
  · intros; exact .record (by assumption)
  · intros; exact .get (by assumption)
  · intros; exact .extend (by assumption) (by assumption)
  · intros; exact .specification (by assumption) (by assumption)
  · intros; exact .prototype (by assumption) (by assumption)
  · intros; exact .reflect (by assumption)
  · intros; exact .metadata (by assumption)
  · intros; exact .project (by assumption)
  · intros; exact .mix (by assumption) (by assumption)
  · intros; exact .fix (by assumption) (by assumption)
  · intros; exact .binary (by assumption) (by assumption)
  · intros; rename_i ihValue ihZero ihSuccessor
    exact .condition ihValue ihZero (by simpa using ihSuccessor)
  · intro context field member; simp at member
  · intro context name body rest type row bu ru hb hr ihb ihr field member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ihb
    · exact ihr field member

/-- A successful closed checker result initializes the genuine typed graph;
no extra scope oracle or termination premise is required. -/
def checked_initial_state (source : AnnotatedTerm) (checked : Checked source []) :
    StateTyping source.assumptions [] (initial source.erase) checked.type where
  current := checked.type
  heap := ⟨rfl,by intro address type absent; simp at absent⟩
  control := .evaluate ⟨[],checked.uses,EnvironmentTyping.empty [],checked.derivation,checked.safe,checked.contextValid⟩
  stack := .nil checked.type
  assumptionsValid := checked.assumptionsValid
  lexical := ObjectiveBendDemandInvariant.initial_lexicalInvariant (source_scoped checked.derivation)
  busy := ObjectiveBendDemandInvariant.initial_busyInvariant source.erase
  terminalStack := ObjectiveBendDemandInvariant.initial_finalStackInvariant source.erase


end Minidregg.Theory.ObjectiveBendDemandTyping
