/- Preservation lemmas over the frozen demand graph and actual source typing.
All-constructor preservation connects the checker derivation to every actual
raw transition; termination, liveness and native authority are separate. -/
import Theory.ObjectiveBendDemandTyping
import Theory.ObjectiveBendDemandAdequacy
import Theory.AxiomPin
namespace Minidregg.Theory.ObjectiveBendDemandPreservation
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandTyping
set_option autoImplicit false

def ClosureTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {closure : Closure} {type : Ty} (extension : TypeExtension before after)
    (typed : ObjectiveBendDemandTyping.ClosureTyping assumptions before closure type) :
    ObjectiveBendDemandTyping.ClosureTyping assumptions after closure type :=
  ⟨typed.context,typed.uses,typed.environment.weaken extension,typed.source,typed.safe,typed.contextValid⟩

theorem ValueTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {value : RuntimeValue} {type : Ty} (extension : TypeExtension before after)
    (typed : ValueTyping assumptions before value type) : ValueTyping assumptions after value type := by
  induction typed with
  | natural value => exact .natural value
  | boolean value => exact .boolean value
  | label value => exact .label value
  | closure environment body safe valid captures =>
      exact .closure (environment.weaken extension) body safe valid captures
  | record row members =>
      refine .record row ?_
      intro fuel name member lookup
      obtain ⟨address,actual,found,assigned,path⟩ := members fuel name member lookup
      exact ⟨address,actual,found,extension address actual assigned,path⟩
  | specification metadata ext => exact .specification (extension _ _ metadata) (extension _ _ ext)
  | prototype spec target => exact .prototype (extension _ _ spec) (extension _ _ target)
  | conversion prior agreement ih => exact .conversion ih agreement
  | variant lookup assigned path => exact .variant lookup (extension _ _ assigned) path

theorem CellTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {cell : Cell} {type : Ty} (extension : TypeExtension before after)
    (typed : CellTyping assumptions before cell type) : CellTyping assumptions after cell type := by
  cases typed with
  | suspended origin pure => exact .suspended (ClosureTyping.weaken extension origin) pure
  | evaluating origin pure => exact .evaluating (ClosureTyping.weaken extension origin) pure
  | cached origin value pure =>
      exact .cached (ClosureTyping.weaken extension origin) (ValueTyping.weaken extension value) pure

theorem FrameTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {frame : Frame} {input output : Ty} (extension : TypeExtension before after)
    (typed : FrameTyping assumptions before frame input output) :
    FrameTyping assumptions after frame input output := by
  cases typed with
  | argument argument callable copyAllowed => exact .argument (ClosureTyping.weaken extension argument) callable copyAllowed
  | update assigned pure => exact .update (extension _ _ assigned) pure
  | field found => exact .field found
  | reflect => exact .reflect _ _
  | metadata => exact .metadata _ _
  | project => exact .project _ _
  | extend environment fields safe valid row => exact .extend (environment.weaken extension) fields safe valid row
  | condition zero environment successor safe valid =>
      exact .condition (ClosureTyping.weaken extension zero) (environment.weaken extension) successor safe valid
  | binaryLeft right => exact .binaryLeft (ClosureTyping.weaken extension right)
  | binaryRight left => exact .binaryRight (ValueTyping.weaken extension left)
  | case environment arms valid => exact .case (environment.weaken extension) arms valid
  | ifBool whenTrue whenFalse =>
      exact .ifBool (ClosureTyping.weaken extension whenTrue) (ClosureTyping.weaken extension whenFalse)
  | effectCase environment arms valid pure => exact .effectCase (environment.weaken extension) arms valid pure

theorem StackTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {stack : List Frame} {input output : Ty} (extension : TypeExtension before after)
    (typed : StackTyping assumptions before stack input output) :
    StackTyping assumptions after stack input output := by
  induction typed with
  | nil type => exact .nil type
  | cons frame rest ih => exact .cons (FrameTyping.weaken extension frame) ih
  | conversion agreement rest ih => exact .conversion agreement ih
  | returns pure rest ih => exact .returns pure ih

theorem ControlTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {control : Control} {type : Ty} (extension : TypeExtension before after)
    (typed : ControlTyping assumptions before control type) :
    ControlTyping assumptions after control type := by
  cases typed with
  | evaluate closure => exact .evaluate (ClosureTyping.weaken extension closure)
  | enter assigned => exact .enter (extension _ _ assigned)
  | returned value => exact .returned (ValueTyping.weaken extension value)
  | complete value => exact .complete (ValueTyping.weaken extension value)
  | blackhole assigned => exact .blackhole (extension _ _ assigned)
  | yielded assigned plan response => exact .yielded (extension _ _ assigned) plan response

/-- Address identity is conserved through arbitrary allocation extensions. -/
theorem type_extension_append (before additions : AddressTypes) :
    TypeExtension before (before ++ additions) := by
  intro address type assigned
  have bound : address < before.length := (List.getElem?_eq_some_iff.mp assigned).1
  simpa [List.getElem?_append,bound] using assigned


/-! ## Activities in the typed graph -/

/-- No heap cell is an activity (CellTyping carries it). -/
theorem heap_type_pure {assumptions : Assumptions} {types : AddressTypes} {heap : Array Cell}
    (heapTyped : HeapTyping assumptions types heap) {address : Address} {type : Ty}
    (assigned : types[address]? = some type) : type.isComputation = false := by
  obtain ⟨cell,_,cellTyped⟩ := heapTyped.cell address type assigned
  cases cellTyped <;> assumption

theorem conversionPath_isComputation {assumptions : Assumptions} {first last : Ty}
    (path : ConversionPath assumptions first last) : first.isComputation = last.isComputation := by
  induction path with
  | refl => rfl
  | step prior agreement ih => exact ih.trans (sameType_isComputation agreement)

theorem lookup_not_computation (bounds : Bounds) (fuel : Nat) (row : Ty) (name : String) (member : Ty)
    (lookup : row.lookup bounds fuel name = some member) : row.isComputation = false := by
  cases fuel <;> cases row <;> simp_all [Ty.lookup,Ty.isComputation]

theorem isRow_not_computation (bounds : Bounds) (fuel : Nat) (row : Ty)
    (isRow : row.isRow bounds fuel = true) : row.isComputation = false := by
  cases fuel <;> cases row <;> simp_all [Ty.isRow,Ty.isComputation]

theorem callable_arrow_not_computation {type : Ty} {reuse : Reuse} {quantity : Quantity} {domain codomain : Ty}
    (callable : callable type = .arrow reuse quantity domain codomain) : type.isComputation = false := by
  cases type <;> simp_all [ObjectiveBendTyping.callable,Ty.isComputation]

theorem sameType_activity_canonical {assumptions : Assumptions} {actual expected plan response produced : Ty}
    (agreement : sameType assumptions actual expected = true)
    (equal : actual.canonical = (Ty.computation plan response produced).canonical) :
    expected.canonical = (Ty.computation plan response produced).canonical := by
  have activity : actual.isComputation = true := by
    rw [← Ty.canonical_isComputation,equal]; rfl
  simp only [sameType,Bool.or_eq_true] at agreement
  rcases agreement with (canonical | aliasActual) | aliasExpected
  · rw [← equal]; exact (by simpa using canonical : actual.canonical = expected.canonical).symm
  · cases actual <;> simp_all [Ty.isComputation]
  · cases expected <;> simp at aliasExpected
    simp_all [Ty.isComputation]

theorem argumentAllowed_not_computation {assumptions : Assumptions} {quantity : Quantity}
    {context : Context} {type : Ty} {uses : Uses}
    (allowed : argumentAllowed assumptions quantity context type uses = true) : type.isComputation = false := by
  simp only [argumentAllowed,Bool.and_eq_true] at allowed
  simpa using allowed.1

/-- An activity-typed continuation begins with an effect case: no other frame,
and in particular no update frame (a shared cell being forced), accepts one. -/
theorem stack_activity_head {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty}
    (typed : StackTyping assumptions types stack input result) :
    input.isComputation = true →
    ∀ frame rest, stack = frame :: rest → ∃ arms environment, frame = .case arms environment := by
  induction typed with
  | nil => intro _ frame rest impossible; simp at impossible
  | cons frameTyped restTyped ih =>
      intro activity frame rest same
      cases same
      cases frameTyped with
      | argument argument callable copy =>
          simp [callable_arrow_not_computation callable] at activity
      | update assigned pure => simp_all
      | field lookup => simp [lookup_not_computation _ _ _ _ _ lookup] at activity
      | extend _ _ _ _ isRow => simp [isRow_not_computation _ _ _ isRow] at activity
      | binaryLeft right => rename_i primitive _ _; cases primitive <;> simp_all [primitiveTypes,Ty.isComputation]
      | binaryRight left => rename_i primitive _; cases primitive <;> simp_all [primitiveTypes,Ty.isComputation]
      | effectCase => exact ⟨_,_,rfl⟩
      | case => exact ⟨_,_,rfl⟩
      | _ => simp_all [Ty.isComputation]
  | conversion agreement restTyped ih =>
      intro activity; exact ih ((sameType_isComputation agreement) ▸ activity)
  | returns pure restTyped ih => intro activity; simp_all

theorem computation_canonical_inj {plan response result plan' response' result' : Ty}
    (equal : (Ty.computation plan response result).canonical = (Ty.computation plan' response' result').canonical) :
    plan.canonical = plan'.canonical ∧ response.canonical = response'.canonical ∧ result.canonical = result'.canonical := by
  simp only [Ty.canonical,Ty.computation.injEq] at equal
  exact equal

/-- Inversion of an activity continuation at an effect case: the arms are
activities over the case's own Plan/Response, and the incoming activity
produces the case's sum. -/
theorem stack_effect_case {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty}
    (typed : StackTyping assumptions types stack input result) :
    ∀ arms environment rest plan response produced, stack = .case arms environment :: rest →
      input.canonical = (Ty.computation plan response produced).canonical →
      ∃ row planType responseType branch context uses,
        EnvironmentTyping types context environment ∧
        ArmsTyping assumptions context arms row (.computation planType responseType branch) uses ∧
        validContext assumptions.shareableVariables context = true ∧
        produced.canonical = (Ty.variant row).canonical ∧
        StackTyping assumptions types rest (.computation planType responseType branch) result := by
  induction typed with
  | nil => intro arms environment rest plan response produced impossible; simp at impossible
  | cons frameTyped restTyped ih =>
      intro arms environment rest plan response produced same equal
      cases same
      cases frameTyped with
      | case environmentTyped armsTyped valid =>
          simp [Ty.canonical] at equal
      | effectCase environmentTyped armsTyped valid pure =>
          obtain ⟨_,_,component⟩ := computation_canonical_inj equal
          exact ⟨_,_,_,_,_,_,environmentTyped,armsTyped,valid,component.symm,restTyped⟩
  | conversion agreement restTyped ih =>
      intro arms environment rest plan response produced same equal
      exact ih arms environment rest plan response produced same (sameType_activity_canonical agreement equal)
  | returns pure restTyped ih =>
      intro arms environment rest plan response produced same equal
      rw [← Ty.canonical_isComputation,equal] at pure
      simp [Ty.canonical,Ty.isComputation] at pure

/-- A cache update preserves every assigned address type and every retained
origin's source/capture evidence; it changes no address assignment. -/
theorem heap_typed_set {assumptions : Assumptions} {types : AddressTypes}
    {heap : Array Cell} {address : Address} {type : Ty} {replacement : Cell}
    (heapTyped : HeapTyping assumptions types heap) (assigned : types[address]? = some type)
    (replacementTyped : CellTyping assumptions types replacement type) :
    HeapTyping assumptions types (heap.set! address replacement) := by
  have bound : address < heap.size := by
    rw [← heapTyped.length]
    exact (List.getElem?_eq_some_iff.mp assigned).1
  refine ⟨by simpa [Array.set!] using heapTyped.length, ?_⟩
  intro index indexType indexAssigned
  by_cases same : index = address
  · subst index
    have equality : indexType = type := Option.some.inj (indexAssigned.symm.trans assigned)
    subst indexType
    exact ⟨replacement,by simp [Array.set!,Array.setIfInBounds,bound],replacementTyped⟩
  · obtain ⟨prior,found,typed⟩ := heapTyped.cell index indexType indexAssigned
    exact ⟨prior,by simpa [Array.set!,Array.setIfInBounds,bound,same,Ne.symm same] using found,typed⟩

/-- Pushing a typed thunk/cached predecessor extends the type assignment once;
all old origins, cached values, captures and frame addresses remain typed. -/
theorem heap_typed_push {assumptions : Assumptions} {types : AddressTypes}
    {heap : Array Cell} {cell : Cell} {type : Ty}
    (heapTyped : HeapTyping assumptions types heap)
    (cellTyped : CellTyping assumptions (types ++ [type]) cell type) :
    HeapTyping assumptions (types ++ [type]) (heap.push cell) := by
  refine ⟨by simp [heapTyped.length], ?_⟩
  intro address assignedType assigned
  by_cases prior : address < types.length
  · have oldAssigned : types[address]? = some assignedType := by
      simpa [List.getElem?_append,prior] using assigned
    obtain ⟨stored,found,typed⟩ := heapTyped.cell address assignedType oldAssigned
    refine ⟨stored,?_,CellTyping.weaken (type_extension_append types [type]) typed⟩
    simpa only [Array.getElem?_push,← heapTyped.length,if_neg (Nat.ne_of_lt prior)] using found
  · have bound : address < types.length + 1 := by
      simpa using (List.getElem?_eq_some_iff.mp assigned).1
    have same : address = types.length := Nat.le_antisymm (Nat.le_of_lt_succ bound) (Nat.le_of_not_gt prior)
    subst address
    have equality : assignedType = type := by simpa [List.getElem?_append] using assigned.symm
    subst assignedType
    exact ⟨cell,by rw [heapTyped.length]; exact Array.getElem?_push_size,cellTyped⟩

/-- A typed control cannot already be a semantic/internal refusal. -/
theorem typed_control_not_refused {assumptions : Assumptions} {types : AddressTypes}
    {control : Control} {type : Ty} (typed : ControlTyping assumptions types control type)
    (reason : Refusal) : control ≠ .refused reason := by
  cases typed <;> simp

/-- Independently qualified graph invariants preserve invalid-update exclusion
for EVERY stepRaw branch. This independent local lemma uses only busy-update
invariants; the all-constructor typing theorem below covers operand refusals. -/
theorem typed_step_no_invalidUpdate {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result) :
    (stepRaw state).control ≠ .refused .invalidUpdate :=
  ObjectiveBendDemandInvariant.stepRaw_no_invalidUpdate typed.busy
    (typed_control_not_refused typed.control .invalidUpdate)

/-- The independent graph invariants accompany any locally proved typed raw
transition, without an additional scope or update-stack premise. -/
def step_certificate {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result)
    (current : Ty) (heap : HeapTyping assumptions types (stepRaw state).heap)
    (control : ControlTyping assumptions types (stepRaw state).control current)
    (stack : StackTyping assumptions types (stepRaw state).stack current result) :
    StateTyping assumptions types (stepRaw state) result :=
  ⟨current,heap,control,stack,typed.assumptionsValid,
    ObjectiveBendDemandInvariant.stepRaw_lexicalInvariant typed.lexical,
    ObjectiveBendDemandInvariant.stepRaw_busyInvariant typed.busy,
    ObjectiveBendDemandInvariant.stepRaw_finalStackInvariant typed.terminalStack⟩

/-- Immediate weak-head values are precisely scalars and lexical lambdas.
Records still allocate suspended fields through the actual machine. -/
def immediateValue (term : Term) (environment : Environment) : Option RuntimeValue :=
  match term with
  | .lam body => some (.closure body environment)
  | other => scalarValue other

/-- All source derivations, including finite row/alias conversions, preserve
immediate value typing. Reusable lambdas retain the actual body capture proof. -/
theorem immediate_value_typed {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    ∀ (types : AddressTypes) (environment : Environment),
      EnvironmentTyping types context environment →
      ∀ value, immediateValue term environment = some value →
        ValueTyping assumptions types value type := by
  refine PartialTyping.rec
    (motive_1 := fun context term type _ _ => ∀ types environment,
      EnvironmentTyping types context environment →
      ∀ value, immediateValue term environment = some value →
        ValueTyping assumptions types value type)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
  · intros; simp [immediateValue,scalarValue] at *
  · intro context n types env envTyped value found
    simp only [immediateValue,scalarValue,Option.some.injEq] at found
    subst value; exact .natural n
  · intro context boolean types env envTyped value found
    simp only [immediateValue,scalarValue,Option.some.injEq] at found
    subst value; exact .boolean boolean
  · intro context label types env envTyped value found
    simp only [immediateValue,scalarValue,Option.some.injEq] at found
    subst value; exact .label label
  · intro context body annotation uses bodyTyped safe valid captures ih types env envTyped value found
    simp only [immediateValue,Option.some.injEq] at found
    subst value; exact .closure envTyped bodyTyped safe valid captures
  · intro context term actual expected uses prior agreement ih types env envTyped value found
    exact .conversion (ih types env envTyped value found) agreement
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; simp [immediateValue,scalarValue] at *
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- Allocating transitions use a genuinely extended assignment; all imported
representation invariants continue over the same raw executor step. -/
def step_alloc_certificate {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result)
    (after : AddressTypes) (current : Ty)
    (heap : HeapTyping assumptions after (stepRaw state).heap)
    (control : ControlTyping assumptions after (stepRaw state).control current)
    (stack : StackTyping assumptions after (stepRaw state).stack current result) :
    StateTyping assumptions after (stepRaw state) result :=
  ⟨current,heap,control,stack,typed.assumptionsValid,
    ObjectiveBendDemandInvariant.stepRaw_lexicalInvariant typed.lexical,
    ObjectiveBendDemandInvariant.stepRaw_busyInvariant typed.busy,
    ObjectiveBendDemandInvariant.stepRaw_finalStackInvariant typed.terminalStack⟩

/-- Demanding ANY well-typed address preserves its assigned type in all three
cell phases. A cyclic active demand may become blackhole, never missingCell.
Suspended origins retain their source derivation and capture quantities. -/
theorem typed_enter_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {address : Address}
    (typed : StateTyping assumptions types state result)
    (enter : state.control = .enter address) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have assigned : types[address]? = some typed.current := by
    have control := typed.control
    rw [enter] at control
    cases control with | enter assigned => exact assigned
  obtain ⟨cell,found,cellTyped⟩ := typed.heap.cell address typed.current assigned
  cases cellTyped with
  | suspended origin _ =>
    refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
    · simpa [stepRaw,enter,found] using heap_typed_set typed.heap assigned (.evaluating origin (heap_type_pure typed.heap assigned))
    · simpa [stepRaw,enter,found] using (ControlTyping.evaluate origin)
    · simpa [stepRaw,enter,found] using (StackTyping.cons (.update assigned (heap_type_pure typed.heap assigned)) typed.stack)
  | evaluating origin _ =>
    refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
    · simpa [stepRaw,enter,found] using typed.heap
    · simpa [stepRaw,enter,found] using (ControlTyping.blackhole assigned)
    · simpa [stepRaw,enter,found] using typed.stack
  | cached origin value _ =>
    refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
    · simpa [stepRaw,enter,found] using typed.heap
    · simpa [stepRaw,enter,found] using (ControlTyping.returned value)
    · simpa [stepRaw,enter,found] using typed.stack

/-- Lookup of the explicit finite row prefix preserves first-field shadowing.
Rigid/recursive tails stay opaque here; this theorem makes no alias-unfolding
or arbitrary future-field assertion. -/
def finiteLookup : Ty → String → Option Ty
  | .field name member tail, query =>
      if name = query then some member else finiteLookup tail query
  | _, _ => none

theorem insert_canonical_lookup (row : Ty) (name query : String) (member : Ty) :
    finiteLookup (row.insertCanonical name member) query =
      if name = query then some member else finiteLookup row query := by
  induction row with
  | field prior old tail oldIH tailIH =>
      by_cases equal : name = prior
      · subst prior
        by_cases hit : name = query <;> simp [Ty.insertCanonical,finiteLookup,hit]
      · by_cases before : name < prior
        · simp only [Ty.insertCanonical,if_neg equal,if_pos before]
          by_cases hit : name = query
          <;> by_cases priorHit : prior = query
          <;> simp_all [finiteLookup]
        · simp only [Ty.insertCanonical,if_neg equal,if_neg before]
          by_cases hit : name = query
          <;> by_cases priorHit : prior = query
          <;> simp_all [finiteLookup]
  | _ => rfl

/-- The SAME canonicalizer used by the executable checker preserves every
visible member modulo recursively canonical member types, at arbitrary row
length and duplicate shadowing. It preserves the opaque tail by construction. -/
theorem canonical_lookup (row : Ty) (query : String) :
    finiteLookup row.canonical query = (finiteLookup row query).map Ty.canonical := by
  induction row with
  | field name member tail memberIH tailIH =>
      simp only [Ty.canonical,insert_canonical_lookup,finiteLookup]
      split <;> simp_all
  | _ => rfl

/-- Finite named-row comparison cannot change a visible member's canonical
meaning. This is a general canonical-equality law, not a closed fixture test. -/
theorem canonical_row_lookup_agreement (first second : Ty) (query : String)
    (agreement : first.canonical = second.canonical) :
    (finiteLookup first query).map Ty.canonical = (finiteLookup second query).map Ty.canonical := by
  rw [← canonical_lookup,← canonical_lookup,agreement]

theorem safe_quantity_add_left (quantity : Quantity) (first second : Nat)
    (safe : safeQuantity quantity (first + second) = true) :
    safeQuantity quantity first = true := by
  cases quantity <;> simp_all [safeQuantity] <;> omega

theorem safe_add_uses_left (context : Context) (first second : Uses)
    (firstLength : first.length = context.length) (secondLength : second.length = context.length)
    (safe : safeUses context (addUses first second) = true) : safeUses context first = true := by
  induction context generalizing first second with
  | nil =>
      cases first with
      | nil => rfl
      | cons head tail => simp at firstLength
  | cons binding context ih =>
      cases first with
      | nil => simp at firstLength
      | cons first firsts =>
        cases second with
        | nil => simp at secondLength
        | cons second seconds =>
          have fl : firsts.length = context.length := Nat.succ.inj firstLength
          have sl : seconds.length = context.length := Nat.succ.inj secondLength
          have decomposed : safeQuantity binding.quantity (first+second) = true ∧
              safeUses context (addUses firsts seconds) = true := by
            simpa [safeUses,addUses,List.zipWith,List.zip,List.all_cons,fl,sl] using safe
          have head := safe_quantity_add_left binding.quantity first second decomposed.1
          have tail := ih firsts seconds fl sl decomposed.2
          simpa [safeUses,List.zip,List.all_cons,fl,head] using tail

def isVariable : Ty → Bool
  | .variable _ => true
  | _ => false

theorem insert_canonical_not_variable (row : Ty) (name : String) (member : Ty) :
    isVariable (row.insertCanonical name member) = false := by
  cases row <;> simp only [Ty.insertCanonical]
  all_goals repeat' first | split
  all_goals rfl

theorem canonical_is_variable (type : Ty) : isVariable type.canonical = isVariable type := by
  cases type <;> try rfl
  exact insert_canonical_not_variable _ _ _

theorem canonical_variable_inverse {type : Ty} {index : Nat}
    (equal : type.canonical = .variable index) : type = .variable index := by
  have isVar : isVariable type = true := by rw [← canonical_is_variable,equal]; rfl
  cases type <;> simp [isVariable] at isVar
  simpa [Ty.canonical] using equal

theorem insert_canonical_tail (row : Ty) (name : String) (member : Ty) :
    (row.insertCanonical name member).tail = row.tail := by
  induction row with
  | field prior old tail oldIH tailIH =>
      simp only [Ty.insertCanonical]
      split <;> try rfl
      split <;> simp_all [Ty.tail]
  | _ => rfl

theorem canonical_tail (row : Ty) : row.canonical.tail = row.tail.canonical := by
  induction row with
  | field name member tail memberIH tailIH =>
      simpa only [Ty.canonical,Ty.tail,insert_canonical_tail] using tailIH
  | _ => rfl

/-- A successful finite lookup either uses the explicit prefix or discloses
its precise unknown tail alias and the already-bounded lookup into that alias.
Cycles are permitted; the theorem never asks an alias to terminate. -/
theorem lookup_prefix_or_alias (bounds : Bounds) (fuel : Nat) (row : Ty)
    (name : String) (member : Ty) (lookup : row.lookup bounds fuel name = some member) :
    finiteLookup row name = some member ∨
      (finiteLookup row name = none ∧ ∃ index bound depth,
        row.tail = .variable index ∧ bounds.lookup index = some bound ∧ bound.lookup bounds depth name = some member) := by
  induction fuel generalizing row with
  | zero => simp [Ty.lookup] at lookup
  | succ fuel ih =>
      cases row with
      | field prior type tail =>
          by_cases hit : prior = name
          · left; simpa [Ty.lookup,finiteLookup,hit] using lookup
          · have next : tail.lookup bounds fuel name = some member := by simpa [Ty.lookup,hit] using lookup
            rcases ih tail next with visible | ⟨absent,index,bound,depth,tailEq,found,next⟩
            · exact Or.inl (by simpa [finiteLookup,hit] using visible)
            · exact Or.inr ⟨by simpa [finiteLookup,hit] using absent,index,bound,depth,tailEq,found,next⟩
      | «variable» index =>
          cases found : bounds.lookup index with
          | none => simp [Ty.lookup,found] at lookup
          | some bound =>
            exact Or.inr ⟨rfl,index,bound,fuel,rfl,found,by simpa [Ty.lookup,found] using lookup⟩
      | _ => simp [Ty.lookup] at lookup

theorem finite_lookup_realizes (bounds : Bounds) (row : Ty) (name : String) (member : Ty)
    (visible : finiteLookup row name = some member) :
    ∃ fuel, row.lookup bounds fuel name = some member := by
  induction row with
  | field prior type tail typeIH tailIH =>
      by_cases hit : prior = name
      · exact ⟨1,by simpa [finiteLookup,Ty.lookup,hit] using visible⟩
      · obtain ⟨fuel,lookup⟩ := tailIH (by simpa [finiteLookup,hit] using visible)
        exact ⟨fuel+1,by simpa [Ty.lookup,hit] using lookup⟩
  | _ => simp [finiteLookup] at visible

theorem alias_tail_lookup_realizes (bounds : Bounds) (row : Ty) (name : String) (member : Ty)
    (absent : finiteLookup row name = none) (index : Nat) (bound : Ty) (depth : Nat)
    (tail : row.tail = .variable index) (found : bounds.lookup index = some bound)
    (lookup : bound.lookup bounds depth name = some member) :
    ∃ fuel, row.lookup bounds fuel name = some member := by
  induction row with
  | field prior type rest typeIH restIH =>
      have hit : prior ≠ name := by intro same; simp [finiteLookup,same] at absent
      obtain ⟨fuel,next⟩ := restIH (by simpa [finiteLookup,hit] using absent) tail
      exact ⟨fuel+1,by simpa [Ty.lookup,hit] using next⟩
  | «variable» prior =>
      have same : prior = index := by simpa [Ty.tail] using tail
      subst prior
      exact ⟨depth+1,by simpa [Ty.lookup,found] using lookup⟩
  | _ => simp [Ty.tail] at tail

/-- The checker's finite row equality transports every actual bounded lookup,
including a disclosed recursive tail. Address member types retain a concrete
canonical-equality proof; unknown members are never fabricated. -/
theorem canonical_lookup_transport (bounds : Bounds) (actual expected : Ty)
    (agreement : actual.canonical = expected.canonical) (fuel : Nat) (name : String) (member : Ty)
    (lookup : expected.lookup bounds fuel name = some member) :
    ∃ depth actualMember, actual.lookup bounds depth name = some actualMember ∧
      actualMember.canonical = member.canonical := by
  have prefixes := canonical_row_lookup_agreement actual expected name agreement
  rcases lookup_prefix_or_alias bounds fuel expected name member lookup with visible | ⟨absent,index,bound,depth,tail,found,next⟩
  · rw [visible] at prefixes
    cases actualPrefix : finiteLookup actual name with
    | none => simp [actualPrefix] at prefixes
    | some actualMember =>
      obtain ⟨depth,actualLookup⟩ := finite_lookup_realizes bounds actual name actualMember actualPrefix
      exact ⟨depth,actualMember,actualLookup,by simpa [actualPrefix] using prefixes⟩
  · have actualAbsent : finiteLookup actual name = none := by
      rw [absent] at prefixes
      cases actualPrefix : finiteLookup actual name <;> simp_all
    have tails : actual.tail.canonical = expected.tail.canonical := by
      simpa only [canonical_tail] using congrArg Ty.tail agreement
    have actualTail : actual.tail = .variable index :=
      canonical_variable_inverse (by simpa [tail,Ty.canonical] using tails)
    obtain ⟨fuel,actualLookup⟩ := alias_tail_lookup_realizes bounds actual name member actualAbsent index bound depth actualTail found next
    exact ⟨fuel,member,actualLookup,rfl⟩

theorem same_type_lookup_transport {assumptions : Assumptions} {actual expected : Ty}
    (agreement : sameType assumptions actual expected = true) (fuel : Nat) (name : String) (member : Ty)
    (lookup : expected.lookup assumptions.bounds fuel name = some member) :
    ∃ depth actualMember, actual.lookup assumptions.bounds depth name = some actualMember ∧
      actualMember.canonical = member.canonical := by
  simp only [sameType,Bool.or_eq_true] at agreement
  rcases agreement with (canonical | aliasActual) | aliasExpected
  · exact canonical_lookup_transport assumptions.bounds actual expected (by simpa using canonical) fuel name member lookup
  · cases actual <;> simp at aliasActual
    rename_i index
    cases found : assumptions.bounds.lookup index with
    | none => simp [found] at aliasActual
    | some bound =>
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = expected.canonical := by simpa [found] using aliasActual
      obtain ⟨depth,actualMember,actualLookup,memberEq⟩ := canonical_lookup_transport assumptions.bounds bound expected equal fuel name member lookup
      exact ⟨depth+1,actualMember,by simpa [Ty.lookup,found] using actualLookup,memberEq⟩
  · cases expected <;> simp at aliasExpected
    rename_i index
    cases found : assumptions.bounds.lookup index with
    | none => simp [found] at aliasExpected
    | some bound =>
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = actual.canonical := by simpa [found] using aliasExpected
      cases fuel with
      | zero => simp [Ty.lookup] at lookup
      | succ fuel =>
        have next : bound.lookup assumptions.bounds fuel name = some member := by simpa [Ty.lookup,found] using lookup
        exact canonical_lookup_transport assumptions.bounds actual bound equal.symm fuel name member next

/-- Declared aliases have a deterministic head equation. Its normalization
relation is partial: cyclic aliases need not produce a head, and no general Fix
computation or subtype oracle is used in conversion. -/
inductive HeadNormalizes (bounds : Bounds) : Ty → Ty → Prop where
  | direct (type : Ty) : isVariable type = false → HeadNormalizes bounds type type.canonical
  | alias {index : Nat} {bound result : Ty} : bounds.lookup index = some bound →
      HeadNormalizes bounds bound result → HeadNormalizes bounds (.variable index) result

theorem head_normalizes_unique {bounds : Bounds} {type first second : Ty}
    (one : HeadNormalizes bounds type first) (two : HeadNormalizes bounds type second) :
    first = second := by
  induction one with
  | direct type terminal =>
      cases two with
      | direct => rfl
      | alias found prior => simp [isVariable] at terminal
  | alias found prior ih =>
      cases two with
      | direct type terminal => simp [isVariable] at terminal
      | alias found' prior' =>
        have same := Option.some.inj (found.symm.trans found')
        subst same
        exact ih prior'

theorem canonical_agreement_normalizes {bounds : Bounds} {first second result : Ty}
    (agreement : first.canonical = second.canonical)
    (normal : HeadNormalizes bounds first result) : HeadNormalizes bounds second result := by
  cases normal with
  | direct first terminal =>
      have terminal' : isVariable second = false := by
        rw [← canonical_is_variable,← agreement,canonical_is_variable,terminal]
      simpa [agreement] using (HeadNormalizes.direct second terminal' : HeadNormalizes bounds second second.canonical)
  | alias found prior =>
      have equal := canonical_variable_inverse agreement.symm
      rw [equal]
      exact .alias found prior

/-- Every successful checker's SAME finite type agreement preserves any head
normalization witness. Thus a row/alias conversion cannot turn a Nat value into
Bool/String or a scalar into a callable/record. Cyclic aliases remain partial. -/
theorem same_type_preserves_head {assumptions : Assumptions} {first second result : Ty}
    (agreement : sameType assumptions first second = true)
    (normal : HeadNormalizes assumptions.bounds first result) :
    HeadNormalizes assumptions.bounds second result := by
  simp only [sameType,Bool.or_eq_true] at agreement
  rcases agreement with (canonical | aliasFirst) | aliasSecond
  · exact canonical_agreement_normalizes (by simpa using canonical) normal
  · cases first <;> simp at aliasFirst
    rename_i index
    cases found : assumptions.bounds.lookup index with
    | none => simp [found] at aliasFirst
    | some bound =>
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = second.canonical := by simpa [found] using aliasFirst
      cases normal with
      | direct type terminal => simp [isVariable] at terminal
      | alias found' prior =>
        have same := Option.some.inj (found'.symm.trans found)
        subst same
        exact canonical_agreement_normalizes equal prior
  · cases second <;> simp at aliasSecond
    rename_i index
    cases found : assumptions.bounds.lookup index with
    | none => simp [found] at aliasSecond
    | some bound =>
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = first.canonical := by simpa [found] using aliasSecond
      exact .alias found (canonical_agreement_normalizes equal.symm normal)

inductive HeadKind where
  | natural | boolean | label | function | row | specification | prototype | custody | variable | variant
  | computation
  deriving DecidableEq

def typeHead : Ty → HeadKind
  | .natural => .natural | .boolean => .boolean | .label => .label
  | .arrow _ _ _ _ => .function | .emptyRow | .field _ _ _ => .row
  | .specification _ _ => .specification | .prototype _ _ => .prototype
  | .custody _ => .custody | .variable _ => .variable | .variant _ => .variant
  | .computation _ _ _ => .computation

def valueHead : RuntimeValue → HeadKind
  | .natural _ => .natural | .boolean _ => .boolean | .label _ => .label
  | .closure _ _ => .function | .record _ => .row
  | .specification _ _ => .specification | .prototype _ _ => .prototype
  | .variant _ _ => .variant

theorem insert_canonical_row_head (row : Ty) (name : String) (member : Ty) :
    typeHead (row.insertCanonical name member) = .row := by
  cases row <;> simp only [Ty.insertCanonical]
  all_goals repeat' first | split
  all_goals rfl

theorem canonical_type_head (type : Ty) : typeHead type.canonical = typeHead type := by
  cases type <;> try rfl
  exact insert_canonical_row_head _ _ _

theorem row_head_normalizes (bounds : Bounds) (fuel : Nat) (row : Ty)
    (isRow : row.isRow bounds fuel = true) :
    ∃ head, HeadNormalizes bounds row head ∧ typeHead head = .row := by
  induction fuel generalizing row with
  | zero => simp [Ty.isRow] at isRow
  | succ fuel ih =>
      cases row with
      | emptyRow => exact ⟨.emptyRow,.direct .emptyRow rfl,rfl⟩
      | field name member tail =>
        exact ⟨_,.direct (.field name member tail) rfl,canonical_type_head _⟩
      | «variable» index =>
        simp only [Ty.isRow] at isRow
        cases found : bounds.lookup index with
        | none => simp [found] at isRow
        | some bound =>
          obtain ⟨head,normal,kind⟩ := ih bound (by simpa [found] using isRow)
          exact ⟨head,.alias found normal,kind⟩
      | _ => simp [Ty.isRow] at isRow

/-- Runtime canonical forms follow from ACTUAL value derivations and the same
finite alias equations checked at source. No assumed constructor-shape oracle
is used, and no termination of cyclic aliases is required. -/
theorem value_head_correct {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {type : Ty} (typed : ValueTyping assumptions types value type) :
    ∃ head, HeadNormalizes assumptions.bounds type head ∧ typeHead head = valueHead value := by
  induction typed with
  | natural value => exact ⟨.natural,.direct .natural rfl,rfl⟩
  | boolean value => exact ⟨.boolean,.direct .boolean rfl,rfl⟩
  | label value => exact ⟨.label,.direct .label rfl,rfl⟩
  | closure environment body safe valid captures => exact ⟨_,.direct _ rfl,rfl⟩
  | record isRow members =>
      obtain ⟨fuel,isRow⟩ := isRow
      exact row_head_normalizes _ fuel _ isRow
  | specification metadata ext => exact ⟨_,.direct _ rfl,rfl⟩
  | prototype spec target => exact ⟨_,.direct _ rfl,rfl⟩
  | variant lookup assigned path => exact ⟨_,.direct _ rfl,rfl⟩
  | conversion prior agreement ih =>
      obtain ⟨head,normal,kind⟩ := ih
      exact ⟨head,same_type_preserves_head agreement normal,kind⟩

/-- No runtime value inhabits an activity type: activities are control, not data. -/
theorem value_typed_not_computation {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {type : Ty} (typed : ValueTyping assumptions types value type) :
    type.isComputation = false := by
  cases h : type.isComputation
  · rfl
  · exfalso
    obtain ⟨head,normal,kind⟩ := value_head_correct typed
    cases type <;> simp [Ty.isComputation] at h
    have same := head_normalizes_unique normal (.direct _ rfl)
    subst same
    cases value <;> simp [typeHead,valueHead,Ty.canonical] at kind

theorem natural_value_form {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} (typed : ValueTyping assumptions types value .natural) :
    ∃ number, value = .natural number := by
  obtain ⟨head,normal,kind⟩ := value_head_correct typed
  have same := head_normalizes_unique normal (.direct .natural rfl)
  subst head
  have scalarKind : valueHead value = .natural := by simpa [typeHead] using kind.symm
  cases value with
  | natural number => exact ⟨number,rfl⟩
  | _ => cases scalarKind

theorem boolean_value_form {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} (typed : ValueTyping assumptions types value .boolean) :
    ∃ boolean, value = .boolean boolean := by
  obtain ⟨head,normal,kind⟩ := value_head_correct typed
  have same := head_normalizes_unique normal (.direct .boolean rfl)
  subst head
  have scalarKind : valueHead value = .boolean := by simpa [typeHead] using kind.symm
  cases value with
  | boolean boolean => exact ⟨boolean,rfl⟩
  | _ => cases scalarKind

theorem label_value_form {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} (typed : ValueTyping assumptions types value .label) :
    ∃ name, value = .label name := by
  obtain ⟨head,normal,kind⟩ := value_head_correct typed
  have same := head_normalizes_unique normal (.direct .label rfl)
  subst head
  have scalarKind : valueHead value = .label := by simpa [typeHead] using kind.symm
  cases value with
  | label name => exact ⟨name,rfl⟩
  | _ => cases scalarKind

theorem canonical_same_type (assumptions : Assumptions) (first second : Ty)
    (agreement : first.canonical = second.canonical) : sameType assumptions first second = true := by
  simp [sameType,agreement]

theorem specification_value_form {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {metadataType extensionType : Ty}
    (typed : ValueTyping assumptions types value (.specification metadataType extensionType)) :
    ∃ metadata extension, value = .specification metadata extension := by
  obtain ⟨head,normal,kind⟩ := value_head_correct typed
  have same := head_normalizes_unique normal (.direct (.specification metadataType extensionType) rfl)
  rw [same,Ty.canonical] at kind
  have shape : valueHead value = .specification := by simpa [typeHead] using kind.symm
  cases value with
  | specification metadata extension => exact ⟨metadata,extension,rfl⟩
  | _ => cases shape

theorem value_specification_fields {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {type : Ty} (typed : ValueTyping assumptions types value type) :
    ∀ metadata extension, value = .specification metadata extension →
      ∃ metadataType extensionType,
        types[metadata]? = some metadataType ∧ types[extension]? = some extensionType ∧
        HeadNormalizes assumptions.bounds type (.specification metadataType.canonical extensionType.canonical) := by
  induction typed with
  | natural value => intros; contradiction
  | boolean value => intros; contradiction
  | label value => intros; contradiction
  | closure environment body safe valid captures => intros; contradiction
  | record isRow members => intros; contradiction
  | specification metadataAssigned extensionAssigned =>
      intro metadata extension same
      cases same
      exact ⟨_,_,metadataAssigned,extensionAssigned,.direct _ rfl⟩
  | prototype spec target => intros; contradiction
  | variant lookup assigned path => intros; contradiction
  | conversion prior agreement ih =>
      intro metadata extension same
      obtain ⟨metadataType,extensionType,metadataAssigned,extensionAssigned,normal⟩ := ih metadata extension same
      exact ⟨metadataType,extensionType,metadataAssigned,extensionAssigned,same_type_preserves_head agreement normal⟩

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

theorem prototype_value_form {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {specType targetType : Ty}
    (typed : ValueTyping assumptions types value (.prototype specType targetType)) :
    ∃ spec target, value = .prototype spec target := by
  obtain ⟨head,normal,kind⟩ := value_head_correct typed
  have same := head_normalizes_unique normal (.direct (.prototype specType targetType) rfl)
  rw [same,Ty.canonical] at kind
  have shape : valueHead value = .prototype := by simpa [typeHead] using kind.symm
  cases value with
  | prototype spec target => exact ⟨spec,target,rfl⟩
  | _ => cases shape

theorem value_prototype_fields {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {type : Ty} (typed : ValueTyping assumptions types value type) :
    ∀ spec target, value = .prototype spec target → ∃ specType targetType,
      types[spec]? = some specType ∧ types[target]? = some targetType ∧
      HeadNormalizes assumptions.bounds type (.prototype specType.canonical targetType.canonical) := by
  induction typed with
  | natural value => intros; contradiction
  | boolean value => intros; contradiction
  | label value => intros; contradiction
  | closure environment body safe valid captures => intros; contradiction
  | record isRow members => intros; contradiction
  | specification metadata ext => intros; contradiction
  | prototype specAssigned targetAssigned =>
      intro spec target same; cases same
      exact ⟨_,_,specAssigned,targetAssigned,.direct _ rfl⟩
  | variant lookup assigned path => intros; contradiction
  | conversion prior agreement ih =>
      intro spec target same
      obtain ⟨specType,targetType,specAssigned,targetAssigned,normal⟩ := ih spec target same
      exact ⟨specType,targetType,specAssigned,targetAssigned,same_type_preserves_head agreement normal⟩

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

structure CapturedFunction (assumptions : Assumptions) (types : AddressTypes)
    (body : Term) (environment : Environment) where
  context : Context
  annotation : LambdaAnnotation
  uses : Uses
  environmentTyped : EnvironmentTyping types context environment
  bodyTyped : PartialTyping assumptions (⟨annotation.domain,annotation.parameter⟩ :: context) body annotation.codomain uses
  safe : safeUses (⟨annotation.domain,annotation.parameter⟩ :: context) uses = true
  valid : validContext assumptions.shareableVariables (⟨annotation.domain,annotation.parameter⟩ :: context) = true
  captures : reusableAllowed assumptions annotation.reuse context uses.tail = true

def CapturedFunction.arrow {assumptions : Assumptions} {types : AddressTypes}
    {body : Term} {environment : Environment} (captured : CapturedFunction assumptions types body environment) : Ty :=
  .arrow captured.annotation.reuse captured.annotation.parameter captured.annotation.domain captured.annotation.codomain

theorem value_closure_fields {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {type : Ty} (typed : ValueTyping assumptions types value type) :
    ∀ body environment, value = .closure body environment →
      ∃ captured : CapturedFunction assumptions types body environment,
        HeadNormalizes assumptions.bounds type captured.arrow.canonical := by
  induction typed with
  | natural value => intros; contradiction
  | boolean value => intros; contradiction
  | label value => intros; contradiction
  | record isRow members => intros; contradiction
  | specification metadata ext => intros; contradiction
  | prototype spec target => intros; contradiction
  | closure env bodyTyped safe valid captures =>
      intro body environment same; cases same
      exact ⟨⟨_,_,_,env,bodyTyped,safe,valid,captures⟩,.direct _ rfl⟩
  | variant lookup assigned path => intros; contradiction
  | conversion prior agreement ih =>
      intro body environment same
      obtain ⟨captured,normal⟩ := ih body environment same
      exact ⟨captured,same_type_preserves_head agreement normal⟩

theorem callable_value_form {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {functionType domain codomain : Ty} {reuse : Reuse} {quantity : Quantity}
    (typed : ValueTyping assumptions types value functionType)
    (callableEq : callable functionType = .arrow reuse quantity domain codomain) :
    (∃ body environment, value = .closure body environment) ∨
      (∃ metadata extension, value = .specification metadata extension) := by
  cases functionType with
  | arrow r q d c =>
      obtain ⟨head,normal,kind⟩ := value_head_correct typed
      have same := head_normalizes_unique normal (.direct (.arrow r q d c) rfl)
      rw [same,Ty.canonical] at kind
      have shape : valueHead value = .function := by simpa [typeHead] using kind.symm
      cases value with
      | closure body environment => exact .inl ⟨body,environment,rfl⟩
      | _ => cases shape
  | specification metadata extension => exact .inr (specification_value_form typed)
  | _ => simp [callable] at callableEq

theorem closure_callable_type {bounds : Bounds} {functionType : Ty}
    {reuse actualReuse : Reuse} {quantity actualQuantity : Quantity}
    {domain codomain actualDomain actualCodomain : Ty}
    (normal : HeadNormalizes bounds functionType (Ty.arrow actualReuse actualQuantity actualDomain actualCodomain).canonical)
    (callableEq : callable functionType = .arrow reuse quantity domain codomain) :
    functionType = .arrow reuse quantity domain codomain := by
  cases functionType with
  | arrow r q d c => exact callableEq
  | specification metadata extension =>
      have same := head_normalizes_unique normal (.direct (.specification metadata extension) rfl)
      simp [Ty.canonical] at same
  | _ => simp [callable] at callableEq

theorem specification_callable_type {bounds : Bounds} {functionType : Ty}
    {reuse : Reuse} {quantity : Quantity} {domain codomain metadata extension : Ty}
    (normal : HeadNormalizes bounds functionType (Ty.specification metadata extension).canonical)
    (callableEq : callable functionType = .arrow reuse quantity domain codomain) :
    ∃ metadataType extensionType, functionType = .specification metadataType extensionType := by
  cases functionType with
  | specification metadata extension => exact ⟨metadata,extension,rfl⟩
  | arrow r q d c =>
      have same := head_normalizes_unique normal (.direct (.arrow r q d c) rfl)
      simp [Ty.canonical] at same
  | _ => simp [callable] at callableEq

theorem stack_argument_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ argument environment rest, stack = .argument argument environment :: rest →
      ∃ functionType domain codomain reuse quantity,
        ∃ origin : ClosureTyping assumptions types ⟨argument,environment⟩ domain,
          callable functionType = .arrow reuse quantity domain codomain ∧
          argumentAllowed assumptions quantity origin.context domain origin.uses = true ∧
          ValueTyping assumptions types value functionType ∧
          StackTyping assumptions types rest codomain result := by
  induction continuation with
  | nil type => intro argument environment rest impossible; simp at impossible
  | cons frame restTyped =>
      intro argument environment rest same; cases same
      cases frame with
      | argument origin callableEq copyAllowed => exact ⟨_,_,_,_,_,origin,callableEq,copyAllowed,valueTyped,restTyped⟩
  | conversion agreement restTyped ih => exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro argument environment rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

/-- Calling a lexical closure allocates the actual argument source at the
closure's authored domain representative. Its body keeps the original capture
and quantity evidence; component conversions remain in the continuation. A
first-class specification enters its stored extension without consuming the
argument frame. This follows the actual machine's two application branches. -/
theorem typed_argument_return_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue} {argument : Term}
    {environment : Environment} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .argument argument environment :: rest) :
    ∃ after, TypeExtension types after ∧ Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control; rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨ft,domain,codomain,reuse,quantity,argumentOrigin,callableEq,copyAllowed,fnTyped,restTyped⟩ :=
    stack_argument_value typed.stack valueTyped argument environment rest stack
  rcases callable_value_form fnTyped callableEq with ⟨body,capturedEnvironment,rfl⟩ | ⟨metadata,extension,rfl⟩
  · obtain ⟨captured,normal⟩ := value_closure_fields fnTyped body capturedEnvironment rfl
    have ftEq := closure_callable_type normal callableEq
    rw [ftEq] at normal
    have same := head_normalizes_unique normal (.direct (.arrow reuse quantity domain codomain) rfl)
    have domainEq : captured.annotation.domain.canonical = domain.canonical := by
      simpa [CapturedFunction.arrow,Ty.canonical] using
        congrArg (fun type => match type with | .arrow _ _ domain _ => domain | _ => type) same
    have codomainEq : captured.annotation.codomain.canonical = codomain.canonical := by
      simpa [CapturedFunction.arrow,Ty.canonical] using
        congrArg (fun type => match type with | .arrow _ _ _ codomain => codomain | _ => type) same
    let after := types ++ [captured.annotation.domain]
    have extension : TypeExtension types after := type_extension_append types _
    have assigned : after[state.heap.size]? = some captured.annotation.domain := by rw [← typed.heap.length]; simp [after]
    let argumentNext : ClosureTyping assumptions after ⟨argument,environment⟩ captured.annotation.domain :=
      ⟨argumentOrigin.context,argumentOrigin.uses,argumentOrigin.environment.weaken extension,
        .conversion argumentOrigin.source (canonical_same_type assumptions _ _ domainEq.symm),argumentOrigin.safe,argumentOrigin.contextValid⟩
    let bodyNext : ClosureTyping assumptions after ⟨body,state.heap.size :: capturedEnvironment⟩ captured.annotation.codomain :=
      ⟨⟨captured.annotation.domain,captured.annotation.parameter⟩ :: captured.context,captured.uses,
        (captured.environmentTyped.weaken extension).cons assigned,captured.bodyTyped,captured.safe,captured.valid⟩
    refine ⟨after,extension,⟨step_alloc_certificate typed after captured.annotation.codomain ?_ ?_ ?_⟩⟩
    · have domainPure : captured.annotation.domain.isComputation = false := by
        rw [← Ty.canonical_isComputation,domainEq,Ty.canonical_isComputation]
        exact argumentAllowed_not_computation copyAllowed
      simpa [stepRaw,returned,stack] using heap_typed_push typed.heap (.suspended argumentNext domainPure)
    · simpa [stepRaw,returned,stack] using (ControlTyping.evaluate bodyNext)
    · simpa [stepRaw,returned,stack] using
        (StackTyping.weaken extension (.conversion (canonical_same_type assumptions _ _ codomainEq) restTyped))
  · obtain ⟨actualMetadata,actualExtension,metadataAssigned,extensionAssigned,normal⟩ := value_specification_fields fnTyped metadata extension rfl
    obtain ⟨metadataType,extensionType,ftEq⟩ := specification_callable_type normal callableEq
    rw [ftEq] at normal callableEq
    have same := head_normalizes_unique normal (.direct (.specification metadataType extensionType) rfl)
    have extensionEq : actualExtension.canonical = extensionType.canonical := by
      simpa [Ty.canonical] using
        congrArg (fun type => match type with | .specification _ extension => extension | _ => type) same
    have extensionCallable : callable extensionType = .arrow reuse quantity domain codomain := callableEq
    refine ⟨types,type_extension_refl types,⟨step_certificate typed actualExtension ?_ ?_ ?_⟩⟩
    · simpa [stepRaw,returned,stack] using typed.heap
    · simpa [stepRaw,returned,stack] using (ControlTyping.enter extensionAssigned)
    · simpa [stepRaw,returned,stack] using
        (StackTyping.conversion (canonical_same_type assumptions _ _ extensionEq)
          (.cons (.argument argumentOrigin extensionCallable copyAllowed) restTyped))

/-- Inserting a lexical slot shifts precisely the indices at/after its depth.
This is independent of rigid future-type variables in annotations. -/
def shiftIndex (depth index : Nat) : Nat := if index < depth then index else index+1

theorem lift_shift_index (depth : Nat) : liftRename (shiftIndex depth) = shiftIndex (depth+1) := by
  funext index
  cases index <;> simp [liftRename,shiftIndex]
  split <;> omega

theorem binding_insert_shift {context : Context} {index depth : Nat} {declared binding : Binding}
    (found : context[index]? = some declared) :
    (context.insertIdx depth binding)[shiftIndex depth index]? = some declared := by
  by_cases before : index < depth
  · simpa [shiftIndex,before,List.getElem?_insertIdx_of_lt before] using found
  · have after : depth < index+1 := by omega
    simpa [shiftIndex,before,List.getElem?_insertIdx_of_gt after] using found

theorem zero_uses_insert (context : Context) (binding : Binding) (depth : Nat)
    (bound : depth ≤ context.length) :
    zeroUses (context.insertIdx depth binding) = (zeroUses context).insertIdx depth 0 := by
  induction depth generalizing context with
  | zero => simp [zeroUses,List.insertIdx_zero,List.replicate_succ]
  | succ depth ih =>
      cases context with
      | nil => simp at bound
      | cons first rest =>
          have tailBound : depth ≤ rest.length := by simpa using bound
          simpa [zeroUses,List.insertIdx_succ_cons,List.replicate_succ] using congrArg (List.cons 0) (ih rest tailBound)

theorem add_uses_insert (first second : Uses) (depth : Nat)
    (lengths : first.length = second.length) (bound : depth ≤ first.length) :
    addUses (first.insertIdx depth 0) (second.insertIdx depth 0) = (addUses first second).insertIdx depth 0 := by
  induction depth generalizing first second with
  | zero => rfl
  | succ depth ih =>
      cases first with
      | nil => simp at bound
      | cons a first =>
          cases second with
          | nil => simp at lengths
          | cons b second =>
              simp only [List.length_cons,Nat.add_le_add_iff_right] at bound
              have lengths' : first.length = second.length := Nat.succ.inj lengths
              simpa [addUses,List.insertIdx_succ_cons,List.zipWith] using congrArg (List.cons (a+b)) (ih first second lengths' bound)

theorem variable_uses_lookup (context : Context) (index query : Nat) :
    (variableUses context index)[query]? =
      if query < context.length then some (if query = index then 1 else 0) else none := by
  by_cases inside : query < context.length <;> simp [variableUses,inside]

theorem variable_uses_insert (context : Context) (binding : Binding) (index depth : Nat)
    (bound : depth ≤ context.length) :
    variableUses (context.insertIdx depth binding) (shiftIndex depth index) =
      (variableUses context index).insertIdx depth 0 := by
  apply List.ext_getElem?
  intro query
  rw [variable_uses_lookup,List.length_insertIdx_of_le_length bound binding,List.getElem?_insertIdx]
  by_cases before : query < depth
  · have inside : query < context.length := by omega
    have shifted : query = shiftIndex depth index ↔ query = index := by
      by_cases prior : index < depth <;> simp [shiftIndex,prior] <;> omega
    have newInside : query < context.length+1 := by omega
    simp [before,inside,newInside,variable_uses_lookup,shifted]
  · by_cases inserted : query = depth
    · subst query
      have notShifted : depth ≠ shiftIndex depth index := by
        by_cases prior : index < depth <;> simp [shiftIndex,prior] <;> omega
      have newInside : depth < context.length+1 := by omega
      simp [before,bound,newInside,notShifted,variableUses]
    · have positive : 0 < query := by omega
      have shifted : query = shiftIndex depth index ↔ query-1 = index := by
        by_cases prior : index < depth <;> simp [shiftIndex,prior] <;> omega
      have range : query < context.length+1 ↔ query-1 < context.length := by omega
      simp [before,inserted,variable_uses_lookup,range,shifted]

theorem safe_quantity_zero (quantity : Quantity) : safeQuantity quantity 0 = true := by
  cases quantity <;> rfl

theorem safe_uses_insert (context : Context) (uses : Uses) (depth : Nat) (binding : Binding)
    (safe : safeUses context uses = true) (bound : depth ≤ context.length) :
    safeUses (context.insertIdx depth binding) (uses.insertIdx depth 0) = true := by
  induction depth generalizing context uses with
  | zero => simpa [safeUses,List.insertIdx_zero,safe_quantity_zero] using safe
  | succ depth ih =>
      cases context with
      | nil => simp at bound
      | cons first context =>
          cases uses with
          | nil => simp [safeUses] at safe
          | cons count uses =>
              have tailBound : depth ≤ context.length := by simpa using bound
              have facts : safeQuantity first.quantity count = true ∧ safeUses context uses = true := by
                simpa [safeUses,List.zip,List.all_cons,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm,and_assoc,and_left_comm,and_comm] using safe
              have tail := ih context uses facts.2 tailBound
              simpa [safeUses,List.insertIdx_succ_cons,List.zip,List.all_cons,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm,and_assoc,and_left_comm,and_comm] using And.intro facts.1 tail

theorem reusable_captures_insert (variables : List Nat) (context : Context) (uses : Uses)
    (depth : Nat) (binding : Binding)
    (captures : reusableCaptures variables context uses = true) (bound : depth ≤ context.length) :
    reusableCaptures variables (context.insertIdx depth binding) (uses.insertIdx depth 0) = true := by
  induction depth generalizing context uses with
  | zero => simpa [reusableCaptures,List.insertIdx_zero] using captures
  | succ depth ih =>
      cases context with
      | nil => simp at bound
      | cons first context =>
          cases uses with
          | nil => simp [reusableCaptures] at captures
          | cons count uses =>
              have tailBound : depth ≤ context.length := by simpa using bound
              have facts : (count == 0 || (first.quantity == .unrestricted && first.type.shareableUnder variables)) = true ∧
                  reusableCaptures variables context uses = true := by
                simpa [reusableCaptures,List.zip,List.all_cons,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm,and_assoc,and_left_comm,and_comm] using captures
              have tail := ih context uses facts.2 tailBound
              simpa [reusableCaptures,List.insertIdx_succ_cons,List.zip,List.all_cons,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm,and_assoc,and_left_comm,and_comm] using And.intro facts.1 tail

theorem valid_context_insert (variables : List Nat) (context : Context) (depth : Nat) (binding : Binding)
    (valid : validContext variables context = true) (bindingValid : validContext variables [binding] = true)
    (bound : depth ≤ context.length) : validContext variables (context.insertIdx depth binding) = true := by
  induction depth generalizing context with
  | zero => simpa [validContext,List.insertIdx_zero] using And.intro bindingValid valid
  | succ depth ih =>
      cases context with
      | nil => simp at bound
      | cons first context =>
          have tailBound : depth ≤ context.length := by simpa using bound
          have facts : (first.quantity != .unrestricted || first.type.shareableUnder variables) = true ∧ validContext variables context = true := by
            simpa [validContext] using valid
          simpa [validContext,List.insertIdx_succ_cons] using And.intro facts.1 (ih context facts.2 tailBound)

theorem reusable_allowed_insert (assumptions : Assumptions) (reuse : Reuse)
    (context : Context) (uses : Uses) (depth : Nat) (binding : Binding)
    (allowed : reusableAllowed assumptions reuse context uses = true) (bound : depth ≤ context.length) :
    reusableAllowed assumptions reuse (context.insertIdx depth binding) (uses.insertIdx depth 0) = true := by
  cases reuse with
  | once => rfl
  | reusable =>
      have captures : reusableCaptures assumptions.shareableVariables context uses = true := by simpa [reusableAllowed] using allowed
      simpa [reusableAllowed] using reusable_captures_insert assumptions.shareableVariables context uses depth binding captures bound

theorem argument_allowed_insert (assumptions : Assumptions) (quantity : Quantity)
    (context : Context) (type : Ty) (uses : Uses) (depth : Nat) (binding : Binding)
    (allowed : argumentAllowed assumptions quantity context type uses = true) (bound : depth ≤ context.length) :
    argumentAllowed assumptions quantity (context.insertIdx depth binding) type (uses.insertIdx depth 0) = true := by
  have pure : type.isComputation = false := argumentAllowed_not_computation allowed
  cases quantity with
  | unrestricted =>
      have facts : type.shareableUnder assumptions.shareableVariables = true ∧
          reusableCaptures assumptions.shareableVariables context uses = true := by simpa [argumentAllowed,pure] using allowed
      simpa [argumentAllowed,pure] using And.intro facts.1
        (reusable_captures_insert assumptions.shareableVariables context uses depth binding facts.2 bound)
  | _ => simp [argumentAllowed,pure]

/-- Under a lambda/conditional binder the inserted free slot is one place
farther down; dropping that original binder restores the outer use vector. -/
theorem uses_tail_insert {uses : Uses} (nonempty : 0 < uses.length) (depth : Nat) :
    (uses.insertIdx (depth+1) 0).tail = uses.tail.insertIdx depth 0 := by
  cases uses with
  | nil => simp at nonempty
  | cons head tail => rfl

theorem insert_usage_bound {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses} (typed : PartialTyping assumptions context term type uses)
    {depth : Nat} (bound : depth ≤ context.length) : depth ≤ uses.length := by rw [source_uses_length typed]; exact bound

/-- Arms account for every lexical slot of the enclosing context. -/
theorem arms_uses_length {assumptions : Assumptions} {context : Context}
    {arms : List (String × Term)} {row result : Ty} {uses : Uses}
    (typed : ArmsTyping assumptions context arms row result uses) : uses.length = context.length := by
  induction arms generalizing row uses with
  | nil => cases typed; simp [zeroUses]
  | cons arm rest ih =>
      cases typed with
      | cons bodyTyped safe shareable restTyped =>
          have bodyLength := source_uses_length bodyTyped
          have restLength := ih restTyped
          simp_all [addUses,List.length_zipWith,List.length_tail]

/-- General capture-sensitive lexical weakening over EVERY source constructor,
including nested fields and conditional/lambda binders. The inserted slot is
unused; its declared context validity is checked rather than assumed pure. -/
theorem source_insert_binding {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping assumptions context term type uses) :
    ∀ depth binding, depth ≤ context.length → validContext assumptions.shareableVariables [binding] = true →
      PartialTyping assumptions (context.insertIdx depth binding) (term.rename (shiftIndex depth)) type (uses.insertIdx depth 0) := by
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ => ∀ depth binding,
      depth ≤ context.length → validContext assumptions.shareableVariables [binding] = true →
      PartialTyping assumptions (context.insertIdx depth binding) (term.rename (shiftIndex depth)) type (uses.insertIdx depth 0))
    (motive_2 := fun context fields row uses _ => ∀ depth binding,
      depth ≤ context.length → validContext assumptions.shareableVariables [binding] = true →
      FieldsTyping assumptions (context.insertIdx depth binding)
        (fields.map fun field => (field.1,field.2.rename (shiftIndex depth))) row (uses.insertIdx depth 0))
    (motive_3 := fun context arms row result uses _ => ∀ depth binding,
      depth ≤ context.length → validContext assumptions.shareableVariables [binding] = true →
      ArmsTyping assumptions (context.insertIdx depth binding)
        (arms.map fun arm => (arm.1,arm.2.rename (shiftIndex (depth+1)))) row result (uses.insertIdx depth 0))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intro context index declared found depth binding bound bindingValid
    simpa only [Term.rename,← variable_uses_insert context binding index depth bound] using
      (PartialTyping.bound (binding_insert_shift found) : PartialTyping assumptions (context.insertIdx depth binding)
        (.bound (shiftIndex depth index)) declared.type (variableUses (context.insertIdx depth binding) (shiftIndex depth index)))
  · intro context value depth binding bound bindingValid
    simpa only [Term.rename,← zero_uses_insert context binding depth bound] using
      (PartialTyping.natural (context.insertIdx depth binding) value : PartialTyping assumptions _ (.nat value) .natural _)
  · intro context value depth binding bound bindingValid
    simpa only [Term.rename,← zero_uses_insert context binding depth bound] using
      (PartialTyping.boolean (context.insertIdx depth binding) value : PartialTyping assumptions _ (.boolean value) .boolean _)
  · intro context value depth binding bound bindingValid
    simpa only [Term.rename,← zero_uses_insert context binding depth bound] using
      (PartialTyping.label (context.insertIdx depth binding) value : PartialTyping assumptions _ (.label value) (literalType value) _)
  · intro context body annotation uses bodyTyped safe valid captures ih depth binding bound bindingValid
    have bodyBound : depth+1 ≤ (⟨annotation.domain,annotation.parameter⟩ :: context).length := by simpa using bound
    have nonempty : 0 < uses.length := by rw [source_uses_length bodyTyped]; simp
    have bodyNext := ih (depth+1) binding bodyBound bindingValid
    have safeNext := safe_uses_insert _ uses (depth+1) binding safe bodyBound
    have validNext := valid_context_insert _ _ (depth+1) binding valid bindingValid bodyBound
    have capturesNext := reusable_allowed_insert assumptions annotation.reuse context uses.tail depth binding captures bound
    simpa only [Term.rename,lift_shift_index,List.insertIdx_succ_cons,uses_tail_insert nonempty] using
      (PartialTyping.lambda bodyNext safeNext validNext (by simpa only [List.insertIdx_succ_cons,uses_tail_insert nonempty] using capturesNext))
  · intro context term actual expected uses prior agreement ih depth binding bound bindingValid
    exact .conversion (ih depth binding bound bindingValid) agreement
  · intro context fn arg functionType argumentType domain codomain fu au reuse quantity fnTyped argTyped callableEq same allowed ihFn ihArg depth binding bound bindingValid
    have counts := add_uses_insert fu au depth ((source_uses_length fnTyped).trans (source_uses_length argTyped).symm) (insert_usage_bound fnTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.application (ihFn depth binding bound bindingValid) (ihArg depth binding bound bindingValid) callableEq same
        (argument_allowed_insert assumptions quantity context argumentType au depth binding allowed bound))
  · intro context fields row uses fieldsTyped ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.record (ih depth binding bound bindingValid))
  · intro context target targetType member uses name fuel targetTyped lookup ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.get (ih depth binding bound bindingValid) lookup)
  · intro context target fields targetType row tu fu targetTyped fieldsTyped isRow ihTarget ihFields depth binding bound bindingValid
    have fieldLength := source_uses_length (PartialTyping.record fieldsTyped)
    have counts := add_uses_insert tu fu depth ((source_uses_length targetTyped).trans fieldLength.symm) (insert_usage_bound targetTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.extend (ihTarget depth binding bound bindingValid) (ihFields depth binding bound bindingValid) isRow)
  · intro context metadata extension metadataType extensionType mu eu metadataTyped extensionTyped mPure ePure ihMetadata ihExtension depth binding bound bindingValid
    have counts := add_uses_insert mu eu depth ((source_uses_length metadataTyped).trans (source_uses_length extensionTyped).symm) (insert_usage_bound metadataTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.specification (ihMetadata depth binding bound bindingValid) (ihExtension depth binding bound bindingValid) mPure ePure)
  · intro context spec target specType targetType su tu specTyped targetTyped sPure tPure ihSpec ihTarget depth binding bound bindingValid
    have counts := add_uses_insert su tu depth ((source_uses_length specTyped).trans (source_uses_length targetTyped).symm) (insert_usage_bound specTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.prototype (ihSpec depth binding bound bindingValid) (ihTarget depth binding bound bindingValid) sPure tPure)
  · intro context target specType targetType uses prior ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.reflect (ih depth binding bound bindingValid))
  · intro context target metadataType extensionType uses prior ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.metadata (ih depth binding bound bindingValid))
  · intro context target specType targetType uses prior ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.project (ih depth binding bound bindingValid))
  · intro context lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped lowerCallable upperCallable captures selfShare inheritedShare middleShare ihLower ihUpper depth binding bound bindingValid
    have counts := add_uses_insert lu uu depth ((source_uses_length lowerTyped).trans (source_uses_length upperTyped).symm) (insert_usage_bound lowerTyped bound)
    have capturesNext := reusable_captures_insert assumptions.shareableVariables context (addUses lu uu) depth binding captures bound
    simpa only [Term.rename,counts] using
      (PartialTyping.mix (ihLower depth binding bound bindingValid) (ihUpper depth binding bound bindingValid)
        lowerCallable upperCallable (by simpa only [counts] using capturesNext) selfShare inheritedShare middleShare)
  · intro context spec inheritedTerm specType inherited target su iu specTyped callableEq inheritedTyped targetShare inheritedAllowed captures ihSpec ihInherited depth binding bound bindingValid
    have counts := add_uses_insert su iu depth ((source_uses_length specTyped).trans (source_uses_length inheritedTyped).symm) (insert_usage_bound specTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.fix (ihSpec depth binding bound bindingValid) callableEq (ihInherited depth binding bound bindingValid) targetShare
        (argument_allowed_insert assumptions .unrestricted context inherited iu depth binding inheritedAllowed bound)
        (reusable_captures_insert assumptions.shareableVariables context su depth binding captures bound))
  · intro context primitive left right input output lu ru primitiveEq leftTyped rightTyped ihLeft ihRight depth binding bound bindingValid
    have counts := add_uses_insert lu ru depth ((source_uses_length leftTyped).trans (source_uses_length rightTyped).symm) (insert_usage_bound leftTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.binary primitiveEq (ihLeft depth binding bound bindingValid) (ihRight depth binding bound bindingValid))
  · intro context value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe ihValue ihZero ihSuccessor depth binding bound bindingValid
    have successorBound : depth+1 ≤ (⟨.natural,.unrestricted⟩ :: context).length := by simpa using bound
    have nonempty : 0 < su.length := by rw [source_uses_length successorTyped]; simp
    have tailLength : su.tail.length = context.length := by simp [List.length_tail,source_uses_length successorTyped]
    have zeroLength := source_uses_length zeroTyped
    have firstCounts := add_uses_insert zu su.tail depth (zeroLength.trans tailLength.symm) (insert_usage_bound zeroTyped bound)
    have sumLength : (addUses zu su.tail).length = context.length := by simp [addUses,List.length_zipWith,zeroLength,tailLength]
    have allCounts := add_uses_insert vu (addUses zu su.tail) depth ((source_uses_length valueTyped).trans sumLength.symm) (insert_usage_bound valueTyped bound)
    simpa only [Term.rename,lift_shift_index,List.insertIdx_succ_cons,uses_tail_insert nonempty,firstCounts,allCounts] using
      (PartialTyping.ifZero (ihValue depth binding bound bindingValid) (ihZero depth binding bound bindingValid)
        (ihSuccessor (depth+1) binding successorBound bindingValid)
        (safe_uses_insert _ su (depth+1) binding successorSafe successorBound))
  · intro context tag payload payloadType row uses fuel payloadTyped lookup pure ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.inject (ih depth binding bound bindingValid) lookup pure)
  · intro context scrutinee arms row result su au scrutineeTyped armsTyped ihScrutinee ihArms depth binding bound bindingValid
    have counts := add_uses_insert su au depth ((source_uses_length scrutineeTyped).trans (arms_uses_length armsTyped).symm) (insert_usage_bound scrutineeTyped bound)
    simpa only [Term.rename,lift_shift_index,counts] using
      (PartialTyping.case (ihScrutinee depth binding bound bindingValid) (ihArms depth binding bound bindingValid))
  · intro context condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped ihCondition ihTrue ihFalse depth binding bound bindingValid
    have trueLength := source_uses_length trueTyped
    have falseLength := source_uses_length falseTyped
    have firstCounts := add_uses_insert tu fu depth (trueLength.trans falseLength.symm) (insert_usage_bound trueTyped bound)
    have sumLength : (addUses tu fu).length = context.length := by simp [addUses,List.length_zipWith,trueLength,falseLength]
    have allCounts := add_uses_insert cu (addUses tu fu) depth ((source_uses_length conditionTyped).trans sumLength.symm) (insert_usage_bound conditionTyped bound)
    simpa only [Term.rename,firstCounts,allCounts] using
      (PartialTyping.ifBool (ihCondition depth binding bound bindingValid) (ihTrue depth binding bound bindingValid)
        (ihFalse depth binding bound bindingValid))
  · intro context plan planType response uses planTyped isPlan isData ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.perform (ih depth binding bound bindingValid) isPlan isData)
  · intro context value planType response result uses valueTyped pure ih depth binding bound bindingValid
    simpa only [Term.rename] using
      (PartialTyping.done (planType := planType) (response := response) (ih depth binding bound bindingValid) pure)
  · intro context scrutinee arms planType response row result su au scrutineeTyped armsTyped pure ihScrutinee ihArms depth binding bound bindingValid
    have counts := add_uses_insert su au depth ((source_uses_length scrutineeTyped).trans (arms_uses_length armsTyped).symm) (insert_usage_bound scrutineeTyped bound)
    simpa only [Term.rename,lift_shift_index,counts] using
      (PartialTyping.effectCase (ihScrutinee depth binding bound bindingValid) (ihArms depth binding bound bindingValid) pure)
  · intro context depth binding bound bindingValid
    simpa only [List.map_nil,← zero_uses_insert context binding depth bound] using (FieldsTyping.nil (context.insertIdx depth binding) : FieldsTyping assumptions _ [] .emptyRow _)
  · intro context name body rest type row bu ru bodyTyped restTyped pure ihBody ihRest depth binding bound bindingValid
    have restLength := source_uses_length (PartialTyping.record restTyped)
    have counts := add_uses_insert bu ru depth ((source_uses_length bodyTyped).trans restLength.symm) (insert_usage_bound bodyTyped bound)
    simpa only [List.map_cons,counts] using
      (FieldsTyping.cons (ihBody depth binding bound bindingValid) (ihRest depth binding bound bindingValid) pure)
  · intro context result depth binding bound bindingValid
    simpa only [List.map_nil,← zero_uses_insert context binding depth bound] using
      (ArmsTyping.nil (context.insertIdx depth binding) result : ArmsTyping assumptions _ [] .emptyRow result _)
  · intro context name body rest payload row result bu ru bodyTyped safe shareable restTyped ihBody ihRest depth binding bound bindingValid
    have bodyBound : depth+1 ≤ (⟨payload,.unrestricted⟩ :: context).length := by simpa using bound
    have nonempty : 0 < bu.length := by rw [source_uses_length bodyTyped]; simp
    have tailLength : bu.tail.length = context.length := by simp [List.length_tail,source_uses_length bodyTyped]
    have counts := add_uses_insert bu.tail ru depth (tailLength.trans (arms_uses_length restTyped).symm)
      (by rw [tailLength]; exact bound)
    have bodyNext := ihBody (depth+1) binding bodyBound bindingValid
    have safeNext := safe_uses_insert _ bu (depth+1) binding safe bodyBound
    simp only [List.insertIdx_succ_cons] at bodyNext safeNext
    have combined := ArmsTyping.cons (name := name) bodyNext safeNext shareable (ihRest depth binding bound bindingValid)
    rw [uses_tail_insert nonempty,counts] at combined
    simpa only [List.map_cons] using combined

theorem shift_zero : shiftIndex 0 = Nat.succ := by funext index; simp [shiftIndex,Nat.succ_eq_add_one]

theorem source_weaken {assumptions : Assumptions} {context : Context} {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping assumptions context term type uses) (binding : Binding)
    (bindingValid : validContext assumptions.shareableVariables [binding] = true) :
    PartialTyping assumptions (binding :: context) (term.rename Nat.succ) type (0 :: uses) := by
  simpa only [shift_zero,List.insertIdx_zero] using source_insert_binding typed 0 binding (Nat.zero_le _) bindingValid

theorem reusable_zero_uses (variables : List Nat) (context : Context) :
    reusableCaptures variables context (zeroUses context) = true := by
  induction context with
  | nil => rfl
  | cons binding context ih => simpa [reusableCaptures,zeroUses,List.replicate_succ,List.zip] using ih

theorem variable_uses_cons_zero (context : Context) (binding : Binding) :
    variableUses (binding :: context) 0 = 1 :: zeroUses context := by
  simp [variableUses,zeroUses,List.range_succ_eq_map,List.map_map,Function.comp_def,List.map_const']

theorem variable_uses_cons_succ (context : Context) (binding : Binding) (index : Nat) :
    variableUses (binding :: context) (index+1) = 0 :: variableUses context index := by
  simp [variableUses,List.range_succ_eq_map,List.map_map,Function.comp_def]

theorem reusable_variable {variables : List Nat} {context : Context} {index : Nat} {binding : Binding}
    (found : context[index]? = some binding) (quantity : binding.quantity = .unrestricted)
    (shareable : binding.type.shareableUnder variables = true) :
    reusableCaptures variables context (variableUses context index) = true := by
  induction context generalizing index with
  | nil => simp at found
  | cons first rest ih =>
      cases index with
      | zero =>
          have same : first = binding := by simpa using found
          subst first
          have head : (1 == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true := by simp [quantity,shareable]
          simpa [variable_uses_cons_zero,reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using And.intro head (reusable_zero_uses variables rest)
      | succ index =>
          have tail : rest[index]? = some binding := by simpa using found
          simpa [variable_uses_cons_succ,reusableCaptures,List.zip] using ih tail

theorem reusable_count_add (quantity : Quantity) (shareable : Bool) (first second : Nat)
    (left : (first == 0 || (quantity == .unrestricted && shareable)) = true)
    (right : (second == 0 || (quantity == .unrestricted && shareable)) = true) :
    (first+second == 0 || (quantity == .unrestricted && shareable)) = true := by
  by_cases firstZero : first = 0
  · simpa [firstZero] using right
  · simpa [firstZero] using left

theorem reusable_count_add_left (quantity : Quantity) (shareable : Bool) (first second : Nat)
    (combined : (first+second == 0 || (quantity == .unrestricted && shareable)) = true) :
    (first == 0 || (quantity == .unrestricted && shareable)) = true := by
  by_cases firstZero : first = 0
  · simp [firstZero]
  · have sumNonzero : first+second ≠ 0 := by omega
    simpa [firstZero,sumNonzero] using combined

theorem reusable_add_uses (variables : List Nat) (context : Context) (first second : Uses)
    (left : reusableCaptures variables context first = true)
    (right : reusableCaptures variables context second = true) :
    reusableCaptures variables context (addUses first second) = true := by
  induction context generalizing first second with
  | nil =>
      have firstEmpty : first = [] := by simpa [reusableCaptures] using left
      subst first; rfl
  | cons binding context ih =>
      cases first with
      | nil => simp [reusableCaptures] at left
      | cons first firsts =>
        cases second with
        | nil => simp [reusableCaptures] at right
        | cons second seconds =>
          have lf : (first == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true ∧ reusableCaptures variables context firsts = true := by
            simpa [reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using left
          have rf : (second == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true ∧ reusableCaptures variables context seconds = true := by
            simpa [reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using right
          simpa [reusableCaptures,addUses,List.zipWith,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using
            And.intro (reusable_count_add _ _ first second lf.1 rf.1) (ih firsts seconds lf.2 rf.2)

theorem reusable_add_uses_left (variables : List Nat) (context : Context) (first second : Uses)
    (firstLength : first.length = context.length) (secondLength : second.length = context.length)
    (combined : reusableCaptures variables context (addUses first second) = true) :
    reusableCaptures variables context first = true := by
  induction context generalizing first second with
  | nil => cases first with | nil => rfl | cons head tail => simp at firstLength
  | cons binding context ih =>
      cases first with
      | nil => simp at firstLength
      | cons first firsts =>
        cases second with
        | nil => simp at secondLength
        | cons second seconds =>
          have fl : firsts.length = context.length := Nat.succ.inj firstLength
          have sl : seconds.length = context.length := Nat.succ.inj secondLength
          have facts : (first+second == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true ∧
              reusableCaptures variables context (addUses firsts seconds) = true := by
            simpa [reusableCaptures,addUses,List.zipWith,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm,fl,sl] using combined
          simpa [reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using
            And.intro (reusable_count_add_left _ _ first second facts.1) (ih firsts seconds fl sl facts.2)

theorem reusable_uses_safe (variables : List Nat) (context : Context) (uses : Uses)
    (captures : reusableCaptures variables context uses = true) : safeUses context uses = true := by
  induction context generalizing uses with
  | nil => cases uses <;> simp_all [safeUses,reusableCaptures]
  | cons binding context ih =>
      cases uses with
      | nil => simp [reusableCaptures] at captures
      | cons count uses =>
          have facts : (count == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true ∧ reusableCaptures variables context uses = true := by
            simpa [reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using captures
          have head : safeQuantity binding.quantity count = true := by
            simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at facts
            rcases facts.1 with zero | ⟨unrestricted,share⟩
            · subst count; exact safe_quantity_zero _
            · rw [unrestricted]; rfl
          simpa [safeUses,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using And.intro head (ih uses facts.2)

theorem reusable_tail {variables : List Nat} {binding : Binding} {context : Context} {uses : Uses}
    (captures : reusableCaptures variables (binding :: context) uses = true) :
    reusableCaptures variables context uses.tail = true := by
  cases uses with
  | nil => simp [reusableCaptures] at captures
  | cons head tail =>
      have facts : (head == 0 || (binding.quantity == .unrestricted && binding.type.shareableUnder variables)) = true ∧ reusableCaptures variables context tail = true := by
        simpa [reusableCaptures,List.zip,List.all_cons,and_assoc,and_left_comm,and_comm] using captures
      exact facts.2

structure ReusableTerm (assumptions : Assumptions) (context : Context) (term : Term) (type : Ty) where
  uses : Uses
  derivation : PartialTyping assumptions context term type uses
  captures : reusableCaptures assumptions.shareableVariables context uses = true

def ReusableTerm.weaken {assumptions : Assumptions} {context : Context} {term : Term} {type : Ty}
    (typed : ReusableTerm assumptions context term type) (binding : Binding)
    (valid : validContext assumptions.shareableVariables [binding] = true) :
    ReusableTerm assumptions (binding :: context) (term.rename Nat.succ) type :=
  ⟨0::typed.uses,source_weaken typed.derivation binding valid,
    by simpa only [List.insertIdx_zero] using reusable_captures_insert assumptions.shareableVariables context typed.uses 0 binding typed.captures (Nat.zero_le _)⟩

def ReusableTerm.«variable» {assumptions : Assumptions} {context : Context} {index : Nat} {binding : Binding}
    (found : context[index]? = some binding) (quantity : binding.quantity = .unrestricted)
    (shareable : binding.type.shareableUnder assumptions.shareableVariables = true) :
    ReusableTerm assumptions context (.bound index) binding.type :=
  ⟨variableUses context index,.bound found,reusable_variable found quantity shareable⟩

def ReusableTerm.apply {assumptions : Assumptions} {context : Context}
    {function argument : Term} {functionType domain codomain : Ty} {reuse : Reuse}
    (fn : ReusableTerm assumptions context function functionType) (arg : ReusableTerm assumptions context argument domain)
    (callableEq : callable functionType = .arrow reuse .unrestricted domain codomain)
    (shareable : domain.shareableUnder assumptions.shareableVariables = true) :
    ReusableTerm assumptions context (.app function argument) codomain :=
  ⟨addUses fn.uses arg.uses,.application fn.derivation arg.derivation callableEq rfl
    (by simpa [argumentAllowed,shareable,Ty.shareableUnder_not_computation _ _ shareable] using arg.captures),
    reusable_add_uses assumptions.shareableVariables context fn.uses arg.uses fn.captures arg.captures⟩

def ReusableTerm.abstraction {assumptions : Assumptions} {context : Context} {body : Term}
    {domain codomain : Ty} {quantity : Quantity}
    (bodyTyped : ReusableTerm assumptions (⟨domain,quantity⟩ :: context) body codomain)
    (valid : validContext assumptions.shareableVariables (⟨domain,quantity⟩ :: context) = true) :
    ReusableTerm assumptions context (.lam body) (.arrow .reusable quantity domain codomain) :=
  ⟨bodyTyped.uses.tail,.lambda (annotation := ⟨domain,codomain,quantity,.reusable⟩) bodyTyped.derivation (reusable_uses_safe _ _ _ bodyTyped.captures) valid
    (by simpa [reusableAllowed] using reusable_tail bodyTyped.captures),reusable_tail bodyTyped.captures⟩

theorem source_weaken_twice {assumptions : Assumptions} {context : Context} {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping assumptions context term type uses) (first second : Binding)
    (firstValid : validContext assumptions.shareableVariables [first] = true)
    (secondValid : validContext assumptions.shareableVariables [second] = true) :
    PartialTyping assumptions (second :: first :: context) (term.rename (fun index => index+2)) type (0::0::uses) := by
  have shifted := source_weaken (source_weaken typed first firstValid) second secondValid
  have equation := ObjectiveBendDemandAdequacy.scoped_rename_comp (source_scoped typed) Nat.succ Nat.succ
  simpa [equation,Nat.succ_eq_add_one,Nat.add_assoc] using shifted

theorem add_zero_uses (context : Context) (uses : Uses) (length : uses.length = context.length) :
    addUses uses (zeroUses context) = uses := by
  induction context generalizing uses with
  | nil => cases uses <;> simp_all [addUses,zeroUses]
  | cons binding context ih =>
      cases uses with
      | nil => simp at length
      | cons head tail =>
        have tailLength : tail.length = context.length := Nat.succ.inj length
        simpa [addUses,zeroUses,List.replicate_succ,List.zipWith] using congrArg (List.cons head) (ih tail tailLength)

theorem add_uses_comm (first second : Uses) : addUses first second = addUses second first := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons head tail ih =>
      cases second with
      | nil => rfl
      | cons other rest =>
        simp only [addUses,List.zipWith]
        rw [Nat.add_comm head other]
        congr 1
        exact ih rest

def ReusableTerm.shiftTwo {assumptions : Assumptions} {context : Context} {term : Term} {type : Ty}
    (typed : ReusableTerm assumptions context term type) (first second : Binding)
    (firstValid : validContext assumptions.shareableVariables [first] = true)
    (secondValid : validContext assumptions.shareableVariables [second] = true) :
    ReusableTerm assumptions (second :: first :: context) (term.rename (fun index => index+2)) type :=
  ⟨0::0::typed.uses,source_weaken_twice typed.derivation first second firstValid secondValid,
    by
      have once := reusable_captures_insert assumptions.shareableVariables context typed.uses 0 first typed.captures (Nat.zero_le _)
      simp only [List.insertIdx_zero] at once
      simpa only [List.insertIdx_zero] using
        reusable_captures_insert assumptions.shareableVariables (first :: context) (0::typed.uses) 0 second once (Nat.zero_le _)⟩

/-- The actual mix-generated lexical body is reusable under the checked operand
capture premise. Both generated parameters retain their shareability evidence;
composition does not make an affine captured environment duplicable. -/
def reusable_mix_body {assumptions : Assumptions} {context : Context} {lower upper : Term}
    {lowerType upperType self inherited middle provided : Ty} {lu uu : Uses}
    (lowerTyped : PartialTyping assumptions context lower lowerType lu)
    (upperTyped : PartialTyping assumptions context upper upperType uu)
    (lowerCallable : callable lowerType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle))
    (upperCallable : callable upperType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted middle provided))
    (captures : reusableCaptures assumptions.shareableVariables context (addUses lu uu) = true)
    (selfShare : self.shareableUnder assumptions.shareableVariables = true)
    (inheritedShare : inherited.shareableUnder assumptions.shareableVariables = true)
    (middleShare : middle.shareableUnder assumptions.shareableVariables = true)
    (contextValid : validContext assumptions.shareableVariables context = true) :
    ReusableTerm assumptions context (mixBody lower upper)
      (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided)) := by
  let selfBinding : Binding := ⟨self,.unrestricted⟩
  let inheritedBinding : Binding := ⟨inherited,.unrestricted⟩
  have selfValid : validContext assumptions.shareableVariables [selfBinding] = true := by simp [validContext,selfBinding,selfShare]
  have inheritedValid : validContext assumptions.shareableVariables [inheritedBinding] = true := by simp [validContext,inheritedBinding,inheritedShare]
  have oneValid : validContext assumptions.shareableVariables (selfBinding :: context) = true := by
    simpa [validContext,selfBinding,selfShare] using contextValid
  have twoValid : validContext assumptions.shareableVariables (inheritedBinding :: selfBinding :: context) = true := by
    simpa [validContext,inheritedBinding,inheritedShare] using oneValid
  have lowerCaptures := reusable_add_uses_left assumptions.shareableVariables context lu uu (source_uses_length lowerTyped) (source_uses_length upperTyped) captures
  have upperCaptures := reusable_add_uses_left assumptions.shareableVariables context uu lu (source_uses_length upperTyped) (source_uses_length lowerTyped) (by simpa only [add_uses_comm] using captures)
  let lowerReusable : ReusableTerm assumptions context lower lowerType := ⟨lu,lowerTyped,lowerCaptures⟩
  let upperReusable : ReusableTerm assumptions context upper upperType := ⟨uu,upperTyped,upperCaptures⟩
  let lowerShifted := lowerReusable.shiftTwo selfBinding inheritedBinding selfValid inheritedValid
  let upperShifted := upperReusable.shiftTwo selfBinding inheritedBinding selfValid inheritedValid
  let selfTerm : ReusableTerm assumptions (inheritedBinding :: selfBinding :: context) (.bound 1) self :=
    ReusableTerm.«variable» (binding := selfBinding) rfl rfl selfShare
  let inheritedTerm : ReusableTerm assumptions (inheritedBinding :: selfBinding :: context) (.bound 0) inherited :=
    ReusableTerm.«variable» (binding := inheritedBinding) rfl rfl inheritedShare
  let lowerSelf := lowerShifted.apply selfTerm lowerCallable selfShare
  let upperSelf := upperShifted.apply selfTerm upperCallable selfShare
  let lowerInherited := lowerSelf.apply inheritedTerm rfl inheritedShare
  let body := upperSelf.apply lowerInherited rfl middleShare
  exact (body.abstraction twoValid).abstraction oneValid

/-- The suspended knot created by Fix is typed using the same recursive address
as both the lexical self binding and the resulting target. No evaluation or
termination of that knot is required by this construction. -/
def reusable_fix_body {assumptions : Assumptions} {context : Context} {spec seed : Term}
    {specType inherited target : Ty} {su iu : Uses}
    (specTyped : PartialTyping assumptions context spec specType su)
    (specCallable : callable specType = .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited target))
    (seedTyped : PartialTyping assumptions context seed inherited iu)
    (targetShare : target.shareableUnder assumptions.shareableVariables = true)
    (seedAllowed : argumentAllowed assumptions .unrestricted context inherited iu = true)
    (specCaptures : reusableCaptures assumptions.shareableVariables context su = true) :
    ReusableTerm assumptions (⟨target,.unrestricted⟩ :: context)
      (.app (.app (spec.rename Nat.succ) (.bound 0)) (seed.rename Nat.succ)) target := by
  obtain ⟨-,seedFacts⟩ : inherited.isComputation = false ∧ (inherited.shareableUnder assumptions.shareableVariables = true ∧
      reusableCaptures assumptions.shareableVariables context iu = true) := by
    simpa [argumentAllowed] using seedAllowed
  let binding : Binding := ⟨target,.unrestricted⟩
  have valid : validContext assumptions.shareableVariables [binding] = true := by simp [validContext,binding,targetShare]
  let specReusable : ReusableTerm assumptions context spec specType := ⟨su,specTyped,specCaptures⟩
  let seedReusable : ReusableTerm assumptions context seed inherited := ⟨iu,seedTyped,seedFacts.2⟩
  let selfTerm : ReusableTerm assumptions (binding :: context) (.bound 0) target :=
    ReusableTerm.«variable» (binding := binding) rfl rfl targetShare
  exact ((specReusable.weaken binding valid).apply selfTerm specCallable targetShare).apply
    (seedReusable.weaken binding valid) rfl seedFacts.1

theorem stack_convert_path {assumptions : Assumptions} {types : AddressTypes}
    {first last result : Ty} {stack : List Frame}
    (path : ConversionPath assumptions first last)
    (continuation : StackTyping assumptions types stack last result) :
    StackTyping assumptions types stack first result := by
  induction path with
  | refl => exact continuation
  | step prior agreement ih => exact ih (.conversion agreement continuation)

/-- Variable source derivations disclose the actual environment binding even
when the authored result has crossed one or several row/alias conversions. -/
theorem source_bound_assignment {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .bound index => ∃ binding, context[index]? = some binding ∧
        ConversionPath assumptions binding.type type
    | _ => True := by
  refine PartialTyping.rec
    (motive_1 := fun context term type _ _ => match term with
      | .bound index => ∃ binding, context[index]? = some binding ∧
          ConversionPath assumptions binding.type type
      | _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
  · intro context index binding found; exact ⟨binding,found,.refl binding.type⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro context term actual expected uses prior agreement ih
    cases term <;> try trivial
    obtain ⟨binding,found,path⟩ := ih
    exact ⟨binding,found,.step path agreement⟩
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
  · intros; trivial
  · intros; trivial


theorem source_mix_expansion {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .mix lower upper => validContext assumptions.shareableVariables context = true →
        Nonempty (ReusableTerm assumptions context (mixBody lower upper) type)
    | _ => True := by
  refine PartialTyping.rec
    (motive_1 := fun context term type _ _ => match term with
      | .mix lower upper => validContext assumptions.shareableVariables context = true →
          Nonempty (ReusableTerm assumptions context (mixBody lower upper) type)
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
    intro valid
    obtain ⟨expanded⟩ := ih valid
    exact ⟨⟨expanded.uses,.conversion expanded.derivation agreement,expanded.captures⟩⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro context lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped lowerCallable upperCallable captures selfShare inheritedShare middleShare ihLower ihUpper valid
    exact ⟨reusable_mix_body lowerTyped upperTyped lowerCallable upperCallable captures selfShare inheritedShare middleShare valid⟩
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


/-- Evaluating every checked mix, including source result conversions, preserves
its actual lexical capture qualification and the executor's generated body. -/
theorem typed_mix_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {lower upper : Term} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    obtain ⟨expanded⟩ := source_mix_expansion origin.source origin.contextValid
    let next : ClosureTyping assumptions types ⟨mixBody lower upper,environment⟩ typed.current :=
      ⟨origin.context,expanded.uses,origin.environment,expanded.derivation,
        reusable_uses_safe _ _ _ expanded.captures,origin.contextValid⟩
    refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
    · simpa [stepRaw,evaluate] using typed.heap
    · simpa [stepRaw,evaluate] using (ControlTyping.evaluate next)
    · simpa [stepRaw,evaluate] using typed.stack

theorem source_fix_expansion {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .fix spec seed => ∃ target,
        target.shareableUnder assumptions.shareableVariables = true ∧
        Nonempty (ReusableTerm assumptions (⟨target,.unrestricted⟩ :: context)
          (.app (.app (spec.rename Nat.succ) (.bound 0)) (seed.rename Nat.succ)) target) ∧
        ConversionPath assumptions target type
    | _ => True := by
  refine PartialTyping.rec
    (motive_1 := fun context term type _ _ => match term with
      | .fix spec seed => ∃ target,
          target.shareableUnder assumptions.shareableVariables = true ∧
          Nonempty (ReusableTerm assumptions (⟨target,.unrestricted⟩ :: context)
            (.app (.app (spec.rename Nat.succ) (.bound 0)) (seed.rename Nat.succ)) target) ∧
          ConversionPath assumptions target type
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
    obtain ⟨target,share,expanded,path⟩ := ih
    exact ⟨target,share,expanded,.step path agreement⟩
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
  · intro context spec seed specType inherited target su iu specTyped callableEq seedTyped share allowed captures ihSpec ihSeed
    exact ⟨target,share,⟨reusable_fix_body specTyped callableEq seedTyped share allowed captures⟩,.refl target⟩
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


/-- Generic Fix preserves typed address assignments at its actual cyclic
allocation. The suspended origin contains the new address, preserving the
recursive self type and capture quantities without any termination premise. -/
theorem typed_fix_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {spec seed : Term} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.fix spec seed) environment) :
    ∃ after, TypeExtension types after ∧
      Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    obtain ⟨target,share,⟨expanded⟩,path⟩ := source_fix_expansion origin.source
    let after := types ++ [target]
    have extension : TypeExtension types after := type_extension_append types [target]
    have assigned : after[state.heap.size]? = some target := by
      rw [← typed.heap.length]
      simp [after]
    have valid : validContext assumptions.shareableVariables (⟨target,.unrestricted⟩ :: origin.context) = true := by
      simpa [validContext,share] using origin.contextValid
    let next : ClosureTyping assumptions after
        ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (seed.rename Nat.succ),state.heap.size :: environment⟩ target :=
      ⟨⟨target,.unrestricted⟩ :: origin.context,expanded.uses,
        (origin.environment.weaken extension).cons assigned,expanded.derivation,
        reusable_uses_safe _ _ _ expanded.captures,valid⟩
    refine ⟨after,extension,⟨step_alloc_certificate typed after target ?_ ?_ ?_⟩⟩
    · simpa [stepRaw,evaluate] using
        heap_typed_push typed.heap (CellTyping.suspended next (Ty.shareableUnder_not_computation _ _ share))
    · simpa [stepRaw,evaluate] using (ControlTyping.enter assigned)
    · simpa [stepRaw,evaluate] using
        (StackTyping.weaken extension (stack_convert_path path typed.stack))

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

/-- Bound-variable demand preserves the actual immutable address type; source
conversions move into the continuation instead of retyping the heap identity. -/
theorem typed_bound_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {index : Nat} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.bound index) environment) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    obtain ⟨binding,found,path⟩ := source_bound_assignment origin.source
    obtain ⟨address,environmentFound,assigned⟩ := origin.environment.binding index binding found
    refine ⟨step_certificate typed binding.type ?_ ?_ ?_⟩
    · simpa [stepRaw,evaluate,environmentFound] using typed.heap
    · simpa [stepRaw,evaluate,environmentFound] using (ControlTyping.enter assigned)
    · simpa [stepRaw,evaluate,environmentFound] using (stack_convert_path path typed.stack)

theorem safe_add_uses_right (context : Context) (first second : Uses)
    (firstLength : first.length = context.length) (secondLength : second.length = context.length)
    (safe : safeUses context (addUses first second) = true) : safeUses context second = true := by
  rw [add_uses_comm] at safe
  exact safe_add_uses_left context second first secondLength firstLength safe

/-- Application inversion retains the actual copy-argument guard and a finite
conversion path for the authored result type. -/
theorem source_application_decomposition {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    match term with
    | .app function argument => ∃ functionType domain codomain functionUses argumentUses reuse quantity,
        PartialTyping assumptions context function functionType functionUses ∧
        PartialTyping assumptions context argument domain argumentUses ∧
        callable functionType = .arrow reuse quantity domain codomain ∧
        argumentAllowed assumptions quantity context domain argumentUses = true ∧
        uses = addUses functionUses argumentUses ∧ ConversionPath assumptions codomain type
    | _ => True := by
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .app function argument => ∃ functionType domain codomain functionUses argumentUses reuse quantity,
          PartialTyping assumptions context function functionType functionUses ∧
          PartialTyping assumptions context argument domain argumentUses ∧
          callable functionType = .arrow reuse quantity domain codomain ∧
          argumentAllowed assumptions quantity context domain argumentUses = true ∧
          uses = addUses functionUses argumentUses ∧ ConversionPath assumptions codomain type
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
    obtain ⟨ft,domain,codomain,fu,au,reuse,quantity,fn,arg,callable,copyAllowed,counts,path⟩ := ih
    exact ⟨ft,domain,codomain,fu,au,reuse,quantity,fn,arg,callable,copyAllowed,counts,.step path agreement⟩
  · intro context function argument functionType argumentType domain codomain fu au reuse quantity fn arg callable same copyAllowed ihFn ihArg
    subst argumentType
    exact ⟨functionType,domain,codomain,fu,au,reuse,quantity,fn,arg,callable,copyAllowed,rfl,.refl codomain⟩
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
  · intros; trivial


/-- Focusing the function of ANY well-typed application keeps both lexical
origins, safely splits the usage vector, and retains copy/shareability evidence
on the actual argument continuation. -/
theorem typed_application_focus_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {function argument : Term} {environment : Environment}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate (.app function argument) environment) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    obtain ⟨ft,domain,codomain,fu,au,reuse,quantity,fn,arg,callable,copyAllowed,counts,path⟩ :=
      source_application_decomposition origin.source
    have safe : safeUses origin.context (addUses fu au) = true := by simpa [counts] using origin.safe
    have fnSafe := safe_add_uses_left origin.context fu au (source_uses_length fn) (source_uses_length arg) safe
    have argSafe := safe_add_uses_right origin.context fu au (source_uses_length fn) (source_uses_length arg) safe
    let fnOrigin : ClosureTyping assumptions types ⟨function,environment⟩ ft :=
      ⟨origin.context,fu,origin.environment,fn,fnSafe,origin.contextValid⟩
    let argOrigin : ClosureTyping assumptions types ⟨argument,environment⟩ domain :=
      ⟨origin.context,au,origin.environment,arg,argSafe,origin.contextValid⟩
    refine ⟨step_certificate typed ft ?_ ?_ ?_⟩
    · simpa [stepRaw,evaluate] using typed.heap
    · simpa [stepRaw,evaluate] using (ControlTyping.evaluate fnOrigin)
    · simpa [stepRaw,evaluate] using
        (StackTyping.cons (FrameTyping.argument argOrigin callable copyAllowed) (stack_convert_path path typed.stack))

def sourceFocus (term : Term) (environment : Environment) : Option (Term × Frame) :=
  match term with
  | .get target name => some (target,.field name)
  | .reflect target => some (target,.reflect)
  | .metadata target => some (target,.metadata)
  | .project target => some (target,.project)
  | .extend target fields => some (target,.extend fields environment)
  | .binary primitive left right => some (left,.binaryLeft primitive right environment)
  | .ifZero value zero successor => some (value,.condition zero successor environment)
  | .case scrutinee arms => some (scrutinee,.case arms environment)
  | .ifBool condition whenTrue whenFalse => some (condition,.ifBool whenTrue whenFalse environment)
  | _ => none

structure FocusedSource (assumptions : Assumptions) (types : AddressTypes)
    (target : Term) (environment : Environment) (frame : Frame) (expected : Ty) where
  current : Ty
  output : Ty
  origin : ClosureTyping assumptions types ⟨target,environment⟩ current
  continuation : FrameTyping assumptions types frame current output
  result : ConversionPath assumptions output expected

/-- Source projections and overlays carry their actual demanded origin and
continuation typing, retaining lexical quantities and finite conversion paths. -/
theorem source_focus_typed {assumptions : Assumptions} {context : Context}
    {term : Term} {type : Ty} {uses : Uses}
    (source : PartialTyping assumptions context term type uses) :
    ∀ types environment, EnvironmentTyping types context environment →
      safeUses context uses = true → validContext assumptions.shareableVariables context = true →
      match sourceFocus term environment with
      | some (target,frame) => Nonempty (FocusedSource assumptions types target environment frame type)
      | none => True := by
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ => ∀ types environment,
      EnvironmentTyping types context environment → safeUses context uses = true →
      validContext assumptions.shareableVariables context = true →
      match sourceFocus term environment with
      | some (target,frame) => Nonempty (FocusedSource assumptions types target environment frame type)
      | none => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
  · intros; simp [sourceFocus]
  · intros; simp [sourceFocus]
  · intros; simp [sourceFocus]
  · intros; simp [sourceFocus]
  · intros; simp [sourceFocus]
  · intro context term actual expected uses prior agreement ih types environment environmentTyped safe valid
    have focused := ih types environment environmentTyped safe valid
    cases found : sourceFocus term environment with
    | none => trivial
    | some pair =>
      obtain ⟨target,frame⟩ := pair
      rw [found] at focused
      obtain ⟨data⟩ := focused
      exact ⟨⟨data.current,data.output,data.origin,data.continuation,.step data.result agreement⟩⟩
  · intros; simp [sourceFocus]
  · intros; simp [sourceFocus]
  · intro context target targetType member uses name fuel targetTyped lookup ih types environment environmentTyped safe valid
    exact ⟨⟨targetType,member,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.field lookup,.refl member⟩⟩
  · intro context target fields targetType row targetUses fieldUses targetTyped fieldsTyped rowValid ihTarget ihFields types environment environmentTyped safe valid
    have targetSafe := safe_add_uses_left context targetUses fieldUses (source_uses_length targetTyped)
      (source_uses_length (PartialTyping.record fieldsTyped)) safe
    have fieldsSafe := safe_add_uses_right context targetUses fieldUses (source_uses_length targetTyped)
      (source_uses_length (PartialTyping.record fieldsTyped)) safe
    exact ⟨⟨targetType,overlay row targetType,⟨context,targetUses,environmentTyped,targetTyped,targetSafe,valid⟩,
      .extend environmentTyped fieldsTyped fieldsSafe valid rowValid,.refl _⟩⟩
  · intros; simp [sourceFocus]
  · intros; simp [sourceFocus]
  · intro context target specType targetType uses targetTyped ih types environment environmentTyped safe valid
    exact ⟨⟨.prototype specType targetType,specType,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.reflect _ _,.refl _⟩⟩
  · intro context target metadataType extensionType uses targetTyped ih types environment environmentTyped safe valid
    exact ⟨⟨.specification metadataType extensionType,metadataType,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.metadata _ _,.refl _⟩⟩
  · intro context target specType targetType uses targetTyped ih types environment environmentTyped safe valid
    exact ⟨⟨.prototype specType targetType,targetType,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.project _ _,.refl _⟩⟩
  · intros; simp [sourceFocus]
  · intros; simp [sourceFocus]
  · intro context primitive left right input output lu ru primitiveEq leftTyped rightTyped ihLeft ihRight types environment environmentTyped safe valid
    have leftSafe := safe_add_uses_left context lu ru (source_uses_length leftTyped) (source_uses_length rightTyped) safe
    have rightSafe := safe_add_uses_right context lu ru (source_uses_length leftTyped) (source_uses_length rightTyped) safe
    have inputEq : (primitiveTypes primitive).1 = input := congrArg Prod.fst primitiveEq
    have outputEq : (primitiveTypes primitive).2 = output := congrArg Prod.snd primitiveEq
    let rightOrigin : ClosureTyping assumptions types ⟨right,environment⟩ input :=
      ⟨context,ru,environmentTyped,rightTyped,rightSafe,valid⟩
    have rightOrigin' : ClosureTyping assumptions types ⟨right,environment⟩ (primitiveTypes primitive).1 := by
      rw [inputEq]; exact rightOrigin
    have frame : FrameTyping assumptions types (.binaryLeft primitive right environment) input output := by
      simpa only [inputEq,outputEq] using FrameTyping.binaryLeft rightOrigin'
    exact ⟨⟨input,output,⟨context,lu,environmentTyped,leftTyped,leftSafe,valid⟩,frame,.refl _⟩⟩
  · intro context value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe ihValue ihZero ihSuccessor types environment environmentTyped safe valid
    have vuLength := source_uses_length valueTyped
    have zuLength := source_uses_length zeroTyped
    have suLength : su.tail.length = context.length := by simp [List.length_tail,source_uses_length successorTyped]
    have branchLength : (addUses zu su.tail).length = context.length := by
      simp [addUses,List.length_zipWith,zuLength,suLength]
    have valueSafe := safe_add_uses_left context vu (addUses zu su.tail) vuLength branchLength safe
    have branchSafe := safe_add_uses_right context vu (addUses zu su.tail) vuLength branchLength safe
    have zeroSafe := safe_add_uses_left context zu su.tail zuLength suLength branchSafe
    let zeroOrigin : ClosureTyping assumptions types ⟨zero,environment⟩ result :=
      ⟨context,zu,environmentTyped,zeroTyped,zeroSafe,valid⟩
    exact ⟨⟨.natural,result,⟨context,vu,environmentTyped,valueTyped,valueSafe,valid⟩,
      .condition zeroOrigin environmentTyped successorTyped successorSafe valid,.refl _⟩⟩
  · intros; simp [sourceFocus]
  · intro context scrutinee arms row result su au scrutineeTyped armsTyped ihScrutinee ihArms types environment environmentTyped safe valid
    have scrutineeSafe := safe_add_uses_left context su au (source_uses_length scrutineeTyped) (arms_uses_length armsTyped) safe
    exact ⟨⟨.variant row,result,⟨context,su,environmentTyped,scrutineeTyped,scrutineeSafe,valid⟩,
      .case environmentTyped armsTyped valid,.refl _⟩⟩
  · intro context condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped ihCondition ihTrue ihFalse types environment environmentTyped safe valid
    have cuLength := source_uses_length conditionTyped
    have tuLength := source_uses_length trueTyped
    have fuLength := source_uses_length falseTyped
    have branchLength : (addUses tu fu).length = context.length := by
      simp [addUses,List.length_zipWith,tuLength,fuLength]
    have conditionSafe := safe_add_uses_left context cu (addUses tu fu) cuLength branchLength safe
    have branchSafe := safe_add_uses_right context cu (addUses tu fu) cuLength branchLength safe
    have trueSafe := safe_add_uses_left context tu fu tuLength fuLength branchSafe
    have falseSafe := safe_add_uses_right context tu fu tuLength fuLength branchSafe
    exact ⟨⟨.boolean,result,⟨context,cu,environmentTyped,conditionTyped,conditionSafe,valid⟩,
      .ifBool ⟨context,tu,environmentTyped,trueTyped,trueSafe,valid⟩ ⟨context,fu,environmentTyped,falseTyped,falseSafe,valid⟩,.refl _⟩⟩
  · intros; simp [sourceFocus]
  · intros; simp [sourceFocus]
  · intro context scrutinee arms planType response row result su au scrutineeTyped armsTyped pure ihScrutinee ihArms types environment environmentTyped safe valid
    have scrutineeSafe := safe_add_uses_left context su au (source_uses_length scrutineeTyped) (arms_uses_length armsTyped) safe
    exact ⟨⟨.computation planType response (.variant row),.computation planType response result,
      ⟨context,su,environmentTyped,scrutineeTyped,scrutineeSafe,valid⟩,
      .effectCase environmentTyped armsTyped valid pure,.refl _⟩⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- Focusing projection/overlay, binary and conditional source forms preserves the typed stack
at the exact raw-machine step; no source annotation or row oracle is assumed. -/
theorem typed_source_focus_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {term target : Term} {environment : Environment} {frame : Frame}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate term environment)
    (focus : sourceFocus term environment = some (target,frame)) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have control := typed.control
  rw [evaluate] at control
  cases control with
  | evaluate origin =>
    have focused := source_focus_typed origin.source types environment origin.environment origin.safe origin.contextValid
    rw [focus] at focused
    obtain ⟨data⟩ := focused
    have next : stepRaw state = {state with control := .evaluate target environment,stack := frame :: state.stack} := by
      cases term <;> simp [sourceFocus] at focus
      all_goals
        obtain ⟨rfl,rfl⟩ := focus
        simp [stepRaw,evaluate]
    refine ⟨step_certificate typed data.current ?_ ?_ ?_⟩
    · simpa [next] using typed.heap
    · simpa [next] using ControlTyping.evaluate data.origin
    · simpa [next] using StackTyping.cons data.continuation (stack_convert_path data.result typed.stack)

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

theorem record_value_form {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {row : Ty} (typed : ValueTyping assumptions types value row)
    (fuel : Nat) (isRow : row.isRow assumptions.bounds fuel = true) :
    ∃ fields, value = .record fields := by
  obtain ⟨head,normal,kind⟩ := value_head_correct typed
  obtain ⟨rowHead,rowNormal,rowKind⟩ := row_head_normalizes assumptions.bounds fuel row isRow
  have equal := head_normalizes_unique normal rowNormal
  subst head
  have shape : valueHead value = .row := kind.symm.trans rowKind
  cases value with
  | record fields => exact ⟨fields,rfl⟩
  | _ => cases shape

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

/-- Evaluating any immediate source value preserves its assigned result type,
including captured reusable/once lambdas and both String and Bool scalars. -/
theorem typed_immediate_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {term : Term} {environment : Environment} {value : RuntimeValue}
    (typed : StateTyping assumptions types state result)
    (evaluate : state.control = .evaluate term environment)
    (immediate : immediateValue term environment = some value) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [evaluate] at control
    cases control with
    | evaluate closure => exact immediate_value_typed closure.source types environment closure.environment value immediate
  have next : stepRaw state = {state with control := .returned value} := by
    cases term <;> simp [immediateValue,scalarValue] at immediate
    all_goals subst value; simp [stepRaw,evaluate]
  refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
  · simpa [next] using typed.heap
  · simpa [next] using (ControlTyping.returned valueTyped)
  · simpa [next] using typed.stack

/-- Source conversions may sit above an update continuation. Transport the
returned value across those exact boundaries before storing it at the immutable
address representative; conversion cannot change the heap assignment. -/
theorem stack_update_value {assumptions : Assumptions} {types : AddressTypes}
    {stack : List Frame} {input result : Ty} {value : RuntimeValue}
    (continuation : StackTyping assumptions types stack input result)
    (valueTyped : ValueTyping assumptions types value input) :
    ∀ address rest, stack = .update address :: rest →
      ∃ addressType, types[address]? = some addressType ∧
        ValueTyping assumptions types value addressType ∧
        StackTyping assumptions types rest addressType result := by
  induction continuation with
  | nil type => intro address rest impossible; simp at impossible
  | cons frame restTyped =>
      intro address rest same
      cases same
      cases frame with
      | update assigned _ => exact ⟨_,assigned,valueTyped,restTyped⟩
  | conversion agreement restTyped ih =>
      exact ih (.conversion valueTyped agreement)
  | returns pure restTyped ih =>
      intro address rest same
      obtain ⟨_,_,impossible⟩ := stack_activity_head restTyped rfl _ _ same
      cases impossible

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

/-- Updating a demanded thunk stores a value of the thunk's original assigned
source type. BusyInvariant supplies the actual evaluating origin; no arbitrary
update-validity oracle is needed. -/
theorem typed_update_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {address : Address} {value : RuntimeValue} {rest : List Frame}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value)
    (stack : state.stack = .update address :: rest) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  obtain ⟨addressType,assigned,addressValue,restTyped⟩ :=
    stack_update_value typed.stack valueTyped address rest stack
  obtain ⟨origin,found⟩ := ObjectiveBendDemandInvariant.busy_update_exists typed.busy stack
  obtain ⟨cell,found',cellTyped⟩ := typed.heap.cell address addressType assigned
  have same : cell = .evaluating origin := Option.some.inj (found'.symm.trans found)
  rw [same] at cellTyped
  cases cellTyped with
  | evaluating originTyped addressPure =>
    refine ⟨step_certificate typed addressType ?_ ?_ ?_⟩
    · simpa [stepRaw,returned,stack,found] using
        heap_typed_set typed.heap assigned (.cached originTyped addressValue addressPure)
    · simpa [stepRaw,returned,stack,found] using (ControlTyping.returned addressValue)
    · simpa [stepRaw,returned,stack,found] using restTyped

/-- A returned value with no pending demand frames completes at the promised
result type. Completion itself makes no termination assertion about the source. -/
theorem typed_completion_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} {value : RuntimeValue}
    (typed : StateTyping assumptions types state result)
    (returned : state.control = .returned value) (empty : state.stack = []) :
    Nonempty (StateTyping assumptions types (stepRaw state) result) := by
  have valueTyped : ValueTyping assumptions types value typed.current := by
    have control := typed.control
    rw [returned] at control
    cases control with | returned valueTyped => exact valueTyped
  refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
  · simpa [stepRaw,returned,empty] using typed.heap
  · simpa [stepRaw,returned,empty] using (ControlTyping.complete valueTyped)
  · simpa [stepRaw,returned,empty] using typed.stack

/-! ## Sums: injection, case and Boolean branching -/

theorem source_convert_path {assumptions : Assumptions} {context : Context} {term : Term}
    {first last : Ty} {uses : Uses} (typed : PartialTyping assumptions context term first uses)
    (path : ConversionPath assumptions first last) : PartialTyping assumptions context term last uses := by
  induction path with
  | refl => exact typed
  | step prior agreement ih => exact .conversion ih agreement

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
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .inject tag payload => InjectDerivation assumptions context tag payload type uses
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
    obtain ⟨payloadType,row,fuel,payloadTyped,lookup,path⟩ := ih
    exact ⟨payloadType,row,fuel,payloadTyped,lookup,.step path agreement⟩
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
  · intro context tag payload payloadType row uses fuel payloadTyped lookup _ ih
    exact ⟨payloadType,row,fuel,payloadTyped,lookup,.refl _⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

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
  refine PartialTyping.rec
    (motive_1 := fun context term type uses _ => match term with
      | .inject tag payload => InjectPureDerivation assumptions context tag payload type uses
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
    obtain ⟨payloadType,row,fuel,payloadTyped,lookup,pure,path⟩ := ih
    exact ⟨payloadType,row,fuel,payloadTyped,lookup,pure,.step path agreement⟩
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
  · intro context tag payload payloadType row uses fuel payloadTyped lookup pure ih
    exact ⟨payloadType,row,fuel,payloadTyped,lookup,pure,.refl _⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

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

theorem value_variant_fields {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {type : Ty} (typed : ValueTyping assumptions types value type) :
    ∀ tag address, value = .variant tag address →
      ∃ (row member actual : Ty) (fuel : Nat), row.lookup assumptions.bounds fuel tag = some member ∧
        types[address]? = some actual ∧ ConversionPath assumptions actual member ∧
        HeadNormalizes assumptions.bounds type (.variant row.canonical) := by
  induction typed with
  | natural value => intros; contradiction
  | boolean value => intros; contradiction
  | label value => intros; contradiction
  | closure environment body safe valid captures => intros; contradiction
  | record isRow members => intros; contradiction
  | specification metadata ext => intros; contradiction
  | prototype spec target => intros; contradiction
  | variant lookup assigned path =>
      intro tag address same
      cases same
      exact ⟨_,_,_,_,lookup,assigned,path,.direct _ rfl⟩
  | conversion prior agreement ih =>
      intro tag address same
      obtain ⟨row,member,actual,fuel,lookup,assigned,path,normal⟩ := ih tag address same
      exact ⟨row,member,actual,fuel,lookup,assigned,path,same_type_preserves_head agreement normal⟩

theorem variant_value_form {assumptions : Assumptions} {types : AddressTypes}
    {value : RuntimeValue} {row : Ty} (typed : ValueTyping assumptions types value (.variant row)) :
    ∃ tag address, value = .variant tag address := by
  obtain ⟨head,normal,kind⟩ := value_head_correct typed
  have same := head_normalizes_unique normal (.direct (.variant row) rfl)
  rw [same,Ty.canonical] at kind
  have shape : valueHead value = .variant := by simpa [typeHead] using kind.symm
  cases value with
  | variant tag address => exact ⟨tag,address,rfl⟩
  | _ => cases shape

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

/-- Every raw-machine constructor preserves typing over a monotonically
extended address assignment. Captured quantities travel with lexical origins,
closures, continuation arguments and generated mix/Fix bodies. -/
theorem typed_stepRaw_preserved {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result) :
    ∃ after, TypeExtension types after ∧ Nonempty (StateTyping assumptions after (stepRaw state) result) := by
  cases control : state.control with
  | enter address => exact ⟨types,type_extension_refl types,typed_enter_preserved typed control⟩
  | evaluate term environment =>
      cases term with
      | bound index => exact ⟨types,type_extension_refl types,typed_bound_preserved typed control⟩
      | lam body => exact ⟨types,type_extension_refl types,typed_immediate_preserved typed control rfl⟩
      | nat number => exact ⟨types,type_extension_refl types,typed_immediate_preserved typed control rfl⟩
      | boolean boolean => exact ⟨types,type_extension_refl types,typed_immediate_preserved typed control rfl⟩
      | label label => exact ⟨types,type_extension_refl types,typed_immediate_preserved typed control rfl⟩
      | app function argument => exact ⟨types,type_extension_refl types,typed_application_focus_preserved typed control⟩
      | mix lower upper => exact ⟨types,type_extension_refl types,typed_mix_preserved typed control⟩
      | fix spec seed => exact typed_fix_preserved typed control
      | record fields => exact typed_record_preserved typed control
      | specification metadata extension => exact typed_pair_preserved typed true control
      | prototype spec target => exact typed_pair_preserved typed false control
      | get target name => exact ⟨types,type_extension_refl types,typed_source_focus_preserved typed control rfl⟩
      | extend target fields => exact ⟨types,type_extension_refl types,typed_source_focus_preserved typed control rfl⟩
      | reflect target => exact ⟨types,type_extension_refl types,typed_source_focus_preserved typed control rfl⟩
      | metadata target => exact ⟨types,type_extension_refl types,typed_source_focus_preserved typed control rfl⟩
      | project target => exact ⟨types,type_extension_refl types,typed_source_focus_preserved typed control rfl⟩
      | binary primitive left right => exact ⟨types,type_extension_refl types,typed_source_focus_preserved typed control rfl⟩
      | ifZero value zero successor => exact ⟨types,type_extension_refl types,typed_source_focus_preserved typed control rfl⟩
      | inject tag payload => exact typed_inject_preserved typed control
      | case scrutinee arms => exact ⟨types,type_extension_refl types,typed_source_focus_preserved typed control rfl⟩
      | ifBool condition whenTrue whenFalse =>
          exact ⟨types,type_extension_refl types,typed_source_focus_preserved typed control rfl⟩
      | perform plan => exact typed_perform_preserved typed control
      | done value => exact ⟨types,type_extension_refl types,typed_done_preserved typed control⟩
  | returned value =>
      cases stack : state.stack with
      | nil => exact ⟨types,type_extension_refl types,typed_completion_preserved typed control stack⟩
      | cons frame rest =>
          cases frame with
          | argument argument environment => exact typed_argument_return_preserved typed control stack
          | update address => exact ⟨types,type_extension_refl types,typed_update_preserved typed control stack⟩
          | field name => exact ⟨types,type_extension_refl types,typed_field_preserved typed control stack⟩
          | reflect => exact ⟨types,type_extension_refl types,typed_prototype_projection_preserved typed true control stack⟩
          | metadata => exact ⟨types,type_extension_refl types,typed_metadata_preserved typed control stack⟩
          | project => exact ⟨types,type_extension_refl types,typed_prototype_projection_preserved typed false control stack⟩
          | extend fields environment => exact typed_extend_preserved typed control stack
          | condition zero successor environment => exact typed_condition_preserved typed control stack
          | binaryLeft primitive right environment => exact ⟨types,type_extension_refl types,typed_binary_left_preserved typed control stack⟩
          | binaryRight primitive left => exact ⟨types,type_extension_refl types,typed_binary_right_preserved typed control stack⟩
          | case arms environment => exact typed_case_preserved typed control stack
          | ifBool whenTrue whenFalse environment =>
              exact ⟨types,type_extension_refl types,typed_ifBool_preserved typed control stack⟩
  | blackhole address => exact ⟨types,type_extension_refl types,by simpa [stepRaw,control] using (Nonempty.intro typed)⟩
  | complete value => exact ⟨types,type_extension_refl types,by simpa [stepRaw,control] using (Nonempty.intro typed)⟩
  | yielded plan => exact ⟨types,type_extension_refl types,by simpa [stepRaw,control] using (Nonempty.intro typed)⟩
  | refused reason => exact False.elim (typed_control_not_refused typed.control reason control)

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
  arms_typing_find value_variant_fields

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

#assert_axioms typed_yield_quiescent typed_resume_preserved typed_perform_preserved

end Minidregg.Theory.ObjectiveBendDemandPreservation
