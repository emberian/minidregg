/- Preservation lemmas over the frozen demand graph and actual source typing.
Complete all-constructor preservation remains an explicit obligation; the
lemmas here do not claim that obligation merely by defining a typed relation. -/
import Theory.ObjectiveBendDemandTyping
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
      obtain ⟨address,found,assigned⟩ := members fuel name member lookup
      exact ⟨address,found,extension address member assigned⟩
  | specification metadata ext => exact .specification (extension _ _ metadata) (extension _ _ ext)
  | prototype spec target => exact .prototype (extension _ _ spec) (extension _ _ target)
  | conversion prior agreement ih => exact .conversion ih agreement

theorem CellTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {cell : Cell} {type : Ty} (extension : TypeExtension before after)
    (typed : CellTyping assumptions before cell type) : CellTyping assumptions after cell type := by
  cases typed with
  | suspended origin => exact .suspended (ClosureTyping.weaken extension origin)
  | evaluating origin => exact .evaluating (ClosureTyping.weaken extension origin)
  | cached origin value => exact .cached (ClosureTyping.weaken extension origin) (ValueTyping.weaken extension value)

theorem FrameTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {frame : Frame} {input output : Ty} (extension : TypeExtension before after)
    (typed : FrameTyping assumptions before frame input output) :
    FrameTyping assumptions after frame input output := by
  cases typed with
  | argument argument callable copyAllowed => exact .argument (ClosureTyping.weaken extension argument) callable copyAllowed
  | update assigned => exact .update (extension _ _ assigned)
  | field found => exact .field found
  | reflect => exact .reflect _ _
  | metadata => exact .metadata _ _
  | project => exact .project _ _
  | extend environment fields safe valid row => exact .extend (environment.weaken extension) fields safe valid row
  | condition zero environment successor safe valid =>
      exact .condition (ClosureTyping.weaken extension zero) (environment.weaken extension) successor safe valid
  | binaryLeft right => exact .binaryLeft (ClosureTyping.weaken extension right)
  | binaryRight left => exact .binaryRight (ValueTyping.weaken extension left)

theorem StackTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {stack : List Frame} {input output : Ty} (extension : TypeExtension before after)
    (typed : StackTyping assumptions before stack input output) :
    StackTyping assumptions after stack input output := by
  induction typed with
  | nil type => exact .nil type
  | cons frame rest ih => exact .cons (FrameTyping.weaken extension frame) ih
  | conversion agreement rest ih => exact .conversion agreement ih

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

/-- Address identity is conserved through arbitrary allocation extensions. -/
theorem type_extension_append (before additions : AddressTypes) :
    TypeExtension before (before ++ additions) := by
  intro address type assigned
  have bound : address < before.length := (List.getElem?_eq_some_iff.mp assigned).1
  simpa [List.getElem?_append,bound] using assigned

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
for EVERY stepRaw branch, including states whose type-preservation proof remains
under construction. This does not establish bad-operand exclusion. -/
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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
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
  | suspended origin =>
    refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
    · simpa [stepRaw,enter,found] using heap_typed_set typed.heap assigned (.evaluating origin)
    · simpa [stepRaw,enter,found] using (ControlTyping.evaluate origin)
    · simpa [stepRaw,enter,found] using (StackTyping.cons (.update assigned) typed.stack)
  | evaluating origin =>
    refine ⟨step_certificate typed typed.current ?_ ?_ ?_⟩
    · simpa [stepRaw,enter,found] using typed.heap
    · simpa [stepRaw,enter,found] using (ControlTyping.blackhole assigned)
    · simpa [stepRaw,enter,found] using typed.stack
  | cached origin value =>
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
      have equal : bound.canonical = second.canonical := by simpa [found] using aliasFirst
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
      have equal : bound.canonical = first.canonical := by simpa [found] using aliasSecond
      exact .alias found (canonical_agreement_normalizes equal.symm normal)

inductive HeadKind where
  | natural | boolean | label | function | row | specification | prototype | custody | variable
  deriving DecidableEq

def typeHead : Ty → HeadKind
  | .natural => .natural | .boolean => .boolean | .label => .label
  | .arrow _ _ _ _ => .function | .emptyRow | .field _ _ _ => .row
  | .specification _ _ => .specification | .prototype _ _ => .prototype
  | .custody _ => .custody | .variable _ => .variable

def valueHead : RuntimeValue → HeadKind
  | .natural _ => .natural | .boolean _ => .boolean | .label _ => .label
  | .closure _ _ => .function | .record _ => .row
  | .specification _ _ => .specification | .prototype _ _ => .prototype

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
  | conversion prior agreement ih =>
      obtain ⟨head,normal,kind⟩ := ih
      exact ⟨head,same_type_preserves_head agreement normal,kind⟩

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

/-- Finite source conversion evidence is retained as a path rather than an
assumed transitive subtype decision procedure. -/
inductive ConversionPath (assumptions : Assumptions) : Ty → Ty → Prop where
  | refl (type : Ty) : ConversionPath assumptions type type
  | step {first middle last : Ty} : ConversionPath assumptions first middle →
      sameType assumptions middle last = true → ConversionPath assumptions first last

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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
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
      | update assigned => exact ⟨_,assigned,valueTyped,restTyped⟩
  | conversion agreement restTyped ih =>
      exact ih (.conversion valueTyped agreement)

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
          heap_typed_push typed.heap (CellTyping.cached predecessor (.natural number))
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
  | evaluating originTyped =>
    refine ⟨step_certificate typed addressType ?_ ?_ ?_⟩
    · simpa [stepRaw,returned,stack,found] using
        heap_typed_set typed.heap assigned (.cached originTyped addressValue)
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

/-- The actual checker token excludes all three internal-reference refusals
through arbitrary raw-machine reachability, even while full semantic operand
preservation is an open obligation. Blackholes and bounds may still suspend. -/
theorem checked_reachable_no_internal_refusal (source : AnnotatedTerm)
    (checked : Checked source []) {state : State}
    (reachable : ObjectiveBendDemandInvariant.Reachable (initial source.erase) state) :
    state.control ≠ .refused .unbound ∧ state.control ≠ .refused .missingCell ∧
      state.control ≠ .refused .invalidUpdate :=
  ObjectiveBendDemandInvariant.reachable_no_internalRefusal (source_scoped checked.derivation) reachable

/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.same_type_preserves_head' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms same_type_preserves_head
/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.value_head_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms value_head_correct
/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.typed_binary_right_no_wrong_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms typed_binary_right_no_wrong_value
/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.typed_condition_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms typed_condition_preserved
/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.typed_condition_no_wrong_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms typed_condition_no_wrong_value
/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.canonical_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canonical_lookup
/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.typed_bound_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms typed_bound_preserved
/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.typed_application_focus_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms typed_application_focus_preserved
/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.typed_enter_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms typed_enter_preserved
/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.typed_update_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms typed_update_preserved
/-
info: 'Minidregg.Theory.ObjectiveBendDemandPreservation.checked_reachable_no_internal_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms checked_reachable_no_internal_refusal

end Minidregg.Theory.ObjectiveBendDemandPreservation
