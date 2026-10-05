/- Preservation, shared lemmas: weakening, the typing/usage algebra, value and stack
inversions, source decompositions every constructor's case uses. No dispatcher here:
the per-constructor case modules import this, the umbrella imports them. -/
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
    cases aliased : assumptions.alias index with
    | none => simp [aliased] at aliasActual
    | some bound =>
      have found := Assumptions.alias_bound aliased
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = expected.canonical := by simpa [aliased] using aliasActual
      obtain ⟨depth,actualMember,actualLookup,memberEq⟩ := canonical_lookup_transport assumptions.bounds bound expected equal fuel name member lookup
      exact ⟨depth+1,actualMember,by simpa [Ty.lookup,found] using actualLookup,memberEq⟩
  · cases expected <;> simp at aliasExpected
    rename_i index
    cases aliased : assumptions.alias index with
    | none => simp [aliased] at aliasExpected
    | some bound =>
      have found := Assumptions.alias_bound aliased
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = actual.canonical := by simpa [aliased] using aliasExpected
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
    cases aliased : assumptions.alias index with
    | none => simp [aliased] at aliasFirst
    | some bound =>
      have found := Assumptions.alias_bound aliased
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = second.canonical := by simpa [aliased] using aliasFirst
      cases normal with
      | direct type terminal => simp [isVariable] at terminal
      | alias found' prior =>
        have same := Option.some.inj (found'.symm.trans found)
        subst same
        exact canonical_agreement_normalizes equal prior
  · cases second <;> simp at aliasSecond
    rename_i index
    cases aliased : assumptions.alias index with
    | none => simp [aliased] at aliasSecond
    | some bound =>
      have found := Assumptions.alias_bound aliased
      obtain ⟨-,equal⟩ : _ ∧ bound.canonical = first.canonical := by simpa [aliased] using aliasSecond
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
  apply PartialTyping.rec
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
    (t := typed)
  case bound =>
    intro context index declared found depth binding bound bindingValid
    simpa only [Term.rename,← variable_uses_insert context binding index depth bound] using
      (PartialTyping.bound (binding_insert_shift found) : PartialTyping assumptions (context.insertIdx depth binding)
        (.bound (shiftIndex depth index)) declared.type (variableUses (context.insertIdx depth binding) (shiftIndex depth index)))
  case natural =>
    intro context value depth binding bound bindingValid
    simpa only [Term.rename,← zero_uses_insert context binding depth bound] using
      (PartialTyping.natural (context.insertIdx depth binding) value : PartialTyping assumptions _ (.nat value) .natural _)
  case boolean =>
    intro context value depth binding bound bindingValid
    simpa only [Term.rename,← zero_uses_insert context binding depth bound] using
      (PartialTyping.boolean (context.insertIdx depth binding) value : PartialTyping assumptions _ (.boolean value) .boolean _)
  case label =>
    intro context value depth binding bound bindingValid
    simpa only [Term.rename,← zero_uses_insert context binding depth bound] using
      (PartialTyping.label (context.insertIdx depth binding) value : PartialTyping assumptions _ (.label value) (literalType value) _)
  case lambda =>
    intro context body annotation uses bodyTyped safe valid captures ih depth binding bound bindingValid
    have bodyBound : depth+1 ≤ (⟨annotation.domain,annotation.parameter⟩ :: context).length := by simpa using bound
    have nonempty : 0 < uses.length := by rw [source_uses_length bodyTyped]; simp
    have bodyNext := ih (depth+1) binding bodyBound bindingValid
    have safeNext := safe_uses_insert _ uses (depth+1) binding safe bodyBound
    have validNext := valid_context_insert _ _ (depth+1) binding valid bindingValid bodyBound
    have capturesNext := reusable_allowed_insert assumptions annotation.reuse context uses.tail depth binding captures bound
    simpa only [Term.rename,lift_shift_index,List.insertIdx_succ_cons,uses_tail_insert nonempty] using
      (PartialTyping.lambda bodyNext safeNext validNext (by simpa only [List.insertIdx_succ_cons,uses_tail_insert nonempty] using capturesNext))
  case conversion =>
    intro context term actual expected uses prior agreement ih depth binding bound bindingValid
    exact .conversion (ih depth binding bound bindingValid) agreement
  case application =>
    intro context fn arg functionType argumentType domain codomain fu au reuse quantity fnTyped argTyped callableEq same allowed ihFn ihArg depth binding bound bindingValid
    have counts := add_uses_insert fu au depth ((source_uses_length fnTyped).trans (source_uses_length argTyped).symm) (insert_usage_bound fnTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.application (ihFn depth binding bound bindingValid) (ihArg depth binding bound bindingValid) callableEq same
        (argument_allowed_insert assumptions quantity context argumentType au depth binding allowed bound))
  case record =>
    intro context fields row uses fieldsTyped ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.record (ih depth binding bound bindingValid))
  case get =>
    intro context target targetType member uses name fuel targetTyped lookup ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.get (ih depth binding bound bindingValid) lookup)
  case extend =>
    intro context target fields targetType row tu fu rowFuel targetTyped fieldsTyped isRow ihTarget ihFields depth binding bound bindingValid
    have fieldLength := source_uses_length (PartialTyping.record fieldsTyped)
    have counts := add_uses_insert tu fu depth ((source_uses_length targetTyped).trans fieldLength.symm) (insert_usage_bound targetTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.extend (ihTarget depth binding bound bindingValid) (ihFields depth binding bound bindingValid) isRow)
  case specification =>
    intro context metadata extension metadataType extensionType mu eu metadataTyped extensionTyped mPure ePure ihMetadata ihExtension depth binding bound bindingValid
    have counts := add_uses_insert mu eu depth ((source_uses_length metadataTyped).trans (source_uses_length extensionTyped).symm) (insert_usage_bound metadataTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.specification (ihMetadata depth binding bound bindingValid) (ihExtension depth binding bound bindingValid) mPure ePure)
  case prototype =>
    intro context spec target specType targetType su tu specTyped targetTyped sPure tPure ihSpec ihTarget depth binding bound bindingValid
    have counts := add_uses_insert su tu depth ((source_uses_length specTyped).trans (source_uses_length targetTyped).symm) (insert_usage_bound specTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.prototype (ihSpec depth binding bound bindingValid) (ihTarget depth binding bound bindingValid) sPure tPure)
  case reflect =>
    intro context target specType targetType uses prior ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.reflect (ih depth binding bound bindingValid))
  case metadata =>
    intro context target metadataType extensionType uses prior ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.metadata (ih depth binding bound bindingValid))
  case project =>
    intro context target specType targetType uses prior ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.project (ih depth binding bound bindingValid))
  case mix =>
    intro context lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped lowerCallable upperCallable captures selfShare inheritedShare middleShare ihLower ihUpper depth binding bound bindingValid
    have counts := add_uses_insert lu uu depth ((source_uses_length lowerTyped).trans (source_uses_length upperTyped).symm) (insert_usage_bound lowerTyped bound)
    have capturesNext := reusable_captures_insert assumptions.shareableVariables context (addUses lu uu) depth binding captures bound
    simpa only [Term.rename,counts] using
      (PartialTyping.mix (ihLower depth binding bound bindingValid) (ihUpper depth binding bound bindingValid)
        lowerCallable upperCallable (by simpa only [counts] using capturesNext) selfShare inheritedShare middleShare)
  case fix =>
    intro context spec inheritedTerm specType inherited target su iu specTyped callableEq inheritedTyped targetShare inheritedAllowed captures ihSpec ihInherited depth binding bound bindingValid
    have counts := add_uses_insert su iu depth ((source_uses_length specTyped).trans (source_uses_length inheritedTyped).symm) (insert_usage_bound specTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.fix (ihSpec depth binding bound bindingValid) callableEq (ihInherited depth binding bound bindingValid) targetShare
        (argument_allowed_insert assumptions .unrestricted context inherited iu depth binding inheritedAllowed bound)
        (reusable_captures_insert assumptions.shareableVariables context su depth binding captures bound))
  case binary =>
    intro context primitive left right input output lu ru primitiveEq leftTyped rightTyped ihLeft ihRight depth binding bound bindingValid
    have counts := add_uses_insert lu ru depth ((source_uses_length leftTyped).trans (source_uses_length rightTyped).symm) (insert_usage_bound leftTyped bound)
    simpa only [Term.rename,counts] using
      (PartialTyping.binary primitiveEq (ihLeft depth binding bound bindingValid) (ihRight depth binding bound bindingValid))
  case ifZero =>
    intro context value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe ihValue ihZero ihSuccessor depth binding bound bindingValid
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
  case inject =>
    intro context tag payload payloadType row uses fuel payloadTyped lookup pure ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.inject (ih depth binding bound bindingValid) lookup pure)
  case case =>
    intro context scrutinee arms row result su au scrutineeTyped armsTyped ihScrutinee ihArms depth binding bound bindingValid
    have counts := add_uses_insert su au depth ((source_uses_length scrutineeTyped).trans (arms_uses_length armsTyped).symm) (insert_usage_bound scrutineeTyped bound)
    simpa only [Term.rename,lift_shift_index,counts] using
      (PartialTyping.case (ihScrutinee depth binding bound bindingValid) (ihArms depth binding bound bindingValid))
  case ifBool =>
    intro context condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped ihCondition ihTrue ihFalse depth binding bound bindingValid
    have trueLength := source_uses_length trueTyped
    have falseLength := source_uses_length falseTyped
    have firstCounts := add_uses_insert tu fu depth (trueLength.trans falseLength.symm) (insert_usage_bound trueTyped bound)
    have sumLength : (addUses tu fu).length = context.length := by simp [addUses,List.length_zipWith,trueLength,falseLength]
    have allCounts := add_uses_insert cu (addUses tu fu) depth ((source_uses_length conditionTyped).trans sumLength.symm) (insert_usage_bound conditionTyped bound)
    simpa only [Term.rename,firstCounts,allCounts] using
      (PartialTyping.ifBool (ihCondition depth binding bound bindingValid) (ihTrue depth binding bound bindingValid)
        (ihFalse depth binding bound bindingValid))
  case perform =>
    intro context plan planType response uses planTyped isPlan isData ih depth binding bound bindingValid
    simpa only [Term.rename] using (PartialTyping.perform (ih depth binding bound bindingValid) isPlan isData)
  case done =>
    intro context value planType response result uses valueTyped pure ih depth binding bound bindingValid
    simpa only [Term.rename] using
      (PartialTyping.done (planType := planType) (response := response) (ih depth binding bound bindingValid) pure)
  case effectCase =>
    intro context scrutinee arms planType response row result su au scrutineeTyped armsTyped pure ihScrutinee ihArms depth binding bound bindingValid
    have counts := add_uses_insert su au depth ((source_uses_length scrutineeTyped).trans (arms_uses_length armsTyped).symm) (insert_usage_bound scrutineeTyped bound)
    simpa only [Term.rename,lift_shift_index,counts] using
      (PartialTyping.effectCase (ihScrutinee depth binding bound bindingValid) (ihArms depth binding bound bindingValid) pure)
  case nil =>
    intro context depth binding bound bindingValid
    simpa only [List.map_nil,← zero_uses_insert context binding depth bound] using (FieldsTyping.nil (context.insertIdx depth binding) : FieldsTyping assumptions _ [] .emptyRow _)
  case cons =>
    intro context name body rest type row bu ru bodyTyped restTyped pure ihBody ihRest depth binding bound bindingValid
    have restLength := source_uses_length (PartialTyping.record restTyped)
    have counts := add_uses_insert bu ru depth ((source_uses_length bodyTyped).trans restLength.symm) (insert_usage_bound bodyTyped bound)
    simpa only [List.map_cons,counts] using
      (FieldsTyping.cons (ihBody depth binding bound bindingValid) (ihRest depth binding bound bindingValid) pure)
  case nil =>
    intro context result depth binding bound bindingValid
    simpa only [List.map_nil,← zero_uses_insert context binding depth bound] using
      (ArmsTyping.nil (context.insertIdx depth binding) result : ArmsTyping assumptions _ [] .emptyRow result _)
  case cons =>
    intro context name body rest payload row result bu ru bodyTyped safe shareable restTyped ihBody ihRest depth binding bound bindingValid
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
  apply PartialTyping.rec
    (motive_1 := fun context term type _ _ => match term with
      | .bound index => ∃ binding, context[index]? = some binding ∧
          ConversionPath assumptions binding.type type
      | _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (t := source)
  case bound =>
    intro context index binding found; exact ⟨binding,found,.refl binding.type⟩
  case conversion =>
    intro context term actual expected uses prior agreement ih
    cases term <;> try trivial
    obtain ⟨binding,found,path⟩ := ih
    exact ⟨binding,found,.step path agreement⟩
  all_goals (intros; trivial)

theorem safe_add_uses_right (context : Context) (first second : Uses)
    (firstLength : first.length = context.length) (secondLength : second.length = context.length)
    (safe : safeUses context (addUses first second) = true) : safeUses context second = true := by
  rw [add_uses_comm] at safe
  exact safe_add_uses_left context second first secondLength firstLength safe

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
  apply PartialTyping.rec
    (motive_1 := fun context term type uses _ => ∀ types environment,
      EnvironmentTyping types context environment → safeUses context uses = true →
      validContext assumptions.shareableVariables context = true →
      match sourceFocus term environment with
      | some (target,frame) => Nonempty (FocusedSource assumptions types target environment frame type)
      | none => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (t := source)
  case conversion =>
    intro context term actual expected uses prior agreement ih types environment environmentTyped safe valid
    have focused := ih types environment environmentTyped safe valid
    cases found : sourceFocus term environment with
    | none => trivial
    | some pair =>
      obtain ⟨target,frame⟩ := pair
      rw [found] at focused
      obtain ⟨data⟩ := focused
      exact ⟨⟨data.current,data.output,data.origin,data.continuation,.step data.result agreement⟩⟩
  case get =>
    intro context target targetType member uses name fuel targetTyped lookup ih types environment environmentTyped safe valid
    exact ⟨⟨targetType,member,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.field lookup,.refl member⟩⟩
  case extend =>
    intro context target fields targetType row targetUses fieldUses rowFuel targetTyped fieldsTyped rowValid ihTarget ihFields types environment environmentTyped safe valid
    have targetSafe := safe_add_uses_left context targetUses fieldUses (source_uses_length targetTyped)
      (source_uses_length (PartialTyping.record fieldsTyped)) safe
    have fieldsSafe := safe_add_uses_right context targetUses fieldUses (source_uses_length targetTyped)
      (source_uses_length (PartialTyping.record fieldsTyped)) safe
    exact ⟨⟨targetType,overlay row targetType,⟨context,targetUses,environmentTyped,targetTyped,targetSafe,valid⟩,
      .extend environmentTyped fieldsTyped fieldsSafe valid rowValid,.refl _⟩⟩
  case reflect =>
    intro context target specType targetType uses targetTyped ih types environment environmentTyped safe valid
    exact ⟨⟨.prototype specType targetType,specType,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.reflect _ _,.refl _⟩⟩
  case metadata =>
    intro context target metadataType extensionType uses targetTyped ih types environment environmentTyped safe valid
    exact ⟨⟨.specification metadataType extensionType,metadataType,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.metadata _ _,.refl _⟩⟩
  case project =>
    intro context target specType targetType uses targetTyped ih types environment environmentTyped safe valid
    exact ⟨⟨.prototype specType targetType,targetType,⟨context,uses,environmentTyped,targetTyped,safe,valid⟩,.project _ _,.refl _⟩⟩
  case binary =>
    intro context primitive left right input output lu ru primitiveEq leftTyped rightTyped ihLeft ihRight types environment environmentTyped safe valid
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
  case ifZero =>
    intro context value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe ihValue ihZero ihSuccessor types environment environmentTyped safe valid
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
  case case =>
    intro context scrutinee arms row result su au scrutineeTyped armsTyped ihScrutinee ihArms types environment environmentTyped safe valid
    have scrutineeSafe := safe_add_uses_left context su au (source_uses_length scrutineeTyped) (arms_uses_length armsTyped) safe
    exact ⟨⟨.variant row,result,⟨context,su,environmentTyped,scrutineeTyped,scrutineeSafe,valid⟩,
      .case environmentTyped armsTyped valid,.refl _⟩⟩
  case ifBool =>
    intro context condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped ihCondition ihTrue ihFalse types environment environmentTyped safe valid
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
  case effectCase =>
    intro context scrutinee arms planType response row result su au scrutineeTyped armsTyped pure ihScrutinee ihArms types environment environmentTyped safe valid
    have scrutineeSafe := safe_add_uses_left context su au (source_uses_length scrutineeTyped) (arms_uses_length armsTyped) safe
    exact ⟨⟨.computation planType response (.variant row),.computation planType response result,
      ⟨context,su,environmentTyped,scrutineeTyped,scrutineeSafe,valid⟩,
      .effectCase environmentTyped armsTyped valid pure,.refl _⟩⟩
  case nil =>
    intros; trivial
  case cons =>
    intros; trivial
  case nil =>
    intros; trivial
  case cons =>
    intros; trivial
  all_goals (intros; simp [sourceFocus])

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

theorem source_convert_path {assumptions : Assumptions} {context : Context} {term : Term}
    {first last : Ty} {uses : Uses} (typed : PartialTyping assumptions context term first uses)
    (path : ConversionPath assumptions first last) : PartialTyping assumptions context term last uses := by
  induction path with
  | refl => exact typed
  | step prior agreement ih => exact .conversion ih agreement

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

end Minidregg.Theory.ObjectiveBendDemandPreservation
