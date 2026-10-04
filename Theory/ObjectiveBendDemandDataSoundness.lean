/- The Plan output path as a theorem: `forceWith`/`executeWith` against the
proved `runBounded`, and deep soundness of the Data that `materializeWith`
extracts by re-entering lazy record fields.

* `forceWith_unrestricted`: `forceWith (fun _ => true)` IS `runBounded`.
* `forceWith_policy_suspends`: any policy only replaces the unrestricted
  outcome by a capacity suspension at an exact retained `runBounded` prefix.
* `executeWith_source_semantics`: a successful `executeWith` (any policy, e.g.
  the native capacity profile) on a closed term is a finished `runBounded`, and
  the extracted Data is a DEEP reference evaluation of the source term:
  every scalar is an `Evaluates` of the term at its path, every record level an
  `Evaluates` to a record literal whose field terms deep-evaluate in order. -/
import Theory.ObjectiveBendDemandCompleteness
import Theory.ObjectiveBendDemandData
import Theory.ObjectiveBendDemandCapacity
namespace Minidregg.Theory.ObjectiveBendDemandDataSoundness
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandInvariant
open Minidregg.Theory.ObjectiveBendDemandAdequacy
open Minidregg.Theory.ObjectiveBendDemandData
set_option autoImplicit false

/-! ## forceWith against runBounded -/

def Terminal (state : State) : Prop :=
  match state.control with
  | .complete _ | .refused _ | .blackhole _ | .yielded _ => True
  | _ => False

 theorem runBounded_terminal {limits : Limits} {state : State} (terminal : Terminal state) (ticks : Nat) :
    runBounded limits ticks state = runBounded limits 0 state := by
  cases ticks with
  | zero => rfl
  | succ ticks =>
      cases control : state.control <;> simp [Terminal,control] at terminal <;> simp [runBounded,step,control]

 theorem forceWith_unrestricted (limits : Limits) (ticks : Nat) (state : State) :
    (forceWith (fun _ => true) limits ticks state).1 = runBounded limits ticks state := by
  induction ticks generalizing state with
  | zero => simp [forceWith]
  | succ ticks ih =>
      cases control : state.control with
      | complete _ | refused _ | blackhole _ | yielded _ =>
          simp [forceWith,control,runBounded,step]
      | evaluate _ _ | enter _ | returned _ =>
          by_cases fits : (stepRaw state).heap.size ≤ limits.heap ∧ (stepRaw state).stack.length ≤ limits.stack
          · have stepped : step limits state = .suspended .ticks (stepRaw state) := by simp [step,control,fits]
            cases next : (stepRaw state).control with
            | complete _ | refused _ | blackhole _ | yielded _ =>
                have terminal : Terminal (stepRaw state) := by simp [Terminal,next]
                have tail : runBounded limits (ticks+1) state = runBounded limits 0 (stepRaw state) := by
                  rw [show runBounded limits (ticks+1) state = runBounded limits ticks (stepRaw state) by
                    simp only [runBounded,stepped],runBounded_terminal terminal]
                rw [tail]
                simp [forceWith,control,runBounded,stepped,next]
            | evaluate _ _ | enter _ | returned _ =>
                simp [forceWith,control,runBounded,stepped,next]
                rw [←ih (stepRaw state)]
          · have stepped : step limits state = .suspended .capacity state := by simp [step,control,fits]
            simp [forceWith,control,runBounded,stepped]

/-- A policy can only stop early, with a capacity suspension retaining the
exact state that the unrestricted bounded run reached at that point. -/
 theorem forceWith_policy_suspends (policy : State → Bool) (limits : Limits) (ticks : Nat) (state : State) :
    (forceWith policy limits ticks state).1 = runBounded limits ticks state ∨
      ∃ count retained, count ≤ ticks ∧ runBounded limits count state = .suspended .ticks retained ∧
        policy retained = false ∧ (forceWith policy limits ticks state).1 = .suspended .capacity retained := by
  induction ticks generalizing state with
  | zero => left; simp [forceWith]
  | succ ticks ih =>
      cases control : state.control with
      | complete _ | refused _ | blackhole _ | yielded _ =>
          left; simp [forceWith,control,runBounded,step]
      | evaluate _ _ | enter _ | returned _ =>
          by_cases allowed : policy state = true
          · by_cases fits : (stepRaw state).heap.size ≤ limits.heap ∧ (stepRaw state).stack.length ≤ limits.stack
            · have stepped : step limits state = .suspended .ticks (stepRaw state) := by simp [step,control,fits]
              cases next : (stepRaw state).control with
              | complete _ | refused _ | blackhole _ | yielded _ =>
                  have terminal : Terminal (stepRaw state) := by simp [Terminal,next]
                  have tail : runBounded limits (ticks+1) state = runBounded limits 0 (stepRaw state) := by
                    rw [show runBounded limits (ticks+1) state = runBounded limits ticks (stepRaw state) by
                      simp only [runBounded,stepped],runBounded_terminal terminal]
                  left
                  rw [tail]
                  simp [forceWith,control,allowed,runBounded,stepped,next]
              | evaluate _ _ | enter _ | returned _ =>
                  rcases ih (stepRaw state) with same | ⟨count,retained,le,prefixEq,refused,result⟩
                  · left
                    simp [forceWith,control,allowed,runBounded,stepped,next]
                    exact same
                  · right
                    refine ⟨count+1,retained,by omega,by simpa [runBounded,stepped] using prefixEq,refused,?_⟩
                    simp [forceWith,control,allowed,runBounded,stepped,next]
                    exact result
            · have stepped : step limits state = .suspended .capacity state := by simp [step,control,fits]
              left; simp [forceWith,control,allowed,runBounded,stepped]
          · right
            refine ⟨0,state,by omega,by simp [runBounded,control],by simpa using allowed,?_⟩
            simp [forceWith,control,allowed]

 theorem forceWith_finished {policy : State → Bool} {limits : Limits} {ticks : Nat} {state final : State}
    {value : RuntimeValue} (finished : (forceWith policy limits ticks state).1 = .finished value final) :
    runBounded limits ticks state = .finished value final := by
  rcases forceWith_policy_suspends policy limits ticks state with same | ⟨_,_,_,_,_,suspended⟩
  · rw [←same]; exact finished
  · rw [finished] at suspended; cases suspended

/-! ## Deep source evaluation of Data -/

mutual
/-- Deep reference evaluation: a scalar is an `Evaluates` of the term; a record
is an `Evaluates` to a record literal whose field TERMS deep-evaluate, in order,
to the field data. This is defined from the independent source semantics only. -/
inductive DeepEvaluates : Term → Data → Prop where
  | natural {term : Term} {number : Nat} : Evaluates term (.nat number) → DeepEvaluates term (.natural number)
  | boolean {term : Term} {value : Bool} : Evaluates term (.boolean value) → DeepEvaluates term (.boolean value)
  | label {term : Term} {name : String} : Evaluates term (.label name) → DeepEvaluates term (.label name)
  | record {term : Term} {fields : List (String × Term)} {data : List (String × Data)} :
      Evaluates term (.record fields) → DeepFields fields data → DeepEvaluates term (.record data)
  /-- A variant evaluates to an injection whose payload TERM deep-evaluates. -/
  | variant {term payload : Term} {tag : String} {data : Data} :
      Evaluates term (.inject tag payload) → DeepEvaluates payload data → DeepEvaluates term (.variant tag data)
inductive DeepFields : List (String × Term) → List (String × Data) → Prop where
  | nil : DeepFields [] []
  | cons {name : String} {term : Term} {value : Data} {fields : List (String × Term)} {data : List (String × Data)} :
      DeepEvaluates term value → DeepFields fields data → DeepFields ((name,term)::fields) ((name,value)::data)
end

 theorem deepEvaluates_steps {before after : Term} {data : Data}
    (steps : Steps before after) (deep : DeepEvaluates after data) : DeepEvaluates before data := by
  cases deep with
  | natural evaluates => exact .natural ⟨sourceSteps_trans steps evaluates.1,evaluates.2⟩
  | boolean evaluates => exact .boolean ⟨sourceSteps_trans steps evaluates.1,evaluates.2⟩
  | label evaluates => exact .label ⟨sourceSteps_trans steps evaluates.1,evaluates.2⟩
  | record evaluates fields => exact .record ⟨sourceSteps_trans steps evaluates.1,evaluates.2⟩ fields
  | variant evaluates payload => exact .variant ⟨sourceSteps_trans steps evaluates.1,evaluates.2⟩ payload

 theorem deepFields_append {fields : List (String × Term)} {data : List (String × Data)}
    {name : String} {term : Term} {value : Data}
    (prefixFields : DeepFields fields data) (last : DeepEvaluates term value) :
    DeepFields (fields ++ [(name,term)]) (data ++ [(name,value)]) := by
  induction fields generalizing data with
  | nil => cases prefixFields; exact .cons last .nil
  | cons field rest ih =>
      cases prefixFields with
      | cons head tail => exact .cons head (ih tail)

/-! ## Materialization re-enters fields soundly -/

/-- A completed, settled heap: no active update, every name realized. -/
def Settled (meaning : AddressMeaning) (state : State) : Prop :=
  LexicalInvariant state ∧ BusyInvariant state ∧ state.stack = [] ∧
    MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap

 theorem force_field_sound {policy : State → Bool} {limits : Limits} {ticks : Nat}
    {state retained : State} {meaning : AddressMeaning} {address : Address} {forced : RuntimeValue}
    (settled : Settled meaning state) (allocated : address < state.heap.size)
    (forcedEq : (forceWith policy limits ticks {heap := state.heap,control := .enter address,stack := []}).1 =
      .finished forced retained) :
    ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ Settled next retained ∧
      state.heap.size ≤ retained.heap.size ∧ RuntimeValueValid retained.heap.size forced ∧
      Steps (meaning address) (valueMeaning next forced) := by
  obtain ⟨lexical,busy,emptyStack,names,heap⟩ := settled
  let entered : State := {state with control := .enter address,stack := []}
  have represented : GraphRepresentsBy meaning entered (meaning address) := by
    refine ⟨⟨lexical.1,?_,?_⟩,?_,?_,names,heap,meaning address,rfl,Steps.refl _⟩
    · simpa [entered,ControlValid] using allocated
    · simp [entered]
    · have busyEmpty : Busy state.heap [] := by simpa [BusyInvariant,emptyStack] using busy
      simpa [BusyInvariant,entered] using busyEmpty
    · intro value complete; simp [entered] at complete
  have run := forceWith_finished (show (forceWith policy limits ticks entered).1 = .finished forced retained from forcedEq)
  obtain ⟨count,_,prefixEq⟩ := runBounded_retained_prefix limits ticks entered
  rw [run] at prefixEq
  simp only [retainedState] at prefixEq
  have complete := runBounded_finished_control run
  obtain ⟨next,same,graph⟩ := rawRun_graphBy_names (ticks := count) represented
    (by rw [←prefixEq,complete]; trivial)
  rw [←prefixEq] at graph
  obtain ⟨lexical',busy',final',names',heap',residual,control,stack⟩ := graph
  have empty := final' forced complete
  simp only [controlMeaning,complete,Option.some.injEq] at control
  subst residual
  have grows : entered.heap.size ≤ retained.heap.size := by
    rw [prefixEq]; exact (reachable_preservesOrigins (rawRun_reachable .start count)).1
  have valid : RuntimeValueValid retained.heap.size forced := by
    simpa [ControlValid,complete] using lexical'.2.1
  refine ⟨next,same,⟨lexical',busy',empty,names',heap'⟩,grows,valid,?_⟩
  simpa only [empty,StackRealizes] using stack

/-- Fold invariant over the record fields processed so far. -/
def FieldsInvariant (origin : State) (meaning : AddressMeaning) (processed : List (String × Address))
    (accumulated : List (String × Data) × State × Budget) : Prop :=
  DeepFields (processed.map fun field => (field.1,meaning field.2)) accumulated.1.reverse ∧
    ∃ current : AddressMeaning, SourceNamesAgree origin meaning current ∧ Settled current accumulated.2.1 ∧
      origin.heap.size ≤ accumulated.2.1.heap.size

 theorem foldlM_fieldsInvariant {origin : State} {meaning : AddressMeaning}
    {body : List (String × Data) × State × Budget → String × Address →
      Except (Failure × State) (List (String × Data) × State × Budget)}
    (stepOk : ∀ processed accumulated field result, field.2 < origin.heap.size →
      FieldsInvariant origin meaning processed accumulated → body accumulated field = .ok result →
      FieldsInvariant origin meaning (processed ++ [field]) result) :
    ∀ (todo processed : List (String × Address)) accumulated result,
      (∀ field ∈ todo, field.2 < origin.heap.size) →
      FieldsInvariant origin meaning processed accumulated → todo.foldlM body accumulated = .ok result →
      FieldsInvariant origin meaning (processed ++ todo) result := by
  intro todo
  induction todo with
  | nil =>
      intro processed accumulated result _ invariant folded
      simp only [List.foldlM_nil] at folded
      cases folded
      simpa using invariant
  | cons field rest ih =>
      intro processed accumulated result valid invariant folded
      simp only [List.foldlM_cons] at folded
      cases first : body accumulated field with
      | error failure => simp [first] at folded; cases folded
      | ok middle =>
          simp only [first] at folded
          have middleInvariant := stepOk processed accumulated field middle
            (valid field (List.mem_cons_self ..)) invariant first
          have done := ih (processed ++ [field]) middle result
            (fun other member => valid other (List.mem_cons_of_mem _ member)) middleInvariant folded
          simpa using done

 theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a,rfl,h⟩

/-- DEEP DATA SOUNDNESS. From a settled heap whose names are realized by
`meaning`, any successful materialization of a runtime value (under ANY
policy, limits and budget) yields Data that is a deep reference evaluation of
the value's source meaning, and leaves a settled heap extending the names. -/
 theorem materialize_sound (policy : State → Bool) (limits : Limits) :
    ∀ (depth : Nat) (budget : Budget) (value : RuntimeValue) (state : State) (meaning : AddressMeaning)
      (result : Result),
      Settled meaning state → RuntimeValueValid state.heap.size value →
      materializeWith policy limits depth budget value state = .ok result →
      DeepEvaluates (valueMeaning meaning value) result.value ∧
        ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ Settled next result.state ∧
          state.heap.size ≤ result.state.heap.size := by
  intro depth
  induction depth with
  | zero =>
      intro budget value state meaning result _ _ h
      cases h
  | succ depth ih =>
      intro budget value state meaning result settled valid h
      have keep : ∃ next : AddressMeaning, SourceNamesAgree state meaning next ∧ Settled next state ∧
          state.heap.size ≤ state.heap.size := ⟨meaning,fun _ _ => rfl,settled,Nat.le_refl _⟩
      cases value with
      | natural number =>
          simp only [materializeWith] at h
          split at h
          · cases h
          · split at h
            · cases h
            · cases h
              exact ⟨.natural ⟨.refl _,.natural _⟩,keep⟩
      | boolean flag =>
          simp only [materializeWith] at h
          split at h
          · cases h
          · split at h
            · cases h
            · cases h
              exact ⟨.boolean ⟨.refl _,.boolean _⟩,keep⟩
      | label name =>
          simp only [materializeWith] at h
          split at h
          · cases h
          · split at h
            · cases h
            · cases h
              exact ⟨.label ⟨.refl _,.label _⟩,keep⟩
      | closure _ _ | specification _ _ | prototype _ _ =>
          simp only [materializeWith] at h
          split at h <;> cases h
      | variant tag payload =>
          simp only [materializeWith] at h
          split at h
          · cases h
          · split at h
            · cases h
            · rename_i bytesOk
              have allocated : payload < state.heap.size := valid
              cases forced : (forceWith policy limits budget.ticks
                  {heap := state.heap,control := .enter payload,stack := []}).1 with
              | suspended _ _ | divergent _ _ | refused _ _ | yielded _ _ => simp [forced] at h
              | finished forcedValue retained =>
                  simp only [forced] at h
                  obtain ⟨_,_,h⟩ := except_bind_ok h
                  obtain ⟨_,_,h⟩ := except_bind_ok h
                  obtain ⟨child,childEq,h⟩ := except_bind_ok h
                  cases h
                  obtain ⟨next,same,nextSettled,grows,forcedValid,steps⟩ :=
                    force_field_sound settled allocated forced
                  obtain ⟨childDeep,last,lastSame,lastSettled,lastGrows⟩ :=
                    ih _ forcedValue retained next child nextSettled forcedValid childEq
                  refine ⟨.variant ⟨.refl _,.inject _ _⟩ (deepEvaluates_steps steps childDeep),last,?_,lastSettled,
                    Nat.le_trans grows lastGrows⟩
                  intro address old
                  exact (same address old).trans (lastSame address (Nat.lt_of_lt_of_le old grows))
      | record fields =>
          simp only [materializeWith] at h
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · split at h
                · cases h
                · obtain ⟨_,_,h⟩ := except_bind_ok h
                  obtain ⟨_,_,h⟩ := except_bind_ok h
                  obtain ⟨_,_,h⟩ := except_bind_ok h
                  obtain ⟨_,_,h⟩ := except_bind_ok h
                  obtain ⟨pair,folded,h⟩ := except_bind_ok h
                  cases h
                  have fieldsValid : ∀ field ∈ fields, field.2 < state.heap.size := valid
                  have done := foldlM_fieldsInvariant (origin := state) (meaning := meaning) ?stepOk fields [] _ pair
                    fieldsValid ?start folded
                  case start => exact ⟨by simpa using DeepFields.nil,meaning,fun _ _ => rfl,settled,Nat.le_refl _⟩
                  case stepOk =>
                    intro processed accumulated field stepResult allocatedField invariant body
                    try dsimp only at body
                    obtain ⟨deepPrefix,current,agree,currentSettled,grown⟩ := invariant
                    split at body
                    · cases body
                    · obtain ⟨_,_,body⟩ := except_bind_ok body
                      cases forced : (forceWith policy limits accumulated.2.2.ticks
                          {heap := accumulated.2.1.heap,control := .enter field.2,stack := []}).1 with
                      | suspended _ _ | divergent _ _ | refused _ _ | yielded _ _ => rw [forced] at body; cases body
                      | finished forcedValue retained =>
                          rw [forced] at body
                          obtain ⟨child,childEq,body⟩ := except_bind_ok body
                          cases body
                          have allocated : field.2 < accumulated.2.1.heap.size := Nat.lt_of_lt_of_le allocatedField grown
                          obtain ⟨next,same,nextSettled,grows,forcedValid,steps⟩ :=
                            force_field_sound currentSettled allocated forced
                          obtain ⟨childDeep,last,lastSame,lastSettled,lastGrows⟩ :=
                            ih _ forcedValue retained next child nextSettled forcedValid childEq
                          have named : current field.2 = meaning field.2 := (agree field.2 allocatedField).symm
                          refine ⟨?_,last,?_,lastSettled,?_⟩
                          · simp only [List.map_append,List.map_cons,List.map_nil,List.reverse_cons]
                            exact deepFields_append deepPrefix (named ▸ deepEvaluates_steps steps childDeep)
                          · intro address old
                            have a1 := agree address old
                            have a2 := same address (Nat.lt_of_lt_of_le old grown)
                            have a3 := lastSame address (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le old grown) grows)
                            exact a1.trans (a2.trans a3)
                          · exact Nat.le_trans grown (Nat.le_trans grows lastGrows)
                  obtain ⟨deepFields,current,agree,currentSettled,grown⟩ := done
                  refine ⟨.record ⟨.refl _,.record _⟩ (by simpa using deepFields),current,agree,currentSettled,grown⟩

/-- THE PLAN OUTPUT IS SOURCE SEMANTICS. Every `ExecutionWith` (the evidence
`executeWith` returns, under any policy — in particular the native capacity
profile — and any limits/budget) of a closed term is a finished `runBounded`
run of the same term, and its extracted Data deep-evaluates the source term. -/
 theorem execution_source_semantics {policy : State → Bool} {limits : Limits} {budget : Budget} {term : Term}
    (closed : Scoped 0 term) (execution : ExecutionWith policy limits budget term) :
    runBounded limits budget.ticks (initial term) = .finished execution.value execution.state ∧
      DeepEvaluates term execution.extraction.result.value := by
  have run := forceWith_finished (by rw [execution.runExact])
  refine ⟨run,?_⟩
  obtain ⟨count,_,prefixEq⟩ := runBounded_retained_prefix limits budget.ticks (initial term)
  rw [run] at prefixEq
  simp only [retainedState] at prefixEq
  have complete := runBounded_finished_control run
  obtain ⟨meaning,graph⟩ := rawRun_named_graph closed count (by rw [←prefixEq,complete]; trivial)
  rw [←prefixEq] at graph
  obtain ⟨lexical,busy,final,names,heap,residual,control,stack⟩ := graph
  have empty := final _ complete
  simp only [controlMeaning,complete,Option.some.injEq] at control
  subst residual
  have sourceSteps : Steps term (valueMeaning meaning execution.value) := by
    simpa only [empty,StackRealizes] using stack
  have valid : RuntimeValueValid execution.state.heap.size execution.value := by
    simpa [ControlValid,complete] using lexical.2.1
  have exact := execution.extraction.exact
  simp only [completeWith] at exact
  split at exact
  · cases exact
  · simp only [complete,empty] at exact
    obtain ⟨materialized,materializedEq,exact⟩ := except_bind_ok exact
    have sound := materialize_sound policy limits _ _ _ _ meaning materialized
      ⟨lexical,busy,empty,names,heap⟩ valid materializedEq
    split at exact
    all_goals (try split at exact)
    all_goals (first | (cases exact; exact deepEvaluates_steps sourceSteps sound.1) | cases exact)

/-! ## Non-vacuity: a real execution exists -/

/-- `{answer: 6 * 7}`: a lazy record whose field is demanded by extraction. -/
def sampleRecord : Term := .record [("answer",.binary .multiply (.nat 6) (.nat 7))]

theorem sampleRecord_closed : Scoped 0 sampleRecord := by
  refine .record ?_
  intro field member
  simp [List.mem_singleton] at member
  subst member
  exact .binary (.natural _) (.natural _)

theorem sampleRecord_executes :
    (executeWith (fun _ => true) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord).toBool = true := by decide +kernel

theorem sampleRecord_source_semantics :
    ∃ execution : ExecutionWith (fun _ => true) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord,
      DeepEvaluates sampleRecord execution.extraction.result.value := by
  cases executed : executeWith (fun _ => true) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord with
  | error failure =>
      have ok := sampleRecord_executes
      rw [executed] at ok
      cases ok
  | ok execution => exact ⟨execution,(execution_source_semantics sampleRecord_closed execution).2⟩

/-- The same program under the native scalar capacity profile (64-bit). -/
theorem sampleRecord_executes_native :
    (executeWith (ObjectiveBendDemandCapacity.allows ⟨64⟩) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord).toBool = true := by
  decide +kernel

theorem sampleRecord_native_source_semantics :
    ∃ execution : ExecutionWith (ObjectiveBendDemandCapacity.allows ⟨64⟩) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord,
      runBounded ⟨16,16⟩ 64 (initial sampleRecord) = .finished execution.value execution.state ∧
      DeepEvaluates sampleRecord execution.extraction.result.value := by
  cases executed : executeWith (ObjectiveBendDemandCapacity.allows ⟨64⟩) ⟨16,16⟩ ⟨8,64,256⟩ sampleRecord with
  | error failure =>
      have ok := sampleRecord_executes_native
      rw [executed] at ok
      cases ok
  | ok execution => exact ⟨execution,execution_source_semantics sampleRecord_closed execution⟩


/-! Axiom pins. -/
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.runBounded_terminal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms runBounded_terminal
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.forceWith_unrestricted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms forceWith_unrestricted
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.forceWith_policy_suspends' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms forceWith_policy_suspends
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.forceWith_finished' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms forceWith_finished
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.deepEvaluates_steps' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms deepEvaluates_steps
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.deepFields_append' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms deepFields_append
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.force_field_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms force_field_sound
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.foldlM_fieldsInvariant' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms foldlM_fieldsInvariant
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.except_bind_ok' does not depend on any axioms
-/
#guard_msgs in
#print axioms except_bind_ok
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.materialize_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms materialize_sound
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.execution_source_semantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms execution_source_semantics
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.sampleRecord_closed' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms sampleRecord_closed
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.sampleRecord_executes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms sampleRecord_executes
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.sampleRecord_source_semantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sampleRecord_source_semantics
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.sampleRecord_executes_native' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms sampleRecord_executes_native
/--
info: 'Minidregg.Theory.ObjectiveBendDemandDataSoundness.sampleRecord_native_source_semantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sampleRecord_native_source_semantics
end Minidregg.Theory.ObjectiveBendDemandDataSoundness
