/- The state a Plan extraction leaves is typed. Definitions: `yieldedPlanWith`
(`Theory.ObjectiveBendDemandData`), `checkpoint` (`Theory.ObjectiveBendDemandCollect`).

A yield stores the extraction's state: the yielded control and stack over the heap in
which every cell the extraction forced is cached. This module proves that state is typed
whenever the yielded state was, and was yielded by a transition (not handed in as a
yield): a perform yields only outside every shared cell (`stepRaw_yields_outside`,
`runBounded_yields_outside`), so no cell is being evaluated at a yield, so every forcing
the extraction runs starts from a typed `enter` with an empty stack and ends typed
(`typed_forceWith_any`), and the forced heap carries the yield's control and stack back
at the extended address types (`typed_yieldedPlanWith`). With `typed_settle` and
`typed_collect` this is `typed_checkpoint`.

What this module does NOT prove: that resuming the extraction's state ends as resuming
the yielded state (sharing transparency). That is `Kernel.ObjectiveResumeContract.
forcingTransparent_of_yieldedPlan`, over `Theory.ObjectiveBendDemandForcing*`. -/
import Theory.ObjectiveBendDemandSettleProofs
import Theory.ObjectiveBendDemandPreservation
namespace Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Theory.ObjectiveBendTypes (Ty)
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandTyping
open Minidregg.Theory.ObjectiveBendDemandInvariant
open Minidregg.Theory.ObjectiveBendDemandPreservation
set_option autoImplicit false

/-! ## A yield happens outside every shared cell -/

theorem forcingShared_false_iff (stack : List Frame) : forcingShared stack = false ↔ stackUpdates stack = [] := by
  induction stack with
  | nil => simp [forcingShared, stackUpdates]
  | cons frame rest ih =>
    cases frame <;> simp_all [forcingShared, stackUpdates]

theorem stepRaw_yields_outside {s : State} {plan : Address} (notYet : ∀ p, s.control ≠ .yielded p)
    (yields : (stepRaw s).control = .yielded plan) : forcingShared (stepRaw s).stack = false := by
  revert yields
  unfold stepRaw
  split <;> (repeat' split) <;> simp_all

theorem runBounded_of_yielded (limits : Limits) (ticks : Nat) {s : State} {plan : Address}
    (yielded : s.control = .yielded plan) : runBounded limits ticks s = .yielded plan s := by
  cases ticks <;> simp [runBounded, step, yielded]

theorem runBounded_zero_yielded {limits : Limits} {s y : State} {plan : Address}
    (ran : runBounded limits 0 s = .yielded plan y) : s.control = .yielded plan ∧ y = s := by
  unfold runBounded at ran
  split at ran <;> simp_all

/-- **A run that yields, yields outside every shared cell**, unless it was handed a
yielded state to begin with. -/
theorem runBounded_yields_outside (limits : Limits) :
    ∀ (ticks : Nat) (s : State) {plan : Address} {y : State}, (∀ p, s.control ≠ .yielded p) →
      runBounded limits ticks s = .yielded plan y → forcingShared y.stack = false := by
  intro ticks
  induction ticks with
  | zero =>
    intro s plan y notYet ran
    exact absurd (runBounded_zero_yielded ran).1 (notYet plan)
  | succ ticks ih =>
    intro s plan y notYet ran
    cases isActive : active s.control with
    | false =>
      rw [runBounded_succ_inactive isActive] at ran
      exact absurd (runBounded_zero_yielded ran).1 (notYet plan)
    | true =>
      rw [runBounded_succ_active isActive] at ran
      split at ran
      · by_cases nowYielded : ∃ q, (stepRaw s).control = .yielded q
        · obtain ⟨q, hq⟩ := nowYielded
          rw [runBounded_of_yielded limits ticks hq] at ran
          cases ran
          exact stepRaw_yields_outside notYet hq
        · exact ih _ (fun p hp => nowYielded ⟨p, hp⟩) ran
      · cases ran

/-! ## Typing through bounded runs and forcing -/

def outcomeState : Outcome → State
  | .finished _ state | .suspended _ state | .divergent _ state | .refused _ state | .yielded _ state => state

theorem outcomeState_runBounded_zero (limits : Limits) (s : State) :
    outcomeState (runBounded limits 0 s) = s := by
  unfold runBounded; split <;> rfl

theorem typed_runBounded_any {assumptions : Assumptions} (limits : Limits) {result : Ty} :
    ∀ (ticks : Nat) (types : AddressTypes) (s : State), StateTyping assumptions types s result →
      ∃ after, TypeExtension types after ∧
        Nonempty (StateTyping assumptions after (outcomeState (runBounded limits ticks s)) result) := by
  intro ticks
  induction ticks with
  | zero =>
    intro types s typed
    rw [outcomeState_runBounded_zero]
    exact ⟨types, type_extension_refl types, ⟨typed⟩⟩
  | succ ticks ih =>
    intro types s typed
    cases isActive : active s.control with
    | false =>
      rw [runBounded_succ_inactive isActive, outcomeState_runBounded_zero]
      exact ⟨types, type_extension_refl types, ⟨typed⟩⟩
    | true =>
      rw [runBounded_succ_active isActive]
      split
      · obtain ⟨after, extension, ⟨next⟩⟩ := typed_stepRaw_preserved typed
        obtain ⟨final, extension', typedFinal⟩ := ih after _ next
        exact ⟨final, type_extension_trans extension extension', typedFinal⟩
      · exact ⟨types, type_extension_refl types, ⟨typed⟩⟩

theorem typed_forceWith_any {assumptions : Assumptions} {policy : State → Bool} (limits : Limits) {result : Ty} :
    ∀ (ticks : Nat) (types : AddressTypes) (s : State), StateTyping assumptions types s result →
      ∃ after, TypeExtension types after ∧
        Nonempty (StateTyping assumptions after (outcomeState (forceWith policy limits ticks s).1) result) := by
  intro ticks
  induction ticks with
  | zero =>
    intro types s typed
    simp only [forceWith]
    rw [outcomeState_runBounded_zero]
    exact ⟨types, type_extension_refl types, ⟨typed⟩⟩
  | succ ticks ih =>
    intro types s typed
    cases isActive : active s.control with
    | false =>
      rw [forceWith_succ_inactive isActive, outcomeState_runBounded_zero]
      exact ⟨types, type_extension_refl types, ⟨typed⟩⟩
    | true =>
      rw [forceWith_succ_active isActive]
      split
      · exact ⟨types, type_extension_refl types, ⟨typed⟩⟩
      · obtain ⟨after, extension, ⟨next⟩⟩ := typed_runBounded_any limits 1 types s typed
        cases ran : runBounded limits 1 s with
        | suspended reason next' =>
          cases reason with
          | ticks =>
            rw [ran] at next
            obtain ⟨final, extension', typedFinal⟩ := ih after _ next
            exact ⟨final, type_extension_trans extension extension', typedFinal⟩
          | capacity => rw [ran] at next; exact ⟨after, extension, ⟨next⟩⟩
        | _ => rw [ran] at next; exact ⟨after, extension, ⟨next⟩⟩

theorem runBounded_finished_control (limits : Limits) :
    ∀ (ticks : Nat) (s : State) {value : RuntimeValue} {r : State},
      runBounded limits ticks s = .finished value r → r.control = .complete value := by
  intro ticks
  induction ticks with
  | zero =>
    intro s value r ran
    unfold runBounded at ran
    split at ran <;> simp_all
  | succ ticks ih =>
    intro s value r ran
    cases isActive : active s.control with
    | false =>
      rw [runBounded_succ_inactive isActive] at ran
      unfold runBounded at ran
      split at ran <;> simp_all
    | true =>
      rw [runBounded_succ_active isActive] at ran
      split at ran
      · exact ih _ ran
      · cases ran

theorem forceWith_finished_control {policy : State → Bool} (limits : Limits) :
    ∀ (ticks : Nat) (s : State) {value : RuntimeValue} {r : State},
      (forceWith policy limits ticks s).1 = .finished value r → r.control = .complete value := by
  intro ticks
  induction ticks with
  | zero => intro s value r ran; exact runBounded_finished_control limits 0 s ran
  | succ ticks ih =>
    intro s value r ran
    cases isActive : active s.control with
    | false =>
      rw [forceWith_succ_inactive isActive] at ran
      exact runBounded_finished_control limits 0 s ran
    | true =>
      rw [forceWith_succ_active isActive] at ran
      split at ran
      · cases ran
      · cases hr : runBounded limits 1 s with
        | suspended reason next =>
          rw [hr] at ran
          cases reason with
          | ticks => exact ih _ ran
          | capacity => cases ran
        | _ => rw [hr] at ran; simp only [continueForce] at ran; first | (cases ran; exact runBounded_finished_control limits 1 s hr) | cases ran

/-! ## The forced heap -/

/-- A heap every forcing may start from: typed, lexically valid, no cell being evaluated. -/
structure HeapGood (assumptions : Assumptions) (types : AddressTypes) (heap : Array Cell) : Prop where
  typed : HeapTyping assumptions types heap
  valid : ∀ (address : Nat) (cell : Cell), heap[address]? = some cell → CellValid heap.size cell
  idle : ∀ (address : Nat) (origin : Closure), heap[address]? ≠ some (.evaluating origin)
  assumptionsValid : assumptions.valid = true

theorem extension_length_le {before after : AddressTypes} (extension : TypeExtension before after) :
    before.length ≤ after.length := by
  cases before with
  | nil => simp
  | cons head tail =>
    have last := extension tail.length ((head :: tail)[tail.length]) (by simp)
    have := (List.getElem?_eq_some_iff.mp last).1
    simp at this ⊢; omega

theorem HeapGood.size_le {assumptions : Assumptions} {types after : AddressTypes} {heap heap' : Array Cell}
    (good : HeapGood assumptions types heap) (good' : HeapGood assumptions after heap')
    (extension : TypeExtension types after) : heap.size ≤ heap'.size := by
  rw [← good.typed.length, ← good'.typed.length]; exact extension_length_le extension

/-- Forcing a cell of a good heap starts from a typed state. -/
def enteredTyping {assumptions : Assumptions} {types : AddressTypes} {heap : Array Cell}
    (good : HeapGood assumptions types heap) {address : Nat} (bound : address < heap.size) :
    StateTyping assumptions types ⟨heap, .enter address, []⟩ (types[address]'(by rw [good.typed.length]; exact bound)) where
  current := types[address]'(by rw [good.typed.length]; exact bound)
  heap := good.typed
  control := .enter (by simp)
  stack := .nil _
  assumptionsValid := good.assumptionsValid
  lexical := ⟨good.valid, bound, by simp⟩
  busy := ⟨by simp [stackUpdates], by
    intro a
    simp only [stackUpdates, List.not_mem_nil, false_iff]
    intro ⟨origin, found⟩
    exact good.idle a origin found⟩
  terminalStack := fun _ _ => rfl

theorem good_of_finished {assumptions : Assumptions} {types : AddressTypes} {r : State} {result : Ty}
    {value : RuntimeValue} (typed : StateTyping assumptions types r result) (complete : r.control = .complete value) :
    HeapGood assumptions types r.heap ∧ RuntimeValueValid r.heap.size value := by
  have empty : r.stack = [] := typed.terminalStack value complete
  have controlValid := typed.lexical.2.1
  rw [complete] at controlValid
  refine ⟨⟨typed.heap, typed.lexical.1, ?_, typed.assumptionsValid⟩, controlValid⟩
  intro address origin found
  have := (typed.busy.2 address).mpr ⟨origin, found⟩
  rw [empty] at this
  simp [stackUpdates] at this

/-- Forcing a cell of a good heap to a finished value leaves a good heap and a valid value. -/
theorem good_forceWith {assumptions : Assumptions} {policy : State → Bool} (limits : Limits)
    {types : AddressTypes} {heap : Array Cell} (good : HeapGood assumptions types heap) {address : Nat}
    (bound : address < heap.size) (ticks : Nat) {value : RuntimeValue} {retained : State}
    (forced : (forceWith policy limits ticks ⟨heap, .enter address, []⟩).1 = .finished value retained) :
    ∃ after, TypeExtension types after ∧ HeapGood assumptions after retained.heap ∧
      RuntimeValueValid retained.heap.size value := by
  obtain ⟨after, extension, ⟨typed⟩⟩ := typed_forceWith_any (policy := policy) limits ticks types _
    (enteredTyping good bound)
  rw [forced] at typed
  obtain ⟨good', valid⟩ := good_of_finished typed (forceWith_finished_control limits ticks _ forced)
  exact ⟨after, extension, good', valid⟩

theorem good_foldlM {assumptions : Assumptions} {base : Nat}
    {step : List (String × Data) × State × Budget → String × Nat →
      Except (Failure × State × Budget) (List (String × Data) × State × Budget)}
    (stepGood : ∀ (acc : List (String × Data)) (st : State) (b : Budget) (field : String × Nat)
        (out : List (String × Data) × State × Budget) (types : AddressTypes),
      HeapGood assumptions types st.heap → base ≤ st.heap.size → field.2 < base →
      step (acc, st, b) field = .ok out →
      ∃ after, TypeExtension types after ∧ HeapGood assumptions after out.2.1.heap) :
    ∀ (fields : List (String × Nat)) (acc : List (String × Data)) (st : State) (b : Budget)
      (out : List (String × Data) × State × Budget) (types : AddressTypes),
      HeapGood assumptions types st.heap → base ≤ st.heap.size → (∀ field ∈ fields, field.2 < base) →
      fields.foldlM step (acc, st, b) = .ok out →
      ∃ after, TypeExtension types after ∧ HeapGood assumptions after out.2.1.heap := by
  intro fields
  induction fields with
  | nil =>
    intro acc st b out types good _ _ folded
    simp [List.foldlM] at folded
    subst folded
    exact ⟨types, type_extension_refl types, good⟩
  | cons field rest ih =>
    intro acc st b out types good baseLe inside folded
    simp only [List.foldlM_cons, except_bind_ok] at folded
    obtain ⟨mid, first, restFolded⟩ := folded
    obtain ⟨after, extension, good'⟩ := stepGood acc st b field mid types good baseLe (inside field (by simp)) first
    have midLe : base ≤ mid.2.1.heap.size := Nat.le_trans baseLe (good.size_le good' extension)
    obtain ⟨final, extension', good''⟩ := ih mid.1 mid.2.1 mid.2.2 out after good' midLe
      (fun x member => inside x (by simp [member])) (by
        have shape : mid = (mid.1, mid.2.1, mid.2.2) := rfl
        rw [← shape]; exact restFolded)
    exact ⟨final, type_extension_trans extension extension', good''⟩

/-- **Materialization keeps the heap good.** -/
theorem good_materializeWith {assumptions : Assumptions} {policy : State → Bool} (limits : Limits) :
    ∀ (depth : Nat) (budget : Budget) (value : RuntimeValue) (s : State) (r : Result) (types : AddressTypes),
      HeapGood assumptions types s.heap → RuntimeValueValid s.heap.size value →
      materializeWith policy limits depth budget value s = .ok r →
      ∃ after, TypeExtension types after ∧ HeapGood assumptions after r.state.heap := by
  intro depth
  induction depth with
  | zero => intro budget value s r types _ _ found; simp [materializeWith] at found
  | succ depth ih =>
    intro budget value s r types good valid found
    cases value with
    | natural n =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · simp at found; rw [← found]; exact ⟨types, type_extension_refl types, good⟩
    | boolean b =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · simp at found; rw [← found]; exact ⟨types, type_extension_refl types, good⟩
    | label l =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · simp at found; rw [← found]; exact ⟨types, type_extension_refl types, good⟩
    | closure body environment => simp [materializeWith] at found; split at found <;> simp at found
    | specification metadata extension => simp [materializeWith] at found; split at found <;> simp at found
    | prototype spec target => simp [materializeWith] at found; split at found <;> simp at found
    | variant label payload =>
      have bound : payload < s.heap.size := valid
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · cases forced : (forceWith policy limits budget.ticks ⟨s.heap, .enter payload, []⟩).1 with
          | finished value retained =>
            rw [forced] at found
            obtain ⟨after, extension, good', valid'⟩ := good_forceWith limits good bound budget.ticks forced
            simp at found
            obtain ⟨a, materialized, rfl⟩ := found
            obtain ⟨final, extension', good''⟩ := ih _ _ _ _ _ good' valid' materialized
            exact ⟨final, type_extension_trans extension extension', good''⟩
          | _ => rw [forced] at found; simp at found
    | record fields =>
      have inside : ∀ field ∈ fields, field.2 < s.heap.size := fun field member => valid field member
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · split at found
            · simp at found
            · obtain ⟨out, folded, rfl⟩ := (except_map_ok _ _ _).mp found
              refine good_foldlM (base := s.heap.size) ?_ fields [] s _ out types good (Nat.le_refl _) inside folded
              intro acc st b field out types' stGood baseLe fieldIn stepped
              simp only at stepped
              split at stepped
              · simp at stepped
              · cases forced : (forceWith policy limits b.ticks ⟨st.heap, .enter field.2, []⟩).1 with
                | finished value retained =>
                  rw [forced] at stepped
                  obtain ⟨after, extension, good', valid'⟩ :=
                    good_forceWith limits stGood (Nat.lt_of_lt_of_le fieldIn baseLe) b.ticks forced
                  simp at stepped
                  obtain ⟨a, materialized, rfl⟩ := stepped
                  obtain ⟨final, extension', good''⟩ := ih _ _ _ _ _ good' valid' materialized
                  exact ⟨final, type_extension_trans extension extension', good''⟩
                | _ => rw [forced] at stepped; simp at stepped
          · simp at found

/-- **The extraction's state is typed**: if the yielded state is typed and was yielded
outside every shared cell, the state the Plan extraction leaves (the yield's control and
stack over the forced heap) is typed at an extension of its address types. -/
theorem typed_yieldedPlanWith {assumptions : Assumptions} {types : AddressTypes} {y : State} {result : Ty}
    {policy : State → Bool} {limits : Limits} {budget : Budget} {r : Result}
    (typed : StateTyping assumptions types y result) (outside : forcingShared y.stack = false)
    (found : yieldedPlanWith policy limits budget y = .ok r) :
    ∃ after, TypeExtension types after ∧ Nonempty (StateTyping assumptions after r.state result) := by
  have noUpdates := (forcingShared_false_iff y.stack).mp outside
  unfold yieldedPlanWith at found
  split at found
  · rename_i plan yielded
    simp only at found
    have good : HeapGood assumptions types y.heap := ⟨typed.heap, typed.lexical.1, by
      intro address origin cell
      have := (typed.busy.2 address).mpr ⟨origin, cell⟩
      rw [noUpdates] at this; simp at this, typed.assumptionsValid⟩
    have planBound : plan < y.heap.size := by
      have := typed.lexical.2.1; rw [yielded] at this; exact this
    cases forced : forceWith policy limits budget.ticks ⟨y.heap, .enter plan, []⟩ with
    | mk outcome ticks =>
      rw [forced] at found
      cases outcome with
      | finished value retained =>
        obtain ⟨after, extension, good', valid'⟩ :=
          good_forceWith limits good planBound budget.ticks (by rw [forced])
        simp at found
        obtain ⟨a, materialized, rfl⟩ := found
        obtain ⟨final, extension', good''⟩ := good_materializeWith limits _ _ _ _ _ _ good' valid' materialized
        have ext := type_extension_trans extension extension'
        have sizeLe : y.heap.size ≤ a.state.heap.size := good.size_le good'' ext
        refine ⟨final, ext, ⟨{
          current := typed.current
          heap := good''.typed
          control := ControlTyping.weaken ext typed.control
          stack := StackTyping.weaken ext typed.stack
          assumptionsValid := typed.assumptionsValid
          lexical := ⟨good''.valid, controlValid_mono typed.lexical.2.1 sizeLe,
            fun frame member => frameValid_mono (typed.lexical.2.2 frame member) sizeLe⟩
          busy := ⟨by simp [noUpdates], by
            intro address
            simp only [noUpdates, List.not_mem_nil, false_iff]
            intro ⟨origin, cell⟩
            exact good''.idle address origin cell⟩
          terminalStack := by
            intro value complete
            simp only at complete
            rw [yielded] at complete; cases complete }⟩⟩
      | _ => simp at found
  · simp at found

/-- **What a yield stores is typed**: the extraction's state, settled and collected. -/
theorem typed_checkpoint {assumptions : Assumptions} {types : AddressTypes} {y : State} {result : Ty}
    {policy : State → Bool} {limits : Limits} {budget : Budget} {r : Result}
    (typed : StateTyping assumptions types y result) (outside : forcingShared y.stack = false)
    (found : yieldedPlanWith policy limits budget y = .ok r) :
    ∃ after, Nonempty (StateTyping assumptions after (checkpoint r.state) result) := by
  obtain ⟨after, _, ⟨forced⟩⟩ := typed_yieldedPlanWith typed outside found
  exact ⟨_, ⟨typed_collect (typed_settle forced)⟩⟩

theorem yieldedPlanWith_control {policy : State → Bool} {limits : Limits} {budget : Budget} {y : State}
    {r : Result} (found : yieldedPlanWith policy limits budget y = .ok r) :
    r.state.control = y.control ∧ r.state.stack = y.stack := by
  unfold yieldedPlanWith at found
  split at found
  · simp only at found
    split at found
    · simp at found
      obtain ⟨a, _, rfl⟩ := found
      exact ⟨rfl, rfl⟩
    all_goals simp at found
  · simp at found

/-! ## The forced checkpoint can be larger than the unforced one

Collection never grows a state, and settling never changes its size; forcing can. A
Plan that is a small closure over a cell the continuation also holds becomes, forced,
the whole structure that closure computes, all of it live. Here the Plan reads cell 0,
a suspended record of three fields; the stack holds cell 0 too. Unforced and collected:
two cells. Forced, settled and collected: five (cell 0's record, the Plan cell and the
three field cells, all reachable from the stack through cell 0). So under heap limits
counted from zero a resumed forced checkpoint may run out of heap where the unforced one
would not (`Kernel.ObjectiveResumeContract.absolute_limits_refuted`); the kernel counts a
segment's limits from its own heap end (`limitsPast`, `Kernel.ObjectiveActivity.
segmentLimits`), under which it resumes exactly (`ObjectiveResumeContract.
largerYield_resumes_exactly`, `runSegment_stored_complete`). -/

def largerYield : State :=
  ⟨#[.suspended ⟨.record [("a", .nat 1), ("b", .nat 2), ("c", .nat 3)], []⟩, .suspended ⟨.bound 0, [0]⟩],
   .yielded 1, [.argument (.bound 0) [0]]⟩

def largerLimits : Limits := ⟨64, 64⟩
def largerBudget : Budget := ⟨16, 64, 256⟩

theorem largerYield_checkpoint_grows :
    (collect largerYield).heap.size = 2 ∧
      ((yieldedPlan largerLimits largerBudget largerYield).toOption.map
        fun r => (checkpoint r.state).heap.size) = some 5 := by
  decide +kernel

end Minidregg.Theory.ObjectiveBendDemandCollect
