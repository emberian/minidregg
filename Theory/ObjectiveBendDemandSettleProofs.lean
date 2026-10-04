/- Settling a checkpoint changes no transition. Definitions: `settle`, `checkpoint` in
`Theory.ObjectiveBendDemandCollect`.

The machine reads a cached cell's VALUE only; a cached cell's origin is never read again
(`stepRaw` reads an origin only from an `evaluating` cell, at its update frame). So two
states that differ only in the origins of cached cells take the same transitions. The
relation is `Agree s t`: erasing every cached origin (`eraseState`) makes them equal.

* `erase_stepRaw` / `agree_stepRaw`: one transition agrees.
* `agree_runBounded`: bounded runs agree EXACTLY, capacity suspensions included (heap
  sizes and stacks are equal, so every capacity check is the same check).
* `agree_resume`, `agree_forceWith`, `agree_materializeWith`, `agree_completeWith`,
  `agree_yieldedPlanWith`: forcing and extraction give the same Data and budget.
* `agree_settle`: `Agree s (settle s)`; `typed_settle`: a settled state is typed at the
  same address types (the self origin is typed at the cell's own type).
* `settle_resume_segment`: the kernel's segment from a settled state agrees with the
  segment from the state it settled. -/
import Theory.ObjectiveBendDemandCollectProofs
namespace Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
set_option autoImplicit false
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Theory.ObjectiveBendTypes (Ty Binding Quantity variableUses safeUses safeQuantity validContext)
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandTyping
open Minidregg.Theory.ObjectiveBendDemandInvariant

/-! ## Erasing cached origins -/

/-- Forget a cached cell's origin. -/
def eraseCell : Cell → Cell
  | .cached _ value => .cached ⟨.nat 0, []⟩ value
  | cell => cell

@[simp] theorem eraseCell_eraseCell (cell : Cell) : eraseCell (eraseCell cell) = eraseCell cell := by
  cases cell <;> rfl

@[simp] theorem eraseCell_suspended (origin : Closure) : eraseCell (.suspended origin) = .suspended origin := rfl
@[simp] theorem eraseCell_evaluating (origin : Closure) : eraseCell (.evaluating origin) = .evaluating origin := rfl
@[simp] theorem eraseCell_cached (origin : Closure) (value : RuntimeValue) :
    eraseCell (.cached origin value) = .cached ⟨.nat 0, []⟩ value := rfl

@[simp] theorem eraseCell_comp : eraseCell ∘ eraseCell = eraseCell := by
  funext cell; simp

def eraseState (state : State) : State := ⟨state.heap.map eraseCell, state.control, state.stack⟩

/-- Two states agree up to the origins of cached cells. -/
def Agree (s t : State) : Prop := eraseState s = eraseState t

theorem Agree.refl (s : State) : Agree s s := rfl
theorem Agree.symm {s t : State} (agree : Agree s t) : Agree t s := Eq.symm agree
theorem Agree.trans {s t u : State} (one : Agree s t) (two : Agree t u) : Agree s u := Eq.trans one two

theorem Agree.control {s t : State} (agree : Agree s t) : s.control = t.control := by
  have same := congrArg State.control (show eraseState s = eraseState t from agree)
  simpa [eraseState] using same
theorem Agree.stack {s t : State} (agree : Agree s t) : s.stack = t.stack := by
  have same := congrArg State.stack (show eraseState s = eraseState t from agree)
  simpa [eraseState] using same
theorem Agree.heap {s t : State} (agree : Agree s t) : s.heap.map eraseCell = t.heap.map eraseCell :=
  congrArg State.heap (show eraseState s = eraseState t from agree)
theorem Agree.size {s t : State} (agree : Agree s t) : s.heap.size = t.heap.size := by
  have := congrArg Array.size agree.heap
  simpa using this

theorem Agree.mk' {s t : State} (heap : s.heap.map eraseCell = t.heap.map eraseCell)
    (control : s.control = t.control) (stack : s.stack = t.stack) : Agree s t := by
  unfold Agree eraseState; rw [heap, control, stack]

theorem agree_eraseState (s : State) : Agree (eraseState s) s := by
  unfold Agree eraseState; simp [Array.map_map]

theorem eraseState_eraseState (s : State) : eraseState (eraseState s) = eraseState s :=
  agree_eraseState s

/-! ## One transition -/

theorem erase_set! (heap : Array Cell) (address : Nat) (cell : Cell) :
    (heap.set! address cell).map eraseCell = (heap.map eraseCell).set! address (eraseCell cell) := by
  simp [Array.set!_eq_setIfInBounds, Array.map_setIfInBounds]

theorem erase_allocateFields (heap : Array Cell) (environment : Environment) (fields : List (String × Term)) :
    allocateFields (heap.map eraseCell) environment fields =
      ((allocateFields heap environment fields).1.map eraseCell, (allocateFields heap environment fields).2) := by
  have loop : ∀ (fields : List (String × Term)) (heap : Array Cell) (names : List (String × Address)),
      fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
        (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (heap.map eraseCell, names) =
      ((fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
        (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (heap, names)).1.map eraseCell,
       (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
        (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (heap, names)).2) := by
    intro fields
    induction fields with
    | nil => intro heap names; rfl
    | cons field rest ih =>
      intro heap names
      simp only [List.foldl_cons, Array.size_map]
      have := ih (heap.push (.suspended ⟨field.2,environment⟩)) ((field.1, heap.size) :: names)
      rw [← this]
      simp [Array.map_push]
  simp only [allocateFields]
  rw [loop]

/-- **Erasure commutes with a transition** (up to the erasure of its result): the
machine never reads a cached cell's origin. -/
theorem erase_stepRaw (s : State) : eraseState (stepRaw (eraseState s)) = eraseState (stepRaw s) := by
  obtain ⟨heap, control, stack⟩ := s
  cases control with
  | complete value => simp [stepRaw, eraseState, Array.map_map]
  | refused reason => simp [stepRaw, eraseState, Array.map_map]
  | blackhole address => simp [stepRaw, eraseState, Array.map_map]
  | yielded plan => simp [stepRaw, eraseState, Array.map_map]
  | enter address =>
    cases found : heap[address]? with
    | none => simp [stepRaw, eraseState, Array.getElem?_map, found, Array.map_map]
    | some cell =>
      cases cell <;>
        simp [stepRaw, eraseState, Array.getElem?_map, found, Array.map_map]
  | evaluate term environment =>
    cases term <;> simp [stepRaw, eraseState, Array.map_map, Array.map_push, erase_allocateFields] <;>
      (try split) <;> simp [Array.map_map, Array.map_push]
  | returned value =>
    cases stack with
    | nil => simp [stepRaw, eraseState, Array.map_map]
    | cons frame rest =>
      cases frame with
      | update address =>
        cases found : heap[address]? with
        | none => simp [stepRaw, eraseState, Array.getElem?_map, found, Array.map_map]
        | some cell =>
          cases cell <;>
            simp [stepRaw, eraseState, Array.getElem?_map, found, Array.map_map]
      | _ =>
        simp [stepRaw, eraseState, Array.map_map, erase_allocateFields] <;>
          (repeat' split) <;> simp [Array.map_map, Array.map_push]

theorem agree_stepRaw {s t : State} (agree : Agree s t) : Agree (stepRaw s) (stepRaw t) := by
  unfold Agree
  rw [← erase_stepRaw s, ← erase_stepRaw t, agree]

/-! ## Bounded runs agree exactly -/

def eraseOutcome : Outcome → Outcome
  | .finished value state => .finished value (eraseState state)
  | .suspended reason state => .suspended reason (eraseState state)
  | .divergent address state => .divergent address (eraseState state)
  | .refused reason state => .refused reason (eraseState state)
  | .yielded plan state => .yielded plan (eraseState state)

/-- Outcomes agree: same constructor, same payload, agreeing retained states. -/
def OutcomeAgree (o o' : Outcome) : Prop := eraseOutcome o = eraseOutcome o'

theorem agree_step (limits : Limits) {s t : State} (agree : Agree s t) :
    OutcomeAgree (step limits s) (step limits t) := by
  have next := agree_stepRaw agree
  have sizes := next.size
  have stacks := next.stack
  have control := agree.control
  have same : eraseState s = eraseState t := agree
  have sameNext : eraseState (stepRaw s) = eraseState (stepRaw t) := next
  show eraseOutcome _ = eraseOutcome _
  unfold step
  rw [control]
  by_cases fits : (stepRaw t).heap.size ≤ limits.heap ∧ (stepRaw t).stack.length ≤ limits.stack
  · cases hc : t.control <;> simp [fits, eraseOutcome, same, sameNext, sizes, stacks]
  · cases hc : t.control <;> simp [fits, eraseOutcome, same, sizes, stacks]

theorem agree_runBounded_zero (limits : Limits) {s t : State} (agree : Agree s t) :
    OutcomeAgree (runBounded limits 0 s) (runBounded limits 0 t) := by
  unfold runBounded
  rw [agree.control]
  split <;> simp only [OutcomeAgree, eraseOutcome] <;> exact congrArg _ agree

/-- **Bounded runs agree exactly**, capacity suspensions included. -/
theorem agree_runBounded (limits : Limits) :
    ∀ (ticks : Nat) (s t : State), Agree s t → OutcomeAgree (runBounded limits ticks s) (runBounded limits ticks t) := by
  intro ticks
  induction ticks with
  | zero => intro s t agree; exact agree_runBounded_zero limits agree
  | succ ticks ih =>
    intro s t agree
    have stepped := agree_step limits agree
    simp only [runBounded]
    cases hs : step limits s with
    | suspended reason next =>
      cases ht : step limits t <;> rw [hs, ht] at stepped <;>
        simp only [OutcomeAgree, eraseOutcome, Outcome.suspended.injEq, reduceCtorEq] at stepped
      obtain ⟨same, rest⟩ := stepped
      subst same
      cases reason with
      | ticks => exact ih _ _ rest
      | capacity => simp only [OutcomeAgree, eraseOutcome, rest]
    | finished value next | divergent value next | refused value next | yielded value next =>
      cases ht : step limits t <;> rw [hs, ht] at stepped <;>
        simp only [OutcomeAgree, eraseOutcome, Outcome.finished.injEq, Outcome.divergent.injEq,
          Outcome.refused.injEq, Outcome.yielded.injEq, reduceCtorEq] at stepped
      all_goals (obtain ⟨same, rest⟩ := stepped; subst same; simp only [OutcomeAgree, eraseOutcome, rest])

theorem agree_resume {s t : State} (agree : Agree s t) (response : Term) {s' : State}
    (resumed : resume response s = some s') :
    ∃ t', resume response t = some t' ∧ Agree s' t' := by
  obtain ⟨plan, yielded⟩ := resume_requires_yield response s (by rw [resumed]; rfl)
  have controlT : t.control = .yielded plan := by rw [← agree.control, yielded]
  simp only [resume, yielded] at resumed
  cases resumed
  refine ⟨{t with control := .evaluate response []}, by simp [resume, controlT], ?_⟩
  exact Agree.mk' agree.heap rfl agree.stack

/-! ## Forcing and extraction agree -/

theorem active_of_agree {s t : State} (agree : Agree s t) : active t.control = active s.control := by
  rw [agree.control]

/-- **Forcing agrees**, for any policy that agreeing states pass alike. -/
theorem agree_forceWith {policy : State → Bool}
    (respects : ∀ s t, Agree s t → policy s = true → policy t = true) (limits : Limits) :
    ∀ (ticks : Nat) (s t : State), Agree s t →
      OutcomeAgree (forceWith policy limits ticks s).1 (forceWith policy limits ticks t).1 ∧
        (forceWith policy limits ticks t).2 = (forceWith policy limits ticks s).2 := by
  intro ticks
  induction ticks with
  | zero => intro s t agree; exact ⟨agree_runBounded_zero limits agree, rfl⟩
  | succ ticks ih =>
    intro s t agree
    have activeT := active_of_agree agree
    cases isActive : active s.control with
    | false =>
      rw [forceWith_succ_inactive isActive, forceWith_succ_inactive (by rw [activeT, isActive])]
      exact ⟨agree_runBounded_zero limits agree, rfl⟩
    | true =>
      rw [forceWith_succ_active isActive, forceWith_succ_active (by rw [activeT, isActive])]
      cases allowed : policy s with
      | false =>
        cases allowedT : policy t with
        | false =>
          simp only [OutcomeAgree, eraseOutcome, if_true]
          exact ⟨congrArg _ agree, trivial⟩
        | true =>
          have := respects t s agree.symm allowedT
          rw [allowed] at this; cases this
      | true =>
        have allowedT := respects s t agree allowed
        simp only [allowedT, Bool.true_eq_false, if_false]
        have ran := agree_runBounded limits 1 s t agree
        cases hs : runBounded limits 1 s with
        | suspended reason next =>
          cases ht : runBounded limits 1 t <;> rw [hs, ht] at ran <;>
            simp only [OutcomeAgree, eraseOutcome, Outcome.suspended.injEq, reduceCtorEq] at ran
          obtain ⟨same, rest⟩ := ran
          subst same
          cases reason with
          | ticks => exact ih _ _ rest
          | capacity => exact ⟨by simp only [continueForce, OutcomeAgree, eraseOutcome, rest], rfl⟩
        | finished value next | divergent value next | refused value next | yielded value next =>
          cases ht : runBounded limits 1 t <;> rw [hs, ht] at ran <;>
            simp only [OutcomeAgree, eraseOutcome, Outcome.finished.injEq, Outcome.divergent.injEq,
              Outcome.refused.injEq, Outcome.yielded.injEq, reduceCtorEq] at ran
          all_goals (obtain ⟨same, rest⟩ := ran; subst same
                     exact ⟨by simp only [continueForce, OutcomeAgree, eraseOutcome, rest], rfl⟩)

/-- Extraction results agree: same Data, same remaining budget, agreeing states. -/
def ResultAgree (r r' : Result) : Prop :=
  r'.value = r.value ∧ r'.remaining = r.remaining ∧ Agree r.state r'.state

theorem foldlM_agree
    {step : List (String × Data) × State × Budget → String × Nat →
      Except (Failure × State) (List (String × Data) × State × Budget)}
    (stepAgree : ∀ (acc : List (String × Data)) (st st' : State) (b : Budget) (field : String × Nat)
        (out : List (String × Data) × State × Budget),
      Agree st st' → step (acc, st, b) field = .ok out →
      ∃ out', step (acc, st', b) field = .ok out' ∧ out'.1 = out.1 ∧ out'.2.2 = out.2.2 ∧
        Agree out.2.1 out'.2.1) :
    ∀ (fields : List (String × Nat)) (acc : List (String × Data)) (st st' : State) (b : Budget)
      (out : List (String × Data) × State × Budget),
      Agree st st' → fields.foldlM step (acc, st, b) = .ok out →
      ∃ out', fields.foldlM step (acc, st', b) = .ok out' ∧
        out'.1 = out.1 ∧ out'.2.2 = out.2.2 ∧ Agree out.2.1 out'.2.1 := by
  intro fields
  induction fields with
  | nil =>
    intro acc st st' b out agree folded
    simp [List.foldlM] at folded
    subst folded
    exact ⟨_, rfl, rfl, rfl, agree⟩
  | cons field rest ih =>
    intro acc st st' b out agree folded
    simp only [List.foldlM_cons, except_bind_ok] at folded
    obtain ⟨mid, first, restFolded⟩ := folded
    obtain ⟨mid', first', same1, same2, midAgree⟩ := stepAgree acc st st' b field mid agree first
    obtain ⟨out', folded', outSame1, outSame2, outAgree⟩ :=
      ih mid.1 mid.2.1 mid'.2.1 mid.2.2 out midAgree restFolded
    refine ⟨out', ?_, outSame1, outSame2, outAgree⟩
    simp only [List.foldlM_cons, except_bind_ok]
    refine ⟨mid', first', ?_⟩
    have shape : mid' = (mid.1, mid'.2.1, mid.2.2) := by
      obtain ⟨a, b, c⟩ := mid'
      simp only at same1 same2
      rw [same1, same2]
    rw [shape]; exact folded'

theorem agree_entered {s t : State} (agree : Agree s t) (address : Nat) :
    Agree ⟨s.heap, .enter address, []⟩ ⟨t.heap, .enter address, []⟩ :=
  Agree.mk' agree.heap rfl rfl

/-- **Materialization agrees.** -/
theorem agree_materializeWith {policy : State → Bool}
    (respects : ∀ s t, Agree s t → policy s = true → policy t = true) (limits : Limits) :
    ∀ (depth : Nat) (budget : Budget) (value : RuntimeValue) (s t : State) (r : Result),
      Agree s t → materializeWith policy limits depth budget value s = .ok r →
      ∃ r', materializeWith policy limits depth budget value t = .ok r' ∧ ResultAgree r r' := by
  intro depth
  induction depth with
  | zero => intro budget value s t r _ found; simp [materializeWith] at found
  | succ depth ih =>
    intro budget value s t r agree found
    cases value with
    | natural n =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨{ r with state := t }, ?_, rfl, rfl, ?_⟩
          · rw [← found]; simp [materializeWith, c1, c2]
          · rw [← found]; exact agree
    | boolean b =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨{ r with state := t }, ?_, rfl, rfl, ?_⟩
          · rw [← found]; simp [materializeWith, c1, c2]
          · rw [← found]; exact agree
    | label l =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨{ r with state := t }, ?_, rfl, rfl, ?_⟩
          · rw [← found]; simp [materializeWith, c1, c2]
          · rw [← found]; exact agree
    | closure body environment => simp [materializeWith] at found; split at found <;> simp at found
    | specification metadata extension => simp [materializeWith] at found; split at found <;> simp at found
    | prototype spec target => simp [materializeWith] at found; split at found <;> simp at found
    | variant label payload =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          cases forced : (forceWith policy limits budget.ticks ⟨s.heap, .enter payload, []⟩).1 with
          | finished value retained =>
            rw [forced] at found
            have ⟨rel, ticksEq⟩ := agree_forceWith respects limits budget.ticks _ _ (agree_entered agree payload)
            rw [forced] at rel
            cases forcedT : (forceWith policy limits budget.ticks ⟨t.heap, .enter payload, []⟩).1 <;>
              rw [forcedT] at rel <;>
              simp only [OutcomeAgree, eraseOutcome, Outcome.finished.injEq, reduceCtorEq] at rel
            obtain ⟨valueEq, retainedAgree⟩ := rel
            subst valueEq
            simp at found
            obtain ⟨a, materialized, rfl⟩ := found
            obtain ⟨a', materialized', aValue, aRemaining, aAgree⟩ := ih _ _ _ _ _ retainedAgree materialized
            refine ⟨⟨.variant label a'.value, a'.state, a'.remaining⟩, ?_, by simp [aValue], aRemaining, aAgree⟩
            simp [materializeWith, c1, c2, forcedT, ticksEq, materialized']
          | _ => rw [forced] at found; simp at found
    | record fields =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · split at found
            · simp at found
            · rename_i c1 c2 c3 c4
              obtain ⟨out, folded, rfl⟩ := (except_map_ok _ _ _).mp found
              have key := foldlM_agree ?_ fields [] s t _ out agree folded
              · obtain ⟨out', folded', same1, same2, outAgree⟩ := key
                refine ⟨⟨.record out'.1.reverse, out'.2.1, out'.2.2⟩, ?_, by simp [same1], by simp [same2], outAgree⟩
                simp [materializeWith, c1, c2, c3, c4, folded']
              · intro acc st st' b field out stAgree stepped
                simp only at stepped ⊢
                split at stepped
                · simp at stepped
                · rename_i cond
                  cases forced : (forceWith policy limits b.ticks ⟨st.heap, .enter field.2, []⟩).1 with
                  | finished value retained =>
                    rw [forced] at stepped
                    have ⟨rel, ticksEq⟩ := agree_forceWith respects limits b.ticks _ _ (agree_entered stAgree field.2)
                    rw [forced] at rel
                    cases forcedT : (forceWith policy limits b.ticks ⟨st'.heap, .enter field.2, []⟩).1 <;>
                      rw [forcedT] at rel <;>
                      simp only [OutcomeAgree, eraseOutcome, Outcome.finished.injEq, reduceCtorEq] at rel
                    obtain ⟨valueEq, retainedAgree⟩ := rel
                    subst valueEq
                    simp at stepped
                    obtain ⟨a, materialized, rfl⟩ := stepped
                    obtain ⟨a', materialized', aValue, aRemaining, aAgree⟩ :=
                      ih _ _ _ _ _ retainedAgree materialized
                    refine ⟨((field.1, a'.value) :: acc, a'.state, a'.remaining), ?_, by simp [aValue],
                      aRemaining, aAgree⟩
                    simp [cond, ticksEq, materialized']
                  | _ => rw [forced] at stepped; simp at stepped
          · simp at found

/-- **Completion agrees.** -/
theorem agree_completeWith {policy : State → Bool}
    (respects : ∀ s t, Agree s t → policy s = true → policy t = true) (limits : Limits)
    (budget : Budget) {s t : State} {r : Result} (agree : Agree s t)
    (found : completeWith policy limits budget s = .ok r) :
    ∃ r', completeWith policy limits budget t = .ok r' ∧ ResultAgree r r' := by
  cases allowed : policy s with
  | false => simp [completeWith, allowed] at found
  | true =>
    have allowedT := respects s t agree allowed
    have controlEq := agree.control
    have stackEq := agree.stack
    unfold completeWith at found ⊢
    simp only [allowed, allowedT, Bool.not_true, Bool.false_eq_true, if_false] at found ⊢
    rw [← controlEq, ← stackEq]
    split at found
    · rename_i value _ _
      simp only [except_bind_ok] at found
      obtain ⟨a, materialized, rest⟩ := found
      obtain ⟨a', materialized', aValue, aRemaining, aAgree⟩ :=
        agree_materializeWith respects limits _ _ _ _ _ _ agree materialized
      split at rest
      · rename_i bytes encodedAt
        split at rest
        · simp at rest
        · rename_i small
          simp at rest; subst rest
          refine ⟨a', ?_, aValue, aRemaining, aAgree⟩
          simp [materialized', aValue, encodedAt, small]
      · simp at rest
    · simp at found

/-- **Plan extraction agrees.** -/
theorem agree_yieldedPlanWith {policy : State → Bool}
    (respects : ∀ s t, Agree s t → policy s = true → policy t = true) (limits : Limits)
    (budget : Budget) {s t : State} {r : Result} (agree : Agree s t)
    (found : yieldedPlanWith policy limits budget s = .ok r) :
    ∃ r', yieldedPlanWith policy limits budget t = .ok r' ∧ ResultAgree r r' := by
  have controlEq := agree.control
  have stackEq := agree.stack
  unfold yieldedPlanWith at found ⊢
  rw [← controlEq, ← stackEq]
  split at found
  · rename_i plan yielded
    have ⟨rel, ticksEq⟩ := agree_forceWith respects limits budget.ticks _ _ (agree_entered agree plan)
    simp only at found rel ticksEq ⊢
    cases forced : forceWith policy limits budget.ticks ⟨s.heap, .enter plan, []⟩ with
    | mk outcome ticks =>
      rw [forced] at found rel ticksEq
      cases outcome with
      | finished value retained =>
        cases forcedT : forceWith policy limits budget.ticks ⟨t.heap, .enter plan, []⟩ with
        | mk outcome' ticks' =>
          rw [forcedT] at rel ticksEq
          simp only at rel ticksEq
          subst ticksEq
          cases outcome' <;>
            simp only [OutcomeAgree, eraseOutcome, Outcome.finished.injEq, reduceCtorEq] at rel
          obtain ⟨valueEq, retainedAgree⟩ := rel
          subst valueEq
          simp at found
          obtain ⟨a, materialized, rfl⟩ := found
          obtain ⟨a', materialized', aValue, aRemaining, aAgree⟩ :=
            agree_materializeWith respects limits _ _ _ _ _ _ retainedAgree materialized
          refine ⟨{a' with state := {a'.state with control := s.control, stack := s.stack}},
            ?_, aValue, aRemaining, Agree.mk' aAgree.heap rfl rfl⟩
          simp [materialized', yielded]
      | _ => simp at found
  · simp at found

/-! ## Settling agrees, and keeps typing -/

theorem settle_heap_erased (state : State) :
    (settle state).heap.map eraseCell = state.heap.map eraseCell := by
  apply Array.ext_getElem?
  intro i
  simp only [settle, Array.getElem?_map, Array.getElem?_mapIdx, Option.map_map]
  cases state.heap[i]? with
  | none => rfl
  | some cell => cases cell <;> rfl

/-- **A settled state agrees with the state it settled.** -/
theorem agree_settle (state : State) : Agree state (settle state) :=
  Agree.mk' (settle_heap_erased state).symm rfl rfl

theorem settle_getElem? (state : State) (address : Nat) :
    (settle state).heap[address]? = (state.heap[address]?).map (settleCell address) := by
  simp [settle, Array.getElem?_mapIdx]

@[simp] theorem settle_size (state : State) : (settle state).heap.size = state.heap.size := by
  simp [settle]

/-- **Resuming a settled state ends as resuming the state it settled**: with any
response, for any limits and tick budget, the bounded runs agree exactly. -/
theorem settle_resume_runBounded {state resumed : State} {response : Term}
    (yielded : resume response state = some resumed) (limits : Limits) (ticks : Nat) :
    ∃ resumed', resume response (settle state) = some resumed' ∧
      OutcomeAgree (runBounded limits ticks resumed) (runBounded limits ticks resumed') := by
  obtain ⟨resumed', again, agree⟩ := agree_resume (agree_settle state) response yielded
  exact ⟨resumed', again, agree_runBounded limits ticks _ _ agree⟩

/-- The self origin is typed at the cell's own assigned type: the closure `bound 0`
over the one-address environment `[address]`, its binding affine (read at most once). -/
def selfOriginTyping (assumptions : Assumptions) {types : AddressTypes} {address : Nat} {type : Ty}
    (assigned : types[address]? = some type) : ClosureTyping assumptions types (selfOrigin address) type where
  context := [⟨type, .affine⟩]
  uses := variableUses [⟨type, .affine⟩] 0
  environment := (EnvironmentTyping.empty types).cons (binding := ⟨type, .affine⟩) assigned
  source := .bound (binding := ⟨type, .affine⟩) rfl
  safe := by simp [safeUses, variableUses, safeQuantity]
  contextValid := by simp [validContext]

theorem heapTyping_settle {assumptions : Assumptions} {types : AddressTypes} {state : State}
    (typed : HeapTyping assumptions types state.heap) : HeapTyping assumptions types (settle state).heap := by
  refine ⟨by simp [typed.length], ?_⟩
  intro address type assigned
  obtain ⟨stored, found, cellTyped⟩ := typed.cell address type assigned
  refine ⟨settleCell address stored, by rw [settle_getElem?, found]; rfl, ?_⟩
  cases cellTyped with
  | suspended origin pure => exact .suspended origin pure
  | evaluating origin pure => exact .evaluating origin pure
  | cached origin value pure => exact .cached (selfOriginTyping assumptions assigned) value pure

theorem lexical_settle {state : State} (lexical : LexicalInvariant state) : LexicalInvariant (settle state) := by
  obtain ⟨cells, control, frames⟩ := lexical
  refine ⟨?_, by rw [settle_size]; exact control, by rw [settle_size]; exact frames⟩
  intro address cell found
  rw [settle_getElem?] at found
  rw [settle_size]
  cases original : state.heap[address]? with
  | none => rw [original] at found; cases found
  | some stored =>
    rw [original] at found
    simp only [Option.map_some, Option.some.injEq] at found
    subst found
    have valid := cells address stored original
    have bound : address < state.heap.size := (Array.getElem?_eq_some_iff.mp original).1
    cases stored with
    | suspended origin => exact valid
    | evaluating origin => exact valid
    | cached origin value =>
      refine ⟨⟨.bound (by simp [selfOrigin]), ?_⟩, valid.2⟩
      intro x member
      simp only [selfOrigin, List.mem_singleton] at member
      subst member; exact bound

theorem busy_settle {state : State} (busy : BusyInvariant state) : BusyInvariant (settle state) := by
  refine ⟨busy.1, ?_⟩
  intro address
  show address ∈ stackUpdates state.stack ↔ ∃ origin, (settle state).heap[address]? = some (.evaluating origin)
  rw [busy.2 address, settle_getElem?]
  cases state.heap[address]? with
  | none => simp
  | some cell => cases cell <;> simp [settleCell]

/-- **A settled state is typed at the same address types.** -/
def typed_settle {assumptions : Assumptions} {types : AddressTypes} {state : State} {result : Ty}
    (typed : StateTyping assumptions types state result) : StateTyping assumptions types (settle state) result where
  current := typed.current
  heap := heapTyping_settle typed.heap
  control := typed.control
  stack := typed.stack
  assumptionsValid := typed.assumptionsValid
  lexical := lexical_settle typed.lexical
  busy := busy_settle typed.busy
  terminalStack := typed.terminalStack

/-! ## The kernel's segment from a settled state -/

/-- **The kernel's segment from a settled state** agrees exactly with the segment from
the state it settled: the same Plan address and Plan Data, the same result Data, the
same divergence and refusal, and agreeing retained states. -/
theorem settle_resume_segment {state resumed : State} {response : Term}
    (yielded : resume response state = some resumed) (limits : Limits) (ticks : Nat) (budget : Budget) :
    ∃ resumed', resume response (settle state) = some resumed' ∧
      (∀ plan y r, runBounded limits ticks resumed = .yielded plan y → yieldedPlan limits budget y = .ok r →
        ∃ y' r', runBounded limits ticks resumed' = .yielded plan y' ∧ Agree y y' ∧
          yieldedPlan limits budget y' = .ok r' ∧ ResultAgree r r') ∧
      (∀ value y r, runBounded limits ticks resumed = .finished value y → complete limits budget y = .ok r →
        ∃ y' r', runBounded limits ticks resumed' = .finished value y' ∧
          complete limits budget y' = .ok r' ∧ r'.value = r.value) ∧
      (∀ address y, runBounded limits ticks resumed = .divergent address y →
        ∃ y', runBounded limits ticks resumed' = .divergent address y') ∧
      (∀ reason y, runBounded limits ticks resumed = .refused reason y →
        ∃ y', runBounded limits ticks resumed' = .refused reason y') := by
  obtain ⟨resumed', again, agree⟩ := agree_resume (agree_settle state) response yielded
  have always : ∀ s t, Agree s t → (fun _ => true : State → Bool) s = true →
      (fun _ => true : State → Bool) t = true := fun _ _ _ _ => rfl
  have ran := agree_runBounded limits ticks _ _ agree
  refine ⟨resumed', again, ?_, ?_, ?_, ?_⟩
  · intro plan y r run extracted
    rw [run] at ran
    cases runT : runBounded limits ticks resumed' <;> rw [runT] at ran <;>
      simp only [OutcomeAgree, eraseOutcome, Outcome.yielded.injEq, reduceCtorEq] at ran
    obtain ⟨same, yAgree⟩ := ran
    subst same
    obtain ⟨r', extracted', resultAgree⟩ := agree_yieldedPlanWith always limits budget yAgree extracted
    exact ⟨_, r', rfl, yAgree, extracted', resultAgree⟩
  · intro value y r run completed
    rw [run] at ran
    cases runT : runBounded limits ticks resumed' <;> rw [runT] at ran <;>
      simp only [OutcomeAgree, eraseOutcome, Outcome.finished.injEq, reduceCtorEq] at ran
    obtain ⟨same, yAgree⟩ := ran
    subst same
    obtain ⟨r', completed', resultAgree⟩ := agree_completeWith always limits budget yAgree completed
    exact ⟨_, r', rfl, completed', resultAgree.1⟩
  · intro address y run
    rw [run] at ran
    cases runT : runBounded limits ticks resumed' <;> rw [runT] at ran <;>
      simp only [OutcomeAgree, eraseOutcome, Outcome.divergent.injEq, reduceCtorEq] at ran
    exact ⟨_, by rw [ran.1]⟩
  · intro reason y run
    rw [run] at ran
    cases runT : runBounded limits ticks resumed' <;> rw [runT] at ran <;>
      simp only [OutcomeAgree, eraseOutcome, Outcome.refused.injEq, reduceCtorEq] at ran
    exact ⟨_, by rw [ran.1]⟩

end Minidregg.Theory.ObjectiveBendDemandCollect
