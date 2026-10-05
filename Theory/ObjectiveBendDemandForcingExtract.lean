/- Extraction through a forcing chain (forcing transparency, part 8).

* `addrValid_of_lexical`: `LexicalInvariant` gives `AddrValid` (every held address allocated).
* `forces_fits` / `forces_forceWith` / `forces_materializeWith` / `forces_yieldedPlan` /
  `forces_complete`: along a forcing chain, with heap headroom of the chain's gap, the forced
  side runs, forces and extracts whatever the lazy side does, to the same Data, in no more
  ticks.
* `forces_segment`: the four endings of one bounded segment transfer (the shape of the
  kernel's `runSegment`).
* `HeapForces` / `yieldedPlan_heapForces`: a successful Plan extraction is a chain of finished
  closed demands (`demand_forces`), so the yielded heap forces to the extraction's heap, on
  every valid control and stack of the yielded heap. -/
import Theory.ObjectiveBendDemandForcingSegment
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendDemandData
set_option autoImplicit false

/-! ## The lexical invariant names only allocated addresses -/

section Lexical
open Minidregg.Theory.ObjectiveBendDemandInvariant

theorem valueValid_allIn {b : Nat} {v : RuntimeValue} (h : RuntimeValueValid b v) :
    AllIn (· < b) (valueAddresses v) := by
  cases v with
  | closure body env => simp only [RuntimeValueValid] at h; exact h.2
  | natural _ => exact allIn_nil _
  | boolean _ => exact allIn_nil _
  | label _ => exact allIn_nil _
  | record fields =>
    simp only [RuntimeValueValid] at h
    intro x m
    obtain ⟨fld, mem, rfl⟩ := List.mem_map.mp m
    exact h fld mem
  | specification a c =>
    simp only [RuntimeValueValid] at h
    intro x m
    simp only [valueAddresses, List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact h.1
    · exact h.2
  | prototype a c =>
    simp only [RuntimeValueValid] at h
    intro x m
    simp only [valueAddresses, List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact h.1
    · exact h.2
  | variant _ p =>
    simp only [RuntimeValueValid] at h
    intro x m
    simp only [valueAddresses, List.mem_singleton] at m
    subst m; exact h

theorem cellValid_allIn {b : Nat} {c : Cell} (h : CellValid b c) : AllIn (· < b) (cellAddresses c) := by
  cases c with
  | suspended o => simp only [CellValid, ClosureValid] at h; exact h.2
  | evaluating o => simp only [CellValid, ClosureValid] at h; exact h.2
  | cached o v =>
    simp only [CellValid, ClosureValid] at h
    exact allIn_append h.1.2 (valueValid_allIn h.2)

theorem frameValid_allIn {b : Nat} {fr : Frame} (h : FrameValid b fr) : AllIn (· < b) (frameAddresses fr) := by
  cases fr with
  | argument term env => simp only [FrameValid, ClosureValid] at h; exact h.2
  | binaryLeft _ term env => simp only [FrameValid, ClosureValid] at h; exact h.2
  | update a =>
    simp only [FrameValid] at h
    intro x m; simp only [frameAddresses, List.mem_singleton] at m; subst m; exact h
  | field _ => exact allIn_nil _
  | reflect => exact allIn_nil _
  | metadata => exact allIn_nil _
  | project => exact allIn_nil _
  | extend fields env => simp only [FrameValid] at h; exact h.1
  | condition z s env => simp only [FrameValid] at h; exact h.1
  | binaryRight _ v => simp only [FrameValid] at h; exact valueValid_allIn h
  | case arms env => simp only [FrameValid] at h; exact h.1
  | ifBool t f env => simp only [FrameValid] at h; exact h.1

theorem controlValid_allIn {b : Nat} {c : Control} (h : ControlValid b c) :
    AllIn (· < b) (controlAddresses c) := by
  cases c with
  | evaluate term env => simp only [ControlValid, ClosureValid] at h; exact h.2
  | enter a =>
    simp only [ControlValid] at h
    intro x m; simp only [controlAddresses, List.mem_singleton] at m; subst m; exact h
  | blackhole a =>
    simp only [ControlValid] at h
    intro x m; simp only [controlAddresses, List.mem_singleton] at m; subst m; exact h
  | yielded a =>
    simp only [ControlValid] at h
    intro x m; simp only [controlAddresses, List.mem_singleton] at m; subst m; exact h
  | returned v => simp only [ControlValid] at h; exact valueValid_allIn h
  | complete v => simp only [ControlValid] at h; exact valueValid_allIn h
  | refused _ => exact allIn_nil _

/-- **The lexical invariant gives address validity.** -/
theorem addrValid_of_lexical {s : State} (lexical : LexicalInvariant s) : AddrValid s :=
  ⟨fun a c found => cellValid_allIn (lexical.1 a c found), controlValid_allIn lexical.2.1,
    fun fr m => frameValid_allIn (lexical.2.2 fr m)⟩

end Lexical

/-! ## The forced side runs whatever the lazy side runs -/

/-- **Fitting transfers along a chain**, with heap headroom of the chain's gap. -/
theorem forces_fits {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) {n : Nat} (halts : Halts σ n)
    (fits : FitsFrom L σ n) :
    ∃ n' F', n' ≤ n ∧ Halts τ n' ∧ FitsFrom L' τ n' ∧ ForcesBy gap F' (exec n σ) (exec n' τ) ∧
      ∀ a, a < σ.heap.size → F' a = F a := by
  obtain ⟨n', F', le, haltsT, bounded, rel, ext⟩ := forces_transfer h n halts
  refine ⟨n', F', le, haltsT, fun j' lo hi => ?_, rel, ext⟩
  obtain ⟨j, hj, lj, sz, st⟩ := bounded j' hi
  obtain ⟨fh, fs⟩ := fits j (by omega) hj
  exact ⟨by omega, by omega⟩

/-- **Forcing transfers along a chain**: with no fewer ticks and heap headroom of the gap, the
forced side finishes too, with the renamed value, no fewer ticks left, again in a chain. -/
theorem forces_forceWith {gap : Nat} {F : Nat → Nat} {s t : State} (h : ForcesBy gap F s t) {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) {T T' : Nat} (le : T ≤ T')
    {v : RuntimeValue} {st : State} {r : Nat} (ran : forceWith (fun _ => true) L T s = (.finished v st, r)) :
    ∃ (F' : Nat → Nat) (st' : State) (r' : Nat),
      forceWith (fun _ => true) L' T' t = (.finished (renameValue F' v) st', r') ∧ r ≤ r' ∧
        ForcesBy gap F' st st' ∧ AllIn (· < st.heap.size) (valueAddresses v) ∧
        (∀ a, a < s.heap.size → F' a = F a) ∧ s.heap.size ≤ st.heap.size := by
  obtain ⟨n, le1, halts, fits, eq, ctl, rEq⟩ := forceWith_finished L T s v st r ran
  obtain ⟨n', F', le2, haltsT, fitsT, rel, ext⟩ := forces_fits h heapRoom stackRoom halts fits
  have ctlT : (exec n' t).control = .complete (renameValue F' v) := by
    rw [rel.renames.1, eq, ctl]; rfl
  refine ⟨F', exec n' t, T' - n', forceWith_of_halts L' T' t n' _ haltsT (by omega) fitsT ctlT, by omega,
    by rw [← eq]; exact rel, ?_, ext, by rw [← eq]; exact exec_size_mono s n⟩
  have := (ForcesBy.lazyValid rel).control
  rw [eq, ctl] at this
  exact this

/-- Two budgets differ only in ticks, the second no smaller. -/
def TicksLe (b b' : Budget) : Prop := b'.nodes = b.nodes ∧ b'.bytes = b.bytes ∧ b.ticks ≤ b'.ticks

/-- One field of a record's materialization (the body of `materializeWith`'s fold). -/
def recordStep (policy : State → Bool) (limits : Limits) (depth : Nat)
    (prior : List (String × Data) × State × Budget) (field : String × Nat) :
    Except (Failure × State) (List (String × Data) × State × Budget) := do
  let bytes := field.1.utf8ByteSize+(toString field.1.utf8ByteSize).utf8ByteSize+1
  if bytes > prior.2.2.bytes || prior.2.2.nodes = 0 then throw (.budget,prior.2.1)
  let entered : State := {prior.2.1 with control:=.enter field.2,stack:=[]}
  let (outcome,ticks) := forceWith policy limits prior.2.2.ticks entered
  let nextBudget := {prior.2.2 with ticks:=ticks,bytes:=prior.2.2.bytes-bytes}
  match outcome with
  | .finished forced retained =>
    let child ← materializeWith policy limits depth nextBudget forced retained
    pure ((field.1,child.value)::prior.1,child.state,child.remaining)
  | .suspended _ retained => throw (.suspended,retained)
  | .divergent _ retained => throw (.divergent,retained)
  | .refused _ retained => throw (.refused,retained)
  | .yielded _ retained => throw (.yielded,retained)

theorem materializeWith_record (policy : State → Bool) (limits : Limits) (depth : Nat) (budget : Budget)
    (fields : List (String × Nat)) (state : State) :
    materializeWith policy limits (depth+1) budget (.record fields) state = (do
      if budget.nodes = 0 then throw (.budget,state)
      let remaining := {budget with nodes:=budget.nodes-1}
      let headerBytes := (toString fields.length).utf8ByteSize+2
      if headerBytes > remaining.bytes then throw (.budget,state)
      let remaining := {remaining with bytes:=remaining.bytes-headerBytes}
      if (fields.map Prod.fst).eraseDups.length != fields.length then throw (.duplicateField,state)
      if fields.length > remaining.nodes then throw (.budget,state)
      let pair ← fields.foldlM (recordStep policy limits depth) ([],state,remaining)
      pure ⟨.record pair.1.reverse,pair.2.1,pair.2.2⟩) := rfl

theorem ticksLe_with (b : Budget) {t : Nat} (le : b.ticks ≤ t) : TicksLe b {b with ticks := t} := ⟨rfl, rfl, le⟩

/-- The record fold, along a chain: each field forced on the lazy side is forced on the forced
side at its image under the map the record was renamed by (later maps extend it). -/
theorem foldlM_forces {gap : Nat} {base : Nat} {F0 : Nat → Nat}
    {L L' : Limits} {step : Limits → List (String × Data) × State × Budget → String × Nat →
      Except (Failure × State) (List (String × Data) × State × Budget)}
    (stepRel : ∀ (acc : List (String × Data)) (st st' : State) (b b' : Budget) (field : String × Nat)
        (out : List (String × Data) × State × Budget) (F : Nat → Nat),
      ForcesBy gap F st st' → field.2 < st.heap.size → TicksLe b b' → step L (acc, st, b) field = .ok out →
      ∃ (out' : List (String × Data) × State × Budget) (F' : Nat → Nat),
        step L' (acc, st', b') (field.1, F field.2) = .ok out' ∧ out'.1 = out.1 ∧ TicksLe out.2.2 out'.2.2 ∧
        ForcesBy gap F' out.2.1 out'.2.1 ∧ (∀ a, a < st.heap.size → F' a = F a) ∧
        st.heap.size ≤ out.2.1.heap.size) :
    ∀ (fields : List (String × Nat)) (acc : List (String × Data)) (st st' : State) (b b' : Budget)
      (F : Nat → Nat) (out : List (String × Data) × State × Budget),
      ForcesBy gap F st st' → base ≤ st.heap.size → (∀ a, a < base → F a = F0 a) →
      AllIn (· < base) (fields.map Prod.snd) → TicksLe b b' → fields.foldlM (step L) (acc, st, b) = .ok out →
      ∃ (out' : List (String × Data) × State × Budget) (F' : Nat → Nat),
        (fields.map fun field => (field.1, F0 field.2)).foldlM (step L') (acc, st', b') = .ok out' ∧
        out'.1 = out.1 ∧ TicksLe out.2.2 out'.2.2 ∧ ForcesBy gap F' out.2.1 out'.2.1 ∧
        (∀ a, a < st.heap.size → F' a = F a) ∧ st.heap.size ≤ out.2.1.heap.size := by
  intro fields
  induction fields with
  | nil =>
    intro acc st st' b b' F out rel _ _ _ le folded
    simp [List.foldlM] at folded
    subst folded
    exact ⟨_, F, rfl, rfl, le, rel, fun _ _ => rfl, Nat.le_refl _⟩
  | cons field rest ih =>
    intro acc st st' b b' F out rel baseLe agree inside le folded
    simp only [List.foldlM_cons, except_bind_ok] at folded
    obtain ⟨mid, first, restFolded⟩ := folded
    have fieldIn : field.2 < base := inside field.2 (by simp)
    obtain ⟨mid', F1, first', same1, le1, rel1, ext1, grow1⟩ :=
      stepRel acc st st' b b' field mid F rel (by omega) le first
    rw [agree _ fieldIn] at first'
    obtain ⟨out', F2, folded', outSame, outLe, outRel, ext2, grow2⟩ :=
      ih mid.1 mid.2.1 mid'.2.1 mid.2.2 mid'.2.2 F1 out rel1 (by omega)
        (fun a lt => by rw [ext1 a (by omega), agree a lt])
        (fun x member => inside x (by simp [member])) le1 restFolded
    refine ⟨out', F2, ?_, outSame, outLe, outRel, fun a lt => by rw [ext2 a (by omega), ext1 a lt], by omega⟩
    simp only [List.map_cons, List.foldlM_cons, except_bind_ok]
    refine ⟨mid', first', ?_⟩
    have shape : mid' = (mid.1, mid'.2.1, mid'.2.2) := by
      obtain ⟨a, b, c⟩ := mid'
      simp only at same1
      rw [same1]
    rw [shape]; exact folded'

/-- **Materialization transfers along a chain**: the renamed value materializes on the forced
side to the same Data, with the same nodes and bytes left and no fewer ticks. -/
theorem forces_materializeWith {L L' : Limits} {gap : Nat} (heapRoom : L.heap + gap ≤ L'.heap)
    (stackRoom : L.stack ≤ L'.stack) :
    ∀ (depth : Nat) (budget budget' : Budget) (value : RuntimeValue) (s t : State) (F : Nat → Nat) (r : Result),
      ForcesBy gap F s t → AllIn (· < s.heap.size) (valueAddresses value) → TicksLe budget budget' →
      materializeWith (fun _ => true) L depth budget value s = .ok r →
      ∃ (r' : Result) (F' : Nat → Nat),
        materializeWith (fun _ => true) L' depth budget' (renameValue F value) t = .ok r' ∧
        r'.value = r.value ∧ TicksLe r.remaining r'.remaining ∧ ForcesBy gap F' r.state r'.state ∧
        s.heap.size ≤ r.state.heap.size ∧ ∀ a, a < s.heap.size → F' a = F a := by
  intro depth
  induction depth with
  | zero => intro budget budget' value s t F r _ _ _ found; simp [materializeWith] at found
  | succ depth ih =>
    intro budget budget' value s t F r rel valueIn le found
    obtain ⟨nodes, ticks, bytes⟩ := budget
    obtain ⟨nodes', ticks', bytes'⟩ := budget'
    obtain ⟨hn, hb, ht⟩ := le
    simp only at hn hb ht
    subst nodes' bytes'
    cases value with
    | natural n =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨⟨.natural n, t, ⟨nodes - 1, ticks', bytes - ((toString n).utf8ByteSize + 2)⟩⟩, F, ?_, ?_, ?_, ?_, ?_⟩
          · simp [materializeWith, renameValue, c1, c2]
          · rw [← found]
          · rw [← found]; exact ⟨rfl, rfl, ht⟩
          · rw [← found]; exact rel
          · rw [← found]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    | boolean b =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨⟨.boolean b, t, ⟨nodes - 1, ticks', bytes - 2⟩⟩, F, ?_, ?_, ?_, ?_, ?_⟩
          · simp [materializeWith, renameValue, c1, c2]
          · rw [← found]
          · rw [← found]; exact ⟨rfl, rfl, ht⟩
          · rw [← found]; exact rel
          · rw [← found]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    | label l =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨⟨.label l, t, ⟨nodes - 1, ticks', bytes - (l.utf8ByteSize + (toString l.utf8ByteSize).utf8ByteSize + 2)⟩⟩,
            F, ?_, ?_, ?_, ?_, ?_⟩
          · simp [materializeWith, renameValue, c1, c2]
          · rw [← found]
          · rw [← found]; exact ⟨rfl, rfl, ht⟩
          · rw [← found]; exact rel
          · rw [← found]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    | closure body environment => simp [materializeWith] at found; split at found <;> simp at found
    | specification metadata extension => simp [materializeWith] at found; split at found <;> simp at found
    | prototype spec target => simp [materializeWith] at found; split at found <;> simp at found
    | variant label payload =>
      have payloadIn : payload < s.heap.size := valueIn payload (by simp [valueAddresses])
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          have entered : ForcesBy gap F ⟨s.heap, .enter payload, []⟩ ⟨t.heap, .enter (F payload), []⟩ :=
            rel.reenter (.enter payload) [] (by simp [controlAddresses, payloadIn]) (fun _ m => by cases m)
          cases forced : forceWith (fun _ => true) L ticks ⟨s.heap, .enter payload, []⟩ with
          | mk outcome rest =>
            rw [forced] at found
            cases outcome with
            | finished value retained =>
              obtain ⟨F1, st', r1, forcedT, restLe, rel1, valueIn1, ext1, grow1⟩ :=
                forces_forceWith entered heapRoom stackRoom ht forced
              simp at found
              obtain ⟨a, materialized, rfl⟩ := found
              obtain ⟨a', F2, materialized', aValue, aLe, aRel, aGrow, ext2⟩ :=
                ih _ _ value retained st' F1 a rel1 valueIn1 (ticksLe_with _ (by exact restLe)) materialized
              simp only at grow1
              refine ⟨⟨.variant label a'.value, a'.state, a'.remaining⟩, F2, ?_, by simp [aValue], aLe, aRel,
                by simp only; omega, fun x lt => by rw [ext2 x (by omega), ext1 x lt]⟩
              rw [show renameValue F (.variant label payload) = .variant label (F payload) from rfl]
              simp [materializeWith, c1, c2, forcedT, materialized']
            | _ => simp at found
    | record fields =>
      have fieldsIn : AllIn (· < s.heap.size) (fields.map Prod.snd) := valueIn
      simp [materializeWith_record] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · split at found
            · simp at found
            · rename_i c1 c2 c3 c4
              obtain ⟨out, folded, rfl⟩ := (except_map_ok _ _ _).mp found
              have key := foldlM_forces (gap := gap) (base := s.heap.size) (F0 := F) (L := L) (L' := L')
                (step := fun L => recordStep (fun _ => true) L depth) ?_ fields []
                s t _ _ F out rel (Nat.le_refl _) (fun _ _ => rfl) fieldsIn (ticksLe_with _ (by exact ht)) folded
              · obtain ⟨out', F', folded', same1, outLe, outRel, ext', grow'⟩ := key
                refine ⟨⟨.record out'.1.reverse, out'.2.1, out'.2.2⟩, F', ?_, by simp [same1], outLe, outRel, grow',
                  ext'⟩
                simp [materializeWith_record, renameValue, c1, c2, c3, c4, folded', Function.comp_def]
              · intro acc st st' b b' field out F stRel inField stLe stepped
                obtain ⟨bn, bt, bb⟩ := b
                obtain ⟨bn', bt', bb'⟩ := b'
                obtain ⟨hn, hb, ht2⟩ := stLe
                simp only at hn hb ht2
                subst bn' bb'
                simp [recordStep] at stepped
                split at stepped
                · simp at stepped
                · rename_i cond
                  have entered : ForcesBy gap F ⟨st.heap, .enter field.2, []⟩ ⟨st'.heap, .enter (F field.2), []⟩ :=
                    stRel.reenter (.enter field.2) [] (by simp [controlAddresses, inField]) (fun _ m => by cases m)
                  cases forced : forceWith (fun _ => true) L bt ⟨st.heap, .enter field.2, []⟩ with
                  | mk outcome rest =>
                    rw [forced] at stepped
                    cases outcome with
                    | finished value retained =>
                      obtain ⟨F1, st'', r1, forcedT, restLe, rel1, valueIn1, ext1, grow1⟩ :=
                        forces_forceWith entered heapRoom stackRoom ht2 forced
                      simp at stepped
                      obtain ⟨a, materialized, rfl⟩ := stepped
                      obtain ⟨a', F2, materialized', aValue, aLe, aRel, aGrow, ext2⟩ :=
                        ih _ _ value retained st'' F1 a rel1 valueIn1 (ticksLe_with _ (by exact restLe)) materialized
                      simp only at grow1
                      refine ⟨((field.1, a'.value) :: acc, a'.state, a'.remaining), F2, ?_, by simp [aValue], aLe, aRel,
                        fun x lt => by rw [ext2 x (by omega), ext1 x lt], by simp only; omega⟩
                      simp [recordStep, cond, forcedT, materialized']
                    | _ => simp at stepped
          · simp at found

/-- **Plan extraction transfers along a chain.** -/
theorem forces_yieldedPlan {gap : Nat} {F : Nat → Nat} {y y' : State} (h : ForcesBy gap F y y') {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) {budget : Budget} {r : Result}
    (found : yieldedPlan L budget y = .ok r) :
    ∃ r', yieldedPlan L' budget y' = .ok r' ∧ r'.value = r.value := by
  have valid := h.lazyValid
  obtain ⟨ctlEq, _⟩ := h.renames
  unfold yieldedPlan yieldedPlanWith at found ⊢
  cases hc : y.control with
  | yielded plan =>
    rw [hc] at found
    have planIn : plan < y.heap.size := by
      have := valid.control; rw [hc] at this; exact this plan (by simp [controlAddresses])
    have ctlT : y'.control = .yielded (F plan) := by rw [ctlEq, hc]; rfl
    rw [ctlT]
    simp only at found ⊢
    have entered : ForcesBy gap F ⟨y.heap, .enter plan, []⟩ ⟨y'.heap, .enter (F plan), []⟩ :=
      h.reenter (.enter plan) [] (by simp [controlAddresses, planIn]) (fun _ m => by cases m)
    cases forced : forceWith (fun _ => true) L budget.ticks ⟨y.heap, .enter plan, []⟩ with
    | mk outcome rest =>
      rw [forced] at found
      cases outcome with
      | finished value retained =>
        obtain ⟨F1, st', r1, forcedT, restLe, rel1, valueIn1, _, _⟩ :=
          forces_forceWith entered heapRoom stackRoom (Nat.le_refl _) forced
        simp at found
        obtain ⟨a, materialized, rfl⟩ := found
        obtain ⟨a', F2, materialized', aValue, _, _, _, _⟩ :=
          forces_materializeWith heapRoom stackRoom _ _ _ value retained st' F1 a rel1 valueIn1
            (ticksLe_with _ (by exact restLe)) materialized
        refine ⟨{a' with state := {a'.state with control := .yielded (F plan), stack := y'.stack}}, ?_, aValue⟩
        simp [forcedT, materialized']
      | _ => simp at found
  | _ => rw [hc] at found; simp at found

/-- **Completion transfers along a chain.** -/
theorem forces_complete {gap : Nat} {F : Nat → Nat} {y y' : State} (h : ForcesBy gap F y y') {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) {budget : Budget} {r : Result}
    (found : complete L budget y = .ok r) :
    ∃ r', complete L' budget y' = .ok r' ∧ r'.value = r.value := by
  have valid := h.lazyValid
  obtain ⟨ctlEq, stEq⟩ := h.renames
  unfold complete completeWith at found ⊢
  cases hc : y.control with
  | complete v =>
    cases hs : y.stack with
    | nil =>
      have ctlT : y'.control = .complete (renameValue F v) := by rw [ctlEq, hc]; rfl
      have stT : y'.stack = [] := by rw [stEq, hs]; rfl
      have vIn : AllIn (· < y.heap.size) (valueAddresses v) := by
        have := valid.control; rw [hc] at this; exact this
      rw [hc, hs] at found
      rw [ctlT, stT]
      simp at found ⊢
      obtain ⟨a, materialized, rest⟩ := found
      obtain ⟨a', F2, materialized', aValue, _, _, _, _⟩ :=
        forces_materializeWith heapRoom stackRoom _ _ _ v y y' F a h vIn ⟨rfl, rfl, Nat.le_refl _⟩ materialized
      split at rest
      · rename_i bytes encodedAt
        split at rest
        · simp at rest
        · rename_i small
          simp at rest; subst rest
          refine ⟨a', ⟨a', materialized', ?_⟩, aValue⟩
          simp [aValue, encodedAt, small]
      · simp at rest
    | cons fr rest => rw [hc, hs] at found; simp at found
  | _ => rw [hc] at found; simp at found

/-- **A bounded run that does not suspend transfers along a chain**: both runs are their halting
raw runs, whose ends are again in a chain. -/
theorem forces_runBounded {gap : Nat} {F : Nat → Nat} {s t : State} (h : ForcesBy gap F s t) {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) (ticks : Nat)
    (notSusp : ∀ r st, runBounded L ticks s ≠ .suspended r st) :
    ∃ (n n' : Nat) (F' : Nat → Nat), runBounded L ticks s = runBounded L 0 (exec n s) ∧
      runBounded L' ticks t = runBounded L' 0 (exec n' t) ∧ ForcesBy gap F' (exec n s) (exec n' t) := by
  obtain ⟨n, le, halts, fits, eq⟩ := runBounded_halts L ticks s notSusp
  obtain ⟨n', F', le', haltsT, fitsT, rel, _⟩ := forces_fits h heapRoom stackRoom halts fits
  exact ⟨n, n', F', eq, runBounded_of_halts L' ticks t n' haltsT (by omega) fitsT, rel⟩

/-- The terminal outcomes of a chain's two ends correspond. -/
theorem runBounded_zero_forces {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) (L L' : Limits) :
    (∀ v y, runBounded L 0 σ = .finished v y → y = σ ∧ runBounded L' 0 τ = .finished (renameValue F v) τ) ∧
    (∀ p y, runBounded L 0 σ = .yielded p y → y = σ ∧ runBounded L' 0 τ = .yielded (F p) τ) ∧
    (∀ a y, runBounded L 0 σ = .divergent a y → runBounded L' 0 τ = .divergent (F a) τ) ∧
    (∀ reason y, runBounded L 0 σ = .refused reason y → runBounded L' 0 τ = .refused reason τ) := by
  have ctl := h.renames.1
  refine ⟨fun v y ran => ?_, fun p y ran => ?_, fun a y ran => ?_, fun reason y ran => ?_⟩ <;>
    cases hc : σ.control <;> simp only [runBounded, hc] at ran <;> cases ran <;>
    simp [runBounded, ctl, hc, renameControl]

/-- **One segment's four endings transfer along a chain**, with heap headroom of its gap: a
yield whose Plan extracts, a completion that extracts, a divergence, a refusal. -/
theorem forces_segment {gap : Nat} {F : Nat → Nat} {s t : State} (h : ForcesBy gap F s t) {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) (ticks : Nat) (budget : Budget) :
    (∀ plan y r, runBounded L ticks s = .yielded plan y → yieldedPlan L budget y = .ok r →
      ∃ plan' y' r', runBounded L' ticks t = .yielded plan' y' ∧ yieldedPlan L' budget y' = .ok r' ∧
        r'.value = r.value) ∧
    (∀ value y r, runBounded L ticks s = .finished value y → complete L budget y = .ok r →
      ∃ value' y' r', runBounded L' ticks t = .finished value' y' ∧ complete L' budget y' = .ok r' ∧
        r'.value = r.value) ∧
    (∀ address y, runBounded L ticks s = .divergent address y →
      ∃ address' y', runBounded L' ticks t = .divergent address' y') ∧
    (∀ reason y, runBounded L ticks s = .refused reason y → ∃ y', runBounded L' ticks t = .refused reason y') := by
  refine ⟨fun plan y r ran extracted => ?_, fun value y r ran completed => ?_, fun address y ran => ?_,
    fun reason y ran => ?_⟩
  · obtain ⟨n, n', F', eq, eqT, rel⟩ := forces_runBounded h heapRoom stackRoom ticks
      (fun _ _ h' => by rw [ran] at h'; cases h')
    rw [eq] at ran
    obtain ⟨same, ranT⟩ := (runBounded_zero_forces rel L L').2.1 plan y ran
    subst same
    obtain ⟨r', extracted', value⟩ := forces_yieldedPlan rel heapRoom stackRoom extracted
    exact ⟨_, _, r', by rw [eqT, ranT], extracted', value⟩
  · obtain ⟨n, n', F', eq, eqT, rel⟩ := forces_runBounded h heapRoom stackRoom ticks
      (fun _ _ h' => by rw [ran] at h'; cases h')
    rw [eq] at ran
    obtain ⟨same, ranT⟩ := (runBounded_zero_forces rel L L').1 value y ran
    subst same
    obtain ⟨r', completed', value⟩ := forces_complete rel heapRoom stackRoom completed
    exact ⟨_, _, r', by rw [eqT, ranT], completed', value⟩
  · obtain ⟨n, n', F', eq, eqT, rel⟩ := forces_runBounded h heapRoom stackRoom ticks
      (fun _ _ h' => by rw [ran] at h'; cases h')
    rw [eq] at ran
    exact ⟨_, _, by rw [eqT, (runBounded_zero_forces rel L L').2.2.1 address y ran]⟩
  · obtain ⟨n, n', F', eq, eqT, rel⟩ := forces_runBounded h heapRoom stackRoom ticks
      (fun _ _ h' => by rw [ran] at h'; cases h')
    rw [eq] at ran
    exact ⟨_, by rw [eqT, (runBounded_zero_forces rel L L').2.2.2 reason y ran]⟩

/-! ## A successful extraction is a forcing chain -/

/-- **`H` forces to `H'`**: both valid, `H'` extends `H`, and on every valid control and stack of
`H`, `H` forces to `H'` (headroom: the cells `H'` added) by a map that is the identity on `H`. -/
def HeapForces (H H' : Array Cell) : Prop :=
  HeapValid H ∧ HeapValid H' ∧ H.size ≤ H'.size ∧ ∃ F : Nat → Nat, (∀ a, a < H.size → F a = a) ∧
    ∀ (c : Control) (S : List Frame), AllIn (· < H.size) (controlAddresses c) →
      (∀ fr ∈ S, AllIn (· < H.size) (frameAddresses fr)) →
      ForcesBy (H'.size - H.size) F ⟨H, c, S⟩ ⟨H', c, S⟩

theorem heapForces_refl {H : Array Cell} (valid : HeapValid H) : HeapForces H H :=
  ⟨valid, valid, Nat.le_refl _, id, fun _ _ => rfl, fun _ _ cIn sIn =>
    .agree (agreeRel_refl ⟨valid, cIn, sIn⟩) (by simp)⟩

theorem heapForces_trans {H1 H2 H3 : Array Cell} (one : HeapForces H1 H2) (two : HeapForces H2 H3) :
    HeapForces H1 H3 := by
  obtain ⟨v1, _, le1, F1, id1, ch1⟩ := one
  obtain ⟨_, v3, le2, F2, id2, ch2⟩ := two
  refine ⟨v1, v3, by omega, F2 ∘ F1, fun a lt => by simp [Function.comp_apply, id1 a lt, id2 a (by omega)],
    fun c S cIn sIn => ?_⟩
  exact .trans (ch1 c S cIn sIn) (ch2 c S (allBelow_mono cIn le1) (frames_mono sIn le1)) (by omega)

/-- **A finished closed demand makes its base force to its final heap** (`demand_forces`). -/
theorem heapForces_demand {H : Array Cell} {a n : Nat} {H' : Array Cell} {v : RuntimeValue} (valid : HeapValid H)
    (d : Demand H a n H' v) : HeapForces H H' := by
  obtain ⟨F, Fid, chain⟩ := demand_forces n H a H' v valid d
  have aLt := (demand_cell_lt d).1
  have grow : H.size ≤ H'.size := by
    have := exec_size_mono (demandStart H a) n; rw [d.final] at this; exact this
  have valid' : HeapValid H' := by
    have := heapValid_exec (addrValid_demandStart valid aLt) n; rw [d.final] at this; exact this
  exact ⟨valid, valid', grow, F, Fid, chain⟩

/-- A transition that completes leaves an empty stack. -/
theorem stepRaw_complete_stack {s : State} {v : RuntimeValue} (act : active s.control = true)
    (h : (stepRaw s).control = .complete v) : (stepRaw s).stack = [] := by
  obtain ⟨heap, control, stack⟩ := s
  cases control with
  | returned w =>
    cases stack with
    | nil => rfl
    | cons fr rest =>
      cases fr <;> simp only [stepRaw] at h ⊢ <;> (repeat' split at h) <;> simp_all
  | evaluate term env =>
    cases term <;> simp only [stepRaw] at h <;> (repeat' split at h) <;> simp_all
  | enter a => simp only [stepRaw] at h; split at h <;> simp_all
  | _ => simp [active] at act

/-- **Forcing a cell with the open policy is its closed demand.** -/
theorem forceWith_demand {L : Limits} {T : Nat} {H : Array Cell} {a : Nat} {v : RuntimeValue} {st : State} {r : Nat}
    (ran : forceWith (fun _ => true) L T ⟨H, .enter a, []⟩ = (.finished v st, r)) :
    ∃ n, Demand H a n st.heap v := by
  obtain ⟨n, _, halts, _, eq, ctl, _⟩ := forceWith_finished L T _ v st r ran
  have pos : n ≠ 0 := by
    intro h0; subst h0; have := halts.2; simp [exec, active] at this
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have act : active (exec m ⟨H, .enter a, []⟩).control = true := halts.1 m (by omega)
  have stack : st.stack = [] := by
    rw [← eq, exec_succ]; exact stepRaw_complete_stack act (by rw [← exec_succ, eq, ctl])
  refine ⟨m + 1, halts, ?_⟩
  show exec (m + 1) ⟨H, .enter a, []⟩ = _
  rw [eq, state_ext (s := st), ctl, stack]

theorem foldlM_invariant {α β ε : Type} {step : β → α → Except ε β} (P : β → Prop)
    (stepP : ∀ x a y, P x → step x a = .ok y → P y) :
    ∀ (l : List α) (x y : β), P x → l.foldlM step x = .ok y → P y := by
  intro l
  induction l with
  | nil => intro x y px folded; simp [List.foldlM] at folded; subst folded; exact px
  | cons a rest ih =>
    intro x y px folded
    simp only [List.foldlM_cons, except_bind_ok] at folded
    obtain ⟨mid, first, restFolded⟩ := folded
    exact ih mid y (stepP x a mid px first) restFolded

/-- **A successful materialization is a forcing chain.** -/
theorem materializeWith_heapForces (L : Limits) :
    ∀ (depth : Nat) (budget : Budget) (value : RuntimeValue) (s : State) (r : Result), HeapValid s.heap →
      materializeWith (fun _ => true) L depth budget value s = .ok r → HeapForces s.heap r.state.heap := by
  intro depth
  induction depth with
  | zero => intro budget value s r _ found; simp [materializeWith] at found
  | succ depth ih =>
    intro budget value s r valid found
    cases value with
    | natural n =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · simp at found; rw [← found]; exact heapForces_refl valid
    | boolean b =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · simp at found; rw [← found]; exact heapForces_refl valid
    | label l =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · simp at found; rw [← found]; exact heapForces_refl valid
    | closure body environment => simp [materializeWith] at found; split at found <;> simp at found
    | specification metadata extension => simp [materializeWith] at found; split at found <;> simp at found
    | prototype spec target => simp [materializeWith] at found; split at found <;> simp at found
    | variant label payload =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · cases forced : forceWith (fun _ => true) L budget.ticks ⟨s.heap, .enter payload, []⟩ with
          | mk outcome rest =>
            rw [forced] at found
            cases outcome with
            | finished value retained =>
              obtain ⟨n, d⟩ := forceWith_demand forced
              have one := heapForces_demand valid d
              simp at found
              obtain ⟨a, materialized, rfl⟩ := found
              exact heapForces_trans one (ih _ _ _ a one.2.1 materialized)
            | _ => simp at found
    | record fields =>
      simp [materializeWith_record] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · split at found
            · simp at found
            · obtain ⟨out, folded, rfl⟩ := (except_map_ok _ _ _).mp found
              refine foldlM_invariant (fun x => HeapForces s.heap x.2.1.heap) ?_ fields _ out
                (heapForces_refl valid) folded
              intro x field y px stepped
              simp [recordStep] at stepped
              split at stepped
              · simp at stepped
              · cases forced : forceWith (fun _ => true) L x.2.2.ticks ⟨x.2.1.heap, .enter field.2, []⟩ with
                | mk outcome rest =>
                  rw [forced] at stepped
                  cases outcome with
                  | finished value retained =>
                    obtain ⟨n, d⟩ := forceWith_demand forced
                    have one := heapForces_demand px.2.1 d
                    simp at stepped
                    obtain ⟨a, materialized, rfl⟩ := stepped
                    exact heapForces_trans px (heapForces_trans one (ih _ _ _ a one.2.1 materialized))
                  | _ => simp at stepped
          · simp at found

/-- **A successful Plan extraction is a forcing chain**: the yielded heap forces to the
extraction's heap. -/
theorem yieldedPlan_heapForces {L : Limits} {budget : Budget} {y : State} {r : Result} (valid : HeapValid y.heap)
    (found : yieldedPlan L budget y = .ok r) : HeapForces y.heap r.state.heap := by
  unfold yieldedPlan yieldedPlanWith at found
  cases hc : y.control with
  | yielded plan =>
    rw [hc] at found
    simp only at found
    cases forced : forceWith (fun _ => true) L budget.ticks ⟨y.heap, .enter plan, []⟩ with
    | mk outcome rest =>
      rw [forced] at found
      cases outcome with
      | finished value retained =>
        obtain ⟨n, d⟩ := forceWith_demand forced
        have one := heapForces_demand valid d
        simp at found
        obtain ⟨a, materialized, rfl⟩ := found
        exact heapForces_trans one (materializeWith_heapForces L _ _ _ _ a one.2.1 materialized)
      | _ => simp at found
  | _ => rw [hc] at found; simp at found

/-- **The resumed yield forces to the resumed extraction**: resuming a valid yield and resuming
the state its Plan extraction left (the same control and stack over the larger heap) are related
by a forcing chain whose headroom is the cells the extraction added. -/
theorem yieldedPlan_forces {L : Limits} {budget : Budget} {y : State} {r : Result} (valid : AddrValid y)
    (found : yieldedPlan L budget y = .ok r) (c : Control) (cIn : AllIn (· < y.heap.size) (controlAddresses c)) :
    ∃ F, ForcesBy (r.state.heap.size - y.heap.size) F ⟨y.heap, c, y.stack⟩ ⟨r.state.heap, c, y.stack⟩ := by
  obtain ⟨_, _, _, F, _, chain⟩ := yieldedPlan_heapForces valid.heap found
  exact ⟨F, chain c y.stack cIn valid.stack⟩

#assert_axioms valueValid_allIn cellValid_allIn frameValid_allIn controlValid_allIn addrValid_of_lexical
#assert_axioms forces_fits forces_forceWith ticksLe_with materializeWith_record foldlM_forces
#assert_axioms forces_materializeWith forces_yieldedPlan forces_complete
#assert_axioms forces_runBounded runBounded_zero_forces forces_segment
#assert_axioms heapForces_refl heapForces_trans heapForces_demand stepRaw_complete_stack forceWith_demand
#assert_axioms foldlM_invariant materializeWith_heapForces yieldedPlan_heapForces yieldedPlan_forces

end Minidregg.Theory.ObjectiveBendDemandForcing
