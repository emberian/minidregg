/- Every finished closed demand is a forcing chain (forcing transparency, part 6).

* `pending_within`: inside every finished nested evaluation sits a PRE-SHALLOW demand:
  following the first suspended cell of the base heap each nested evaluation enters, one
  reaches an evaluation that enters none (besides its own cell). Its closed demand on the
  base heap finishes and reads, of the base, only its cell and cached cells.
* `pendRel_start`: a pre-shallow demand pends between the base heap and its final heap.
* `demand_forces` (the main induction, on the demand's length): a finished closed demand of
  `y` on `B` makes `B` force to the final heap: pend the first pre-shallow demand inside it,
  run the rest of the demand against it (`pend_transfer`: strictly shorter, ending in exact
  agreement), apply the induction to that shorter demand, and close with the inverse of the
  agreement. -/
import Theory.ObjectiveBendDemandForcingChain
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
set_option autoImplicit false

/-- A stripped nested run, seen from the base heap `B`: the cells of `B` other than `w`
keep their state in `P`, and every update frame is for `w` or for a cell past `B`. -/
def StripInv (B P : Array Cell) (w : Nat) (s : State) : Prop :=
  (∀ a, a < B.size → a ≠ w → s.heap[a]? = P[a]?) ∧
    (∀ fr ∈ s.stack, ∀ b, fr = .update b → b = w ∨ B.size ≤ b) ∧ B.size ≤ s.heap.size

/-- The transition enters no suspended cell of `B` but `w`. -/
def NoPreEntry (B : Array Cell) (w : Nat) (s : State) : Prop :=
  ∀ b o, s.control = .enter b → s.heap[b]? = some (.suspended o) → b < B.size → b = w

theorem stripInv_step {B P : Array Cell} {w : Nat} {s : State} (inv : StripInv B P w s)
    (noPre : NoPreEntry B w s) : StripInv B P w (stepRaw s) := by
  obtain ⟨heapI, stackI, sizeI⟩ := inv
  refine ⟨?_, ?_, Nat.le_trans sizeI (stepRaw_size_mono s)⟩
  · intro a lt ne
    by_cases reads : readsAt s = some a
    · cases ctl : s.control with
      | enter b =>
        have bEq : b = a := by simp [readsAt, ctl] at reads; exact reads
        subst bEq
        rcases stepRaw_enter_cases ctl with ⟨o, su⟩ | ⟨same, _⟩
        · exact absurd (noPre b o ctl su lt) ne
        · rw [same]; exact heapI b lt ne
      | returned v =>
        obtain ⟨rest, top⟩ : ∃ rest, s.stack = .update a :: rest := by
          cases st : s.stack with
          | nil => simp [readsAt, ctl, st] at reads
          | cons fr rest =>
            cases fr <;> simp [readsAt, ctl, st] at reads
            exact ⟨rest, by rw [reads]⟩
        rcases stackI _ (by rw [top]; exact List.mem_cons_self ..) a rfl with h | h
        · exact absurd h ne
        · omega
      | _ => simp [readsAt, ctl] at reads
    · rw [stepRaw_heap_keep s (by omega) reads]; exact heapI a lt ne
  · intro fr mem b isB
    subst isB
    rcases stepRaw_stack_shape s with same | ⟨fr', push⟩ | ⟨fr0, rest, eq, notUpd, fr', next⟩ | ⟨fr0, rest, eq, next⟩
    · rw [same] at mem; exact stackI _ mem b rfl
    · rw [push] at mem
      rcases List.mem_cons.mp mem with rfl | mem
      · have ctl := stepRaw_push_update s push rfl
        rcases stepRaw_enter_cases ctl with ⟨o, su⟩ | ⟨_, same⟩
        · by_cases lt : b < B.size
          · exact Or.inl (noPre b o ctl su lt)
          · exact Or.inr (Nat.le_of_not_lt lt)
        · rw [same] at push; have := congrArg List.length push; simp at this
      · exact stackI _ mem b rfl
    · rw [next] at mem
      rcases List.mem_cons.mp mem with rfl | mem
      · have := stepRaw_top_update s eq (by rw [next])
        exact stackI _ (by rw [eq]; exact List.mem_cons_self ..) b this
      · exact stackI _ (by rw [eq]; exact List.mem_cons_of_mem _ mem) b rfl
    · rw [next] at mem; exact stackI _ (by rw [eq]; exact List.mem_cons_of_mem _ mem) b rfl

theorem stripInv_run {B P : Array Cell} {w : Nat} {s : State} (inv : StripInv B P w s) :
    ∀ j, (∀ i, i < j → NoPreEntry B w (exec i s)) → StripInv B P w (exec j s) := by
  intro j
  induction j with
  | zero => intro _; exact inv
  | succ j ih =>
    intro noPre
    rw [exec_succ]
    exact stripInv_step (ih (fun i lt => noPre i (by omega))) (noPre j (by omega))

/-- The map from a heap `P` that extends `B` back to `B`: the identity on `B`, the shift past
`P`'s end; the cells of `P` past `B` (allocated before the nested demand) are left out. -/
def backMap (B P : Nat) : Nat → Nat := fun a => if a < B then a else a - P + B

/-- **Inside every finished nested evaluation sits a pre-shallow demand.** Following the
first suspended cell of the base heap `B` each nested evaluation enters, one reaches an
evaluation that enters none (besides its own cell): the closed demand of that cell on `B`
finishes and reads, of `B`, only that cell and cached cells; and the run entered it. The
heap `σ` runs on is `B` with some cells (`M`) marked evaluating (the evaluations it is
nested in) and cells allocated past `B`. -/
theorem pending_within (B : Array Cell) (Bvalid : HeapValid B) :
    ∀ (k : Nat) (σ : State) (w : Nat) (o : Closure) (R : List Frame) (M : Nat → Prop),
      σ.control = .enter w → σ.stack = R → σ.heap[w]? = some (.suspended o) → w < B.size →
      B.size ≤ σ.heap.size →
      (∀ a, a < B.size → ¬ M a → σ.heap[a]? = B[a]?) →
      (∀ a, M a → a < B.size ∧ ∃ o', σ.heap[a]? = some (.evaluating o') ∧ B[a]? = some (.suspended o')) →
      1 ≤ k → (∀ j, j < k → active (exec j σ).control = true) →
      (∀ Y, (exec k σ).stack ≠ Y ++ .update w :: R) →
      ∃ w' o' n' Bw vw, B[w']? = some (.suspended o') ∧ Demand B w' n' Bw vw ∧ PreShallow B w' n' ∧
        ∃ i, i < k ∧ (exec i σ).control = .enter w' ∧ (exec i σ).heap[w']? = some (.suspended o') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro σ w o R M ctl st su wB grow agreeB marks pos alive gone
  obtain ⟨p, v, pPos, pLt, inv, stP, ctlP, nextP, strip, dem⟩ := nested_demand ctl st su pos alive gone
  have notMw : ¬ M w := by
    intro h; obtain ⟨_, o', ev, _⟩ := marks w h; rw [su] at ev; cases ev
  have Bw : B[w]? = some (.suspended o) := by rw [← agreeB w wB notMw]; exact su
  let σ0 := demandStart σ.heap w
  have strip0 : StripInv B σ.heap w σ0 :=
    ⟨fun _ _ _ => rfl, fun fr m => by simp [σ0, demandStart] at m, grow⟩
  have ctlAt : ∀ j, j ≤ p + 1 → (exec j σ0).control = (exec j σ).control := by
    intro j hj; rw [strip j hj]; rfl
  have heapAt : ∀ j, j ≤ p + 1 → (exec j σ0).heap = (exec j σ).heap := by
    intro j hj; rw [strip j hj]; rfl
  -- the enters of suspended cells of B, after the first step
  let Q : Nat → Prop := fun j => 1 ≤ j → j ≤ p + 1 →
    ¬ ∃ b o', b < B.size ∧ (exec j σ0).control = .enter b ∧ (exec j σ0).heap[b]? = some (.suspended o')
  have noPreOf : ∀ i, (i = 0 ∨ Q i) → i ≤ p + 1 → NoPreEntry B w (exec i σ0) := by
    intro i h hi b o' c s' lt
    rcases h with rfl | q
    · simp [exec, σ0, demandStart] at c; exact c.symm
    · by_cases i0 : i = 0
      · subst i0; simp [exec, σ0, demandStart] at c; exact c.symm
      · exact absurd ⟨b, o', lt, c, s'⟩ (q (by omega) hi)
  by_cases allQ : ∀ j, Q j
  · -- the nested evaluation enters no other suspended cell of B: it is pre-shallow
    have noPre : ∀ i, i ≤ p + 1 → NoPreEntry B w (exec i σ0) := fun i hi =>
      noPreOf i (Or.inr (allQ i)) hi
    have stripAt : ∀ j, j ≤ p + 2 → StripInv B σ.heap w (exec j σ0) := fun j hj =>
      stripInv_run strip0 j (fun i lt => noPre i (by omega))
    have halts := dem.halts
    -- what the stripped run reads of B
    have readsB : ∀ j, j < p + 2 → ∀ a, readsAt (exec j σ0) = some a → a < B.size →
        Footprint B w a ∧ ¬ M a := by
      intro j hj a reads lt
      have si := stripAt j (by omega)
      cases c : (exec j σ0).control with
      | enter b =>
        have bEq : b = a := by simp [readsAt, c] at reads; exact reads
        subst bEq
        by_cases isW : b = w
        · subst isW; exact ⟨Or.inl rfl, notMw⟩
        · have keep := si.1 b lt isW
          have stuck : ∀ o', (exec j σ0).heap[b]? ≠ some (.evaluating o') := by
            intro o' ev
            have blk := stepRaw_enter_evaluating c ev
            by_cases last : j + 1 < p + 2
            · have := halts.1 (j + 1) last; rw [exec_succ, blk] at this; cases this
            · have jEq : j = p + 1 := by omega
              subst jEq
              have := ctlAt (p + 1) (Nat.le_refl _)
              rw [c, nextP] at this; cases this
          have notSusp : ∀ o', (exec j σ0).heap[b]? ≠ some (.suspended o') := by
            intro o' sus; exact isW (noPre j (by omega) b o' c sus lt)
          by_cases m : M b
          · obtain ⟨_, o', ev, _⟩ := marks b m
            exact absurd (keep.trans ev) (stuck o')
          · refine ⟨?_, m⟩
            rw [keep, agreeB b lt m] at stuck notSusp
            cases hb : B[b]? with
            | none => simp [Array.getElem?_eq_none_iff] at hb; omega
            | some cell => cases cell with
              | suspended o' => exact absurd hb (notSusp o')
              | evaluating o' => exact absurd hb (stuck o')
              | cached o' v' => exact Or.inr ⟨o', v', hb⟩
      | returned rv =>
        obtain ⟨rest, top⟩ : ∃ rest, (exec j σ0).stack = .update a :: rest := by
          cases stk : (exec j σ0).stack with
          | nil => simp [readsAt, c, stk] at reads
          | cons fr rest =>
            cases fr <;> simp [readsAt, c, stk] at reads
            exact ⟨rest, by rw [reads]⟩
        rcases si.2.1 _ (by rw [top]; exact List.mem_cons_self ..) a rfl with h | h
        · subst h; exact ⟨Or.inl rfl, notMw⟩
        · omega
      | _ => simp [readsAt, c] at reads
    -- the stripped run on σ's heap, mirrored by the demand on B
    let h := backMap B.size σ.heap.size
    let D : Nat → Prop := fun a => a < B.size ∨ σ.heap.size ≤ a
    have start : StateAgree h D M σ0 (demandStart B w) := by
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, fun fr m => by simp [σ0, demandStart] at m, rfl⟩
      · intro a past
        have past' : σ.heap.size ≤ a := past
        refine ⟨Or.inr past', fun mm => by have := (marks a mm).1; omega, ?_⟩
        simp only [h, backMap, show ¬ a < B.size by omega, if_false]
        show a - σ.heap.size + B.size + σ.heap.size = a + B.size; omega
      · intro a b da db eq
        simp only [h, backMap] at eq
        by_cases ha : a < B.size <;> by_cases hb : b < B.size <;> simp only [ha, hb, if_true, if_false] at eq
        · exact eq
        · rcases db with db | db <;> omega
        · rcases da with da | da <;> omega
        · rcases da with da | da <;> rcases db with db | db <;> omega
      · intro a da notM bound
        have aB : a < B.size := by rcases da with da | da; exact da; exact absurd bound (by simp [σ0, demandStart]; omega)
        obtain ⟨c, found⟩ : ∃ c, B[a]? = some c := ⟨B[a], by simp [aB]⟩
        refine ⟨c, by rw [show (σ0.heap) = σ.heap from rfl, agreeB a aB notM]; exact found, ?_, ?_⟩
        · show B[h a]? = some (renameCell h c)
          rw [show h a = a by simp [h, backMap, aB], renameCell_id (fun x m => by
            have := Bvalid _ _ found x m; simp [h, backMap, this])]
          exact found
        · exact fun x m => Or.inl (Bvalid _ _ found x m)
      · show AllIn D [w]; exact fun x m => by simp at m; subst m; exact Or.inl wB
      · show Control.enter w = Control.enter (h w); simp [h, backMap, wB]
    have avoids : ∀ j, j < p + 2 → Avoids M (exec j σ0) := by
      intro j hj a reads mm
      exact (readsB j hj a reads (marks a mm).1).2 mm
    have agreeAt : ∀ j, j ≤ p + 2 → StateAgree h D M (exec j σ0) (exec j (demandStart B w)) :=
      fun j hj => agree_exec start j (fun i lt => avoids i (by omega))
    have fin := agreeAt (p + 2) (Nat.le_refl _)
    rw [dem.final] at fin
    have demB : Demand B w (p + 2) (exec (p + 2) (demandStart B w)).heap (renameValue h v) := by
      refine ⟨⟨fun j lt => ?_, ?_⟩, ?_⟩
      · rw [(agreeAt j (by omega)).active_eq]; exact halts.1 j lt
      · rw [(agreeAt (p + 2) (Nat.le_refl _)).active_eq]; exact halts.2
      · have c := fin.control; have s := fin.stack
        simp only [renameControl, List.map_nil] at c s
        rw [state_ext (s := exec (p + 2) (demandStart B w)), c, s]
    refine ⟨w, o, p + 2, _, _, Bw, demB, ?_, 0, pos, ctl, su⟩
    intro j hj a reads lt
    have rel := agreeAt j (by omega)
    rw [rel.readsAt_eq] at reads
    cases r : readsAt (exec j σ0) with
    | none => rw [r] at reads; cases reads
    | some a' =>
      rw [r] at reads; simp only [Option.map_some, Option.some.injEq] at reads
      have da := rel.readsIn r
      have a'B : a' < B.size := by
        rcases da with da | da
        · exact da
        · simp only [h, backMap, show ¬ a' < B.size by omega, if_false] at reads; omega
      have ha : h a' = a' := by simp [h, backMap, a'B]
      rw [ha] at reads; subst reads
      exact (readsB j (by omega) a' r a'B).1
  · -- the first other suspended cell of B the nested evaluation enters
    obtain ⟨j1, notQ, minQ⟩ := exists_first_fail (P := Q) (by
      apply Classical.byContradiction; intro hc; apply allQ; intro j
      apply Classical.byContradiction; intro hq; exact hc ⟨j, hq⟩)
    have j1Pos : 1 ≤ j1 := by
      apply Classical.byContradiction; intro h0; apply notQ; intro h1; omega
    have j1Le : j1 ≤ p + 1 := by
      apply Classical.byContradiction; intro h0; apply notQ; intro _ h1; omega
    obtain ⟨b, o1, bB, ctlB, suB⟩ : ∃ b o', b < B.size ∧ (exec j1 σ0).control = .enter b ∧
        (exec j1 σ0).heap[b]? = some (.suspended o') := by
      apply Classical.byContradiction; intro hc; exact notQ (fun _ _ => hc)
    have j1LeP : j1 ≤ p := by
      apply Classical.byContradiction; intro h0
      have jEq : j1 = p + 1 := by omega
      subst jEq
      have := ctlAt (p + 1) (Nat.le_refl _); rw [ctlB, nextP] at this; cases this
    have stripJ := stripInv_run strip0 j1 (fun i lt => noPreOf i
      (by by_cases i0 : i = 0; exact Or.inl i0; exact Or.inr (minQ i lt)) (by omega))
    let σ' := exec j1 σ
    have eqσ' : σ' = withStack (exec j1 σ0) R := strip j1 (by omega)
    obtain ⟨⟨Y1, hY1, _⟩, wEval⟩ := inv j1 j1Pos j1LeP
    let M' : Nat → Prop := fun x => M x ∨ x = w
    have r := ih (k - j1) (by omega) σ' b o1 σ'.stack M'
      (by rw [eqσ']; exact ctlB) rfl (by rw [eqσ']; exact suB) bB
      (Nat.le_trans grow (exec_size_mono σ j1))
      (by
        intro a aB notM'
        have ne : a ≠ w := fun e => notM' (Or.inr e)
        have notM : ¬ M a := fun m => notM' (Or.inl m)
        rw [eqσ']; show (exec j1 σ0).heap[a]? = _
        rw [stripJ.1 a aB ne]; exact agreeB a aB notM)
      (by
        intro a m'
        rcases m' with m | rfl
        · obtain ⟨aB, o', ev, bs⟩ := marks a m
          have ne : a ≠ w := fun e => notMw (e ▸ m)
          refine ⟨aB, o', ?_, bs⟩
          rw [eqσ']; show (exec j1 σ0).heap[a]? = _
          rw [stripJ.1 a aB ne]; exact ev
        · exact ⟨wB, o, wEval, Bw⟩)
      (by omega)
      (by intro j lt; show active (exec j (exec j1 σ)).control = true; rw [← exec_add]; exact alive _ (by omega))
      (by
        intro Y eqY
        apply gone (Y ++ .update b :: Y1)
        have : exec (k - j1) σ' = exec k σ := by
          show exec (k - j1) (exec j1 σ) = _; rw [← exec_add, show j1 + (k - j1) = k by omega]
        rw [← this, eqY]
        show Y ++ .update b :: σ'.stack = _
        rw [show σ'.stack = Y1 ++ .update w :: R from hY1]; simp)
    obtain ⟨w', o', n', Bw', vw, bsus, d, ps, i', i'lt, ci, si⟩ := r
    refine ⟨w', o', n', Bw', vw, bsus, d, ps, j1 + i', by omega, ?_, ?_⟩
    · rw [exec_add]; exact ci
    · rw [exec_add]; exact si
#assert_axioms stripInv_step
#assert_axioms stripInv_run
#assert_axioms pending_within

theorem renameControl_id {f : Nat → Nat} {c : Control} (same : ∀ x ∈ controlAddresses c, f x = x) :
    renameControl f c = c := by
  rw [renameControl_congr (g := id) same]
  cases c <;> simp [renameControl, renameValue_id (f := id) (fun _ _ => rfl)]

theorem renameFrame_id {f : Nat → Nat} {fr : Frame} (same : ∀ x ∈ frameAddresses fr, f x = x) :
    renameFrame f fr = fr := by
  rw [renameFrame_congr (g := id) same]
  cases fr <;> simp [renameFrame, renameValue_id (f := id) (fun _ _ => rfl)]

theorem renameStack_id {f : Nat → Nat} {S : List Frame} (same : ∀ fr ∈ S, ∀ x ∈ frameAddresses fr, f x = x) :
    S.map (renameFrame f) = S := by
  conv => rhs; rw [← List.map_id S]
  exact List.map_congr_left (fun fr m => renameFrame_id (same fr m))

/-- A pre-shallow closed demand leaves every other cell of its base unchanged. -/
theorem preShallow_keeps {e : Pending} (valid : e.Valid) {a : Nat} (lt : a < e.base.size) (ne : a ≠ e.cell) :
    e.final[a]? = e.base[a]? := by
  have := exec_preservesCached (demandStart e.base e.cell) e.steps
  rw [valid.demand.final] at this
  cases h : e.base[a]? with
  | none => simp [Array.getElem?_eq_none_iff] at h; omega
  | some c =>
    by_cases ca : ∃ o w, c = .cached o w
    · obtain ⟨o, w, rfl⟩ := ca; exact this a o w h
    · have keep := exec_heap_keep (demandStart e.base e.cell) (a := a) lt e.steps (fun j lt' reads => by
        rcases valid.shallow j lt' a reads ‹_› with eq | ⟨o, w, cw⟩
        · exact ne eq
        · rw [h] at cw; cases cw; exact ca ⟨o, w, rfl⟩)
      rw [valid.demand.final] at keep; rw [keep]; exact h

/-- **The pending link**: on any valid control and stack of the base, the base forces to the
pending demand's final heap through that demand. -/
theorem pendRel_start {e : Pending} (valid : e.Valid) {c : Control} {S : List Frame}
    (cIn : AllIn (· < e.base.size) (controlAddresses c))
    (sIn : ∀ fr ∈ S, AllIn (· < e.base.size) (frameAddresses fr)) :
    PendRel e (liftMap e.base.size e.final.size) ⟨e.base, c, S⟩ ⟨e.final, c, S⟩ := by
  have ge := Pending.final_ge valid
  have cellLt := Pending.cell_lt valid
  let f0 := liftMap e.base.size e.final.size
  have f0Old : ∀ a, a < e.base.size → f0 a = a := fun a lt => by simp [f0, liftMap, lt]
  refine ⟨⟨valid, Nat.le_refl _, valid.susp, fun _ _ _ h => h, f0Old, ?_, ⟨?_, ?_, ?_⟩,
    fun _ _ _ => rfl, rfl⟩, ?_, ?_, ⟨valid.baseValid, cIn, sIn⟩⟩
  · intro a le; simp only [f0, liftMap, show ¬ a < e.base.size by omega, if_false]; rfl
  · intro a past
    have past' : e.base.size ≤ a := past
    refine ⟨trivial, fun h => by have := Pending.cell_lt valid; omega, ?_⟩
    simp only [f0, liftMap, show ¬ a < e.base.size by omega, if_false]
    show a + (e.final.size - e.base.size) + e.base.size = a + e.final.size; omega
  · intro a b _ _ eq
    simp only [f0, liftMap] at eq
    split at eq <;> split at eq <;> omega
  · intro a _ ne lt
    have lt' : a < e.base.size := lt
    obtain ⟨c0, found⟩ : ∃ c0, e.base[a]? = some c0 := ⟨e.base[a], by simp [lt']⟩
    refine ⟨c0, found, ?_, allIn_everywhere _⟩
    show e.final[f0 a]? = _
    rw [f0Old a lt', preShallow_keeps valid lt' ne, found,
      renameCell_id (fun x m => f0Old x (valid.baseValid _ _ found x m))]
  · show c = renameControl f0 c
    rw [renameControl_id (fun x m => f0Old x (cIn x m))]
  · show S = S.map (renameFrame f0)
    rw [renameStack_id (fun fr m x mx => f0Old x (sIn fr m x mx))]

theorem demand_cell_lt {B : Array Cell} {y n : Nat} {Bf : Array Cell} {v : RuntimeValue} (d : Demand B y n Bf v) :
    y < B.size ∧ ((∃ o, B[y]? = some (.suspended o)) ∨ (∃ o w, B[y]? = some (.cached o w) ∧ Bf = B)) := by
  have pos : 1 ≤ n := by
    apply Classical.byContradiction; intro h
    have := d.halts.2; rw [show n = 0 by omega] at this; simp [exec, demandStart, active] at this
  cases h : B[y]? with
  | none =>
    exfalso
    have step : stepRaw (demandStart B y) = ⟨B, .refused .missingCell, []⟩ := by simp [stepRaw, demandStart, h]
    by_cases n1 : n = 1
    · subst n1; have := d.final; rw [exec_one, step] at this; cases this
    · have := d.halts.1 1 (by omega); rw [exec_one, step] at this; cases this
  | some c =>
    have lt : y < B.size := bound_of_some h
    cases c with
    | suspended o => exact ⟨lt, Or.inl ⟨o, rfl⟩⟩
    | evaluating o =>
      exfalso
      have step : stepRaw (demandStart B y) = ⟨B, .blackhole y, []⟩ := by simp [stepRaw, demandStart, h]
      by_cases n1 : n = 1
      · subst n1; have := d.final; rw [exec_one, step] at this; cases this
      · have := d.halts.1 1 (by omega); rw [exec_one, step] at this; cases this
    | cached o w =>
      refine ⟨lt, Or.inr ⟨o, w, rfl, ?_⟩⟩
      have s1 : stepRaw (demandStart B y) = ⟨B, .returned w, []⟩ := by simp [stepRaw, demandStart, h]
      have s2 : exec 2 (demandStart B y) = ⟨B, .complete w, []⟩ := by
        rw [show 2 = 1 + 1 from rfl, exec_succ, exec_one, s1]; rfl
      have h2 : Halts (demandStart B y) 2 := by
        refine ⟨fun j lt => ?_, by rw [s2]; rfl⟩
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · rfl
        · rw [exec_one, s1]; rfl
      have := halts_unique d.halts h2; subst this
      have := d.final; rw [s2] at this; simp at this; exact this.1.symm

/-- **A finished closed demand is a forcing chain** (the main induction). On every valid
control and stack of the demand's base heap, the base heap forces to the demand's final
heap, with headroom the cells the demand allocated, by an address map that is the identity
on the base. -/
theorem demand_forces : ∀ (n : Nat) (B : Array Cell) (y : Nat) (Bf : Array Cell) (v : RuntimeValue),
    HeapValid B → Demand B y n Bf v →
    ∃ F : Nat → Nat, (∀ a, a < B.size → F a = a) ∧
      ∀ (c : Control) (S : List Frame), AllIn (· < B.size) (controlAddresses c) →
        (∀ fr ∈ S, AllIn (· < B.size) (frameAddresses fr)) →
        ForcesBy (Bf.size - B.size) F ⟨B, c, S⟩ ⟨Bf, c, S⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro B y Bf v Bvalid d
  obtain ⟨yB, sus | ⟨o, w, _, BfEq⟩⟩ := demand_cell_lt d
  · obtain ⟨o, su⟩ := sus
    have pos : 1 ≤ n := by
      apply Classical.byContradiction; intro h
      have := d.halts.2; rw [show n = 0 by omega] at this; simp [exec, demandStart, active] at this
    have gone : ∀ Y, (exec n (demandStart B y)).stack ≠ Y ++ [.update y] := by
      intro Y h; rw [d.final] at h; have := congrArg List.length h; simp at this
    obtain ⟨w', o', n', Bw, vw, bsus, dw, ps, i, ilt, ci, si⟩ :=
      pending_within B Bvalid n (demandStart B y) y o [] (fun _ => False) rfl rfl su yB (Nat.le_refl _)
        (fun _ _ _ => rfl) (fun _ h => h.elim) pos d.halts.1 gone
    let e : Pending := ⟨B, w', n', Bw, vw, o'⟩
    have ev : e.Valid := ⟨dw, bsus, ps, Bvalid⟩
    have BwGe : B.size ≤ Bw.size := Pending.final_ge ev
    have BwValid : HeapValid Bw := by
      have := heapValid_exec (addrValid_demandStart Bvalid (Pending.cell_lt ev)) n'
      rw [dw.final] at this; exact this
    have start : PendRel e (liftMap e.base.size e.final.size) (demandStart B y) (demandStart Bw y) :=
      pendRel_start ev (c := .enter y) (S := [])
        (by intro x m; simp [controlAddresses] at m; subst m; exact yB) (fun _ m => by cases m)
    obtain ⟨n2, le2, halts2, _, result⟩ := pend_transfer n _ _ start d.halts
    -- the lazy run entered w' suspended and finished: w' is cached at the end
    have cachedEnd : ∃ oc wc, Bf[w']? = some (.cached oc wc) := by
      obtain ⟨p, vp, _, pLt, inv, _, _, nextP⟩ := nested_pop (σ := exec i (demandStart B y)) (k := n - i)
        ci rfl si (by omega) (fun j lt => by rw [← exec_add]; exact d.halts.1 _ (by omega))
        (fun Y h => by
          rw [← exec_add, show i + (n - i) = n by omega, d.final] at h
          have := congrArg List.length h; simp at this)
      have wLt : w' < (exec p (exec i (demandStart B y))).heap.size := bound_of_some (inv p (by omega) (Nat.le_refl _)).2
      have cachedP : (exec (p + 1) (exec i (demandStart B y))).heap[w']? = some (.cached o' vp) := by
        rw [nextP]; simp [wLt]
      have := exec_preservesCached _ (n - i - (p + 1)) w' o' vp cachedP
      rw [← exec_add, ← exec_add, show i + (p + 1 + (n - i - (p + 1))) = n by omega, d.final] at this
      exact ⟨o', vp, this⟩
    rcases result with pend | ⟨g, agree, cover, ident, _, n2lt, sizeEq⟩
    · exfalso
      obtain ⟨oc, wc, ca⟩ := cachedEnd
      have := pend.heap.cellKept
      rw [d.final] at this; simp only at this; rw [ca] at this; cases this
    · -- the remaining demand of y on Bw is shorter: induction
      have ctlEnd := agree.agree.control
      have stEnd := agree.agree.stack
      rw [d.final] at ctlEnd stEnd
      simp only [renameControl, List.map_nil] at ctlEnd stEnd
      let G := (exec n2 (demandStart Bw y)).heap
      have dG : Demand Bw y n2 G (renameValue g v) := by
        refine ⟨halts2, ?_⟩
        rw [state_ext (s := exec n2 (demandStart Bw y)), ctlEnd, stEnd]
      obtain ⟨F2, F2id, chain2⟩ := ih n2 (by omega) Bw y G _ BwValid dG
      have heapAgree := agree.agree.heap
      rw [d.final] at heapAgree cover sizeEq
      simp only at heapAgree cover sizeEq
      have BfValid : HeapValid Bf := by
        have := heapValid_exec (addrValid_demandStart Bvalid yB) n; rw [d.final] at this; exact this
      have GValid : HeapValid G := heapValid_exec (addrValid_demandStart BwValid (by omega)) n2
      obtain ⟨ginv, inverse, left⟩ := agree_inverse heapAgree cover sizeEq BfValid
      have ginvId : ∀ a, a < B.size → ginv a = a := by
        intro a lt; have := left a (by have := exec_size_mono (demandStart B y) n; rw [d.final] at this; simp [demandStart] at this; omega)
        rw [ident a lt] at this; exact this
      have GsizeEq : G.size = Bf.size := sizeEq
      have GGe : Bw.size ≤ G.size := by
        have := exec_size_mono (demandStart Bw y) n2; simp [demandStart] at this; exact this
      refine ⟨ginv ∘ (F2 ∘ liftMap B.size Bw.size), fun a lt => ?_, fun c S cIn sIn => ?_⟩
      · simp only [Function.comp_apply, liftMap, lt, if_true, F2id a (by omega), ginvId a lt]
      · have l1 : ForcesBy e.gap (liftMap B.size Bw.size) ⟨B, c, S⟩ ⟨Bw, c, S⟩ :=
          .pend (pendRel_start ev cIn sIn) (Nat.le_refl _)
        have l2 := chain2 c S (fun x m => by have := cIn x m; omega)
          (fun fr m x mx => by have := sIn fr m x mx; omega)
        have l3 : ForcesBy 0 ginv ⟨G, c, S⟩ ⟨Bf, c, S⟩ := by
          refine .agree ⟨⟨inverse, allIn_everywhere _, ?_, fun _ _ => allIn_everywhere _, ?_⟩,
            ⟨GValid, fun x m => by show x < G.size; have := cIn x m; omega,
              fun fr m x mx => by show x < G.size; have := sIn fr m x mx; omega⟩⟩ (by show Bf.size ≤ G.size + 0; omega)
          · show c = renameControl ginv c
            rw [renameControl_id (fun x m => ginvId x (cIn x m))]
          · show S = S.map (renameFrame ginv)
            rw [renameStack_id (fun fr m x mx => ginvId x (sIn fr m x mx))]
        refine .trans (.trans l1 l2 (Nat.le_refl _)) l3 ?_
        show e.gap + (G.size - Bw.size) + 0 ≤ Bf.size - B.size
        unfold Pending.gap; simp only [e]; omega
  · subst BfEq
    refine ⟨id, fun _ _ => rfl, fun c S cIn sIn => ?_⟩
    exact .agree (agreeRel_refl ⟨Bvalid, cIn, sIn⟩) (by omega)

#assert_axioms renameControl_id
#assert_axioms renameFrame_id
#assert_axioms renameStack_id
#assert_axioms preShallow_keeps
#assert_axioms pendRel_start
#assert_axioms demand_cell_lt
#assert_axioms demand_forces

end Minidregg.Theory.ObjectiveBendDemandForcing
