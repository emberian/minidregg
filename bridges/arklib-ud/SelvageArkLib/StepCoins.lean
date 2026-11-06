import VCVio.OracleComp.QueryTracking.RandomOracle.Tape

/-!
# The lazy random oracle with one coin per query

`stepCoinImpl` answers like the lazy random oracle `OracleSpec.randomOracle`, except that every
query consumes the next coin of a supplied list. A fresh query is answered by that coin and caches
it; a cached query ignores it. This is the positional coin discipline of state-restoration games
written over a coin vector (Selvage's `srTrace`/`srFinalChal`: move `j` reads coin `c j`, final slot
`i` reads coin `d i`, each used only if its query is fresh).

VCVio's `AnswerTape.tapeCachingImpl` consumes a coin only on fresh queries. The two disciplines
differ pathwise and agree in distribution. `evalDist_run_randomOracle_eq_stepCoins` proves the
latter directly: averaged over a list of `m` independent uniform coins, the step-coin oracle *is*
the lazy random oracle, jointly in the output and the final cache, for every `m`. Once the list
runs out it samples fresh, so no query bound is needed for the identity.

The oracle may have dependent answer types `R t`; coins live in one type `C` with `R t = C`.
-/

noncomputable section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace SelvageArkLib.StepCoins

variable {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ t, SampleableType (R t)]
  {C : Type} [SampleableType C]

/-- The step-coin lazy oracle: each query consumes one coin; a fresh query is answered by it. -/
def stepCoinImpl (hR : ∀ t, R t = C) :
    QueryImpl (OracleSpec.ofFn R) (StateT ((OracleSpec.ofFn R).QueryCache × List C) ProbComp) :=
  fun t => StateT.mk fun s =>
    match s.2 with
    | u :: l =>
        match s.1 t with
        | some v => pure (v, (s.1, l))
        | none => pure (cast (hR t).symm u, (s.1.cacheQuery t (cast (hR t).symm u), l))
    | [] =>
        match s.1 t with
        | some v => pure (v, (s.1, []))
        | none => (fun v => (v, (s.1.cacheQuery t v, ([] : List C)))) <$> ($ᵗ R t : ProbComp (R t))

theorem stepCoinImpl_run_cons_some (hR : ∀ t, R t = C) {t : ι}
    {c : (OracleSpec.ofFn R).QueryCache} {u : C} {l : List C} {v : R t} (h : c t = some v) :
    ((stepCoinImpl hR) t).run (c, u :: l) = pure (v, (c, l)) := by
  first
  | (simp only [stepCoinImpl, StateT.run_mk]; simp [h])
  | (unfold stepCoinImpl; dsimp only [StateT.run, StateT.mk]; simp [h])

theorem stepCoinImpl_run_cons_none (hR : ∀ t, R t = C) {t : ι}
    {c : (OracleSpec.ofFn R).QueryCache} {u : C} {l : List C} (h : c t = none) :
    ((stepCoinImpl hR) t).run (c, u :: l) =
      pure (cast (hR t).symm u, (c.cacheQuery t (cast (hR t).symm u), l)) := by
  first
  | (simp only [stepCoinImpl, StateT.run_mk]; simp [h])
  | (unfold stepCoinImpl; dsimp only [StateT.run, StateT.mk]; simp [h])

theorem stepCoinImpl_run_nil_some (hR : ∀ t, R t = C) {t : ι}
    {c : (OracleSpec.ofFn R).QueryCache} {v : R t} (h : c t = some v) :
    ((stepCoinImpl hR) t).run (c, []) = pure (v, (c, [])) := by
  first
  | (simp only [stepCoinImpl, StateT.run_mk]; simp [h])
  | (unfold stepCoinImpl; dsimp only [StateT.run, StateT.mk]; simp [h])

theorem stepCoinImpl_run_nil_none (hR : ∀ t, R t = C) {t : ι}
    {c : (OracleSpec.ofFn R).QueryCache} (h : c t = none) :
    ((stepCoinImpl hR) t).run (c, []) =
      (fun v => (v, (c.cacheQuery t v, ([] : List C)))) <$> ($ᵗ R t : ProbComp (R t)) := by
  first
  | (simp only [stepCoinImpl, StateT.run_mk]; simp [h])
  | (unfold stepCoinImpl; dsimp only [StateT.run, StateT.mk]; simp [h])

/-- A uniform coin cast along an equality of types is a uniform sample of the target. -/
theorem evalDist_uniformSample_bind_cast {α β δ : Type} [iα : SampleableType α]
    [iβ : SampleableType β] [MeasurableSpace δ] (h : α = β) (F : α → ProbComp δ) :
    𝒟[($ᵗ β : ProbComp β) >>= fun u => F (cast h.symm u)] = 𝒟[($ᵗ α : ProbComp α) >>= F] := by
  subst h
  let _ : MeasurableSpace α := ⊤
  simp only [cast_eq]
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
    SampleableType.evalDist_uniformSample_inst_irrel iβ iα]

/-- **The lazy random oracle is the step-coin oracle averaged over iid coins.** For every coin
count `m`, running `oa` under the lazy random oracle from cache `c` has the same joint
distribution of output and final cache as drawing `m` independent uniform coins and running `oa`
under `stepCoinImpl` from `c` with them. -/
theorem evalDist_run_randomOracle_eq_stepCoins (hR : ∀ t, R t = C) {α : Type}
    (oa : OracleComp (OracleSpec.ofFn R) α) (c : (OracleSpec.ofFn R).QueryCache) (m : ℕ) :
    letI : MeasurableSpace (α × (OracleSpec.ofFn R).QueryCache) := ⊤
    𝒟[(simulateQ (OracleSpec.randomOracle (spec := OracleSpec.ofFn R)) oa).run c] =
      𝒟[(do let l ← AnswerTape.tapeList C m
            let z ← (simulateQ (stepCoinImpl hR) oa).run (c, l)
            return (z.1, z.2.1))] := by
  let _ : MeasurableSpace (α × (OracleSpec.ofFn R).QueryCache) := ⊤
  let _ : MeasurableSpace C := ⊤
  let _ : MeasurableSpace (List C) := ⊤
  induction oa using OracleComp.inductionOn generalizing c m with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    rw [_root_.evalDist_bind_const]
    rw [measure_univ, one_smul]
  | query_bind t k ih =>
    let _ : MeasurableSpace (R t) := ⊤
    have hredL : (simulateQ (OracleSpec.randomOracle (spec := OracleSpec.ofFn R))
          (liftM ((OracleSpec.ofFn R).query t) >>= k)).run c =
        ((OracleSpec.randomOracle (spec := OracleSpec.ofFn R) t).run c) >>= fun p =>
          (simulateQ OracleSpec.randomOracle (k p.1)).run p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hredR : ∀ l : List C,
        (simulateQ (stepCoinImpl hR) (liftM ((OracleSpec.ofFn R).query t) >>= k)).run (c, l) =
          (((stepCoinImpl hR) t).run (c, l)) >>= fun p =>
            (simulateQ (stepCoinImpl hR) (k p.1)).run p.2 := fun l => by
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [hredL]
    simp only [hredR]
    cases m with
    | zero =>
      simp only [AnswerTape.tapeList_zero, pure_bind]
      rcases hc : c t with _ | u
      · rw [randomOracle.run_eq, hc, stepCoinImpl_run_nil_none hR hc]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
        apply Measure.bind_congr_right
        filter_upwards [] with v
        simpa only [AnswerTape.tapeList_zero, pure_bind] using ih v (c.cacheQuery t v) 0
      · rw [randomOracle.run_eq, hc, pure_bind, stepCoinImpl_run_nil_some hR hc, pure_bind]
        simpa only [AnswerTape.tapeList_zero, pure_bind] using ih u c 0
    | succ m' =>
      simp only [AnswerTape.tapeList_succ, bind_assoc, pure_bind]
      rcases hc : c t with _ | u
      · rw [randomOracle.run_eq, hc]
        simp only [stepCoinImpl_run_cons_none hR hc, pure_bind, bind_assoc]
        refine Eq.trans ?_ (evalDist_uniformSample_bind_cast (hR t) (fun v =>
          AnswerTape.tapeList C m' >>= fun l =>
            (simulateQ (stepCoinImpl hR) (k v)).run (c.cacheQuery t v, l) >>= fun z =>
              pure (z.1, z.2.1))).symm
        rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
        apply Measure.bind_congr_right
        filter_upwards [] with v
        exact ih v (c.cacheQuery t v) m'
      · rw [randomOracle.run_eq, hc, pure_bind]
        simp only [stepCoinImpl_run_cons_some hR hc, pure_bind]
        rw [_root_.evalDist_bind_const, measure_univ, one_smul]
        exact ih u c m'

end SelvageArkLib.StepCoins

/-- info: 'SelvageArkLib.StepCoins.evalDist_run_randomOracle_eq_stepCoins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SelvageArkLib.StepCoins.evalDist_run_randomOracle_eq_stepCoins
