import SelvageArkLib.Restoration

/-!
# Selvage's straightline state-restoration soundness, derived from ArkLib

`straightlineSrKnowledgeSoundness_of_arklib` proves Selvage's
`StraightlineSrKnowledgeSoundness r Z (fun _ t δ => (t + k) · ε)` for every reduction whose prover
messages form a finite type, from ArkLib's `restored_extraction_bound` (ArkLib #1263). The proof
does not use `Selvage/Depth.lean`'s probability tower (`gameSlotBound_proved`,
`OB2_depth_composition_nonneg_proved`). It uses only:

* the certificate translation (`selvageExtractor_*`, `extractWitness_selvageExtractor`),
* the coupling `StepCoins.evalDist_run_randomOracle_eq_stepCoins`, and
* the deterministic correspondence `adversarySteps_run` / `complete_run`.

Its hypotheses are exactly `FsOfRbrSound`'s, including the nonnegativity guard `0 ≤ ε`. In this
derivation the guard is needed to read ArkLib's `ENNReal.ofReal ε` back as `ε`, the same corner
that `OB2_depth_composition_false` exhibits.
-/

noncomputable section

open Classical

namespace SelvageArkLib.StateRestoration

open Minidregg.Selvage
open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec MeasureTheory
open Interaction.Oracle.TypeTree
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration

variable {r : Reduction} [Finite r.PMsg] {s : ℕ}

attribute [local instance] SampleableType.ofFintype

/-! ## Uniform tapes count -/

/-- A probability over an iid uniform tape is Selvage's counting probability on tuples. -/
theorem prEvent_answerTape_eq_ofReal (C : Type) [Fintype C] [Nonempty C] [SampleableType C]
    (m : ℕ) (p : (Fin m → C) → Prop) :
    Pr{let v ← AnswerTape.answerTape C m}[p v] = ENNReal.ofReal (uniformProb (Fin m → C) p) := by
  rw [ofReal_uniformProb_eq_prEvent (Fin m → C) p]
  let _ : MeasurableSpace C := ⊤
  have hdist : 𝒟[AnswerTape.answerTape C m] = 𝒟[($ᵗ (Fin m → C) : ProbComp (Fin m → C))] := by
    apply Measure.ext_of_singleton
    intro v
    rw [← Set.univ_pi_singleton, AnswerTape.evalDist_answerTape_univPi,
      SampleableType.evalDist_uniformSample, Set.univ_pi_singleton]
    simp only [SampleableType.evalDist_uniformSample, ProbabilityTheory.uniformOn_univ,
      Measure.count_singleton, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Fintype.card_pi, Fintype.card_fin]
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_one, mul_one, Nat.cast_pow,
      ENNReal.inv_pow]
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete, hdist]

/-! ## The whole restoration run on Selvage's coins -/

/-- Selvage's lookup-or-coin resolution is the cache read under agreement. -/
theorem resolveAt_of_cacheAgrees {cache : (rspec r s).QueryCache} {L : List (SrMove r s × r.Chal)}
    (h : CacheAgrees cache L) (q : SrMove r s) (d : r.Chal) :
    resolveAt cache (encodeMove q) d = resolveIn L q d := by
  have hq := h q
  unfold resolveAt resolveIn
  unfold logLookup at hq
  cases hc : cache (encodeMove q) with
  | some v =>
      rw [hc] at hq
      cases hf : L.find? (fun e => decide (e.1 = q)) with
      | none => rw [hf] at hq; simp at hq
      | some e => rw [hf] at hq; simpa using hq
  | none =>
      rw [hc] at hq
      cases hf : L.find? (fun e => decide (e.1 = q)) with
      | none => rfl
      | some e => rw [hf] at hq; simp at hq

theorem completionRounds_ofFn (look : List (r.PMsg × Minidregg.Selvage.Salt s) → r.Chal → r.Chal) :
    (n : ℕ) → (pre : List (r.PMsg × Minidregg.Selvage.Salt s)) →
    (f : Fin n → r.PMsg × Minidregg.Selvage.Salt s) → (g : Fin n → r.Chal) →
    completionRounds look pre (List.ofFn f) (List.ofFn g) =
      List.ofFn fun i => ((f i).1, look (pre ++ (List.ofFn f).take ((i : ℕ) + 1)) (g i))
  | 0, _, _, _ => by simp [completionRounds]
  | n + 1, pre, f, g => by
      rw [List.ofFn_succ (f := f), List.ofFn_succ (f := g), completionRounds,
        completionRounds_ofFn look n (pre ++ [f 0]) (fun i => f i.succ) (fun i => g i.succ),
        List.ofFn_succ (n := n)]
      simp [List.take_succ_cons, List.append_assoc]

theorem outputPrefix_take (o : SrOutput r s) (i : Fin r.k) :
    (outputPrefix o).take ((i : ℕ) + 1) = (o.query i).pfx := by
  simp [outputPrefix, SrOutput.query, List.ofFn_eq_map, List.map_take]

/-- **The restoration run on Selvage's coins is Selvage's game.** The induced adversary followed
by ArkLib's completion, on move coins `c` and completion coins `d`, outputs Selvage's statement and
candidate witness along a path whose rounds are Selvage's final transcript. -/
theorem restoredExecution_run (P : SrProver r s) (t : ℕ) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) :
    ∃ cache path, (simulateQ (stepImpl r s)
        (restoredExecution (List.replicate r.k (round r)) (adversary P t))).run
          (∅, List.ofFn c ++ List.ofFn d) =
        pure ((Sum.inl (srOut P c).stmt, path, (srOut P c).w'), (cache, [])) ∧
      pathRounds r.k path = List.ofFn fun i => ((srOut P c).πs i, srFinalChal P c d i) := by
  obtain ⟨cache₁, h₁, hagree⟩ := adversarySteps_run P (List.ofFn c) (List.ofFn d) []
    (∅ : (rspec r s).QueryCache) (fun q => by simp [logLookup])
  rw [← srTrace_eq_runFrom] at h₁ hagree
  simp only [List.length_ofFn, List.map_nil] at h₁
  set o := srOut P c with ho
  obtain ⟨cache₂, path, h₂, hpath⟩ := complete_run o.stmt r.k id (fun _ => rfl) []
    (fun q hq => by simpa using encodeMove_keyPrefix o.stmt q hq) (outputPrefix o)
    (by simp [outputPrefix]) (List.ofFn d) [] (by simp) cache₁
  rw [simulateQ_embImpl_id, List.append_nil] at h₂
  refine ⟨cache₂, path, ?_, ?_⟩
  · simp only [restoredExecution, adversary, simulateQ_bind, StateT.run_bind, h₁, pure_bind,
      simulateQ_pure, StateT.run_pure]
    rw [show P.out ((srTrace P c).map Prod.snd) = o from rfl, h₂, pure_bind]
  · rw [hpath, outputPrefix, completionRounds_ofFn]
    congr 1
    funext i
    rw [List.nil_append, ← outputPrefix, outputPrefix_take, show (⟨o.stmt, (o.query i).pfx⟩ :
      SrMove r s) = o.query i from rfl, resolveAt_of_cacheAgrees hagree,
      ← srFinalChal_eq_resolveIn]

end SelvageArkLib.StateRestoration
