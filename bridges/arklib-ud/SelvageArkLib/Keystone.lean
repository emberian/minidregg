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

/-! ## The keystone -/

/-- The Selvage statement named by a restoration input (junk inputs name their move's). -/
def stmtOf : Input r s → Stmt r
  | .inl st => st
  | .inr q => q.stmt

/-- Selvage's statement set, as restoration inputs: junk inputs are never in it. -/
def inputSet (Z : Set (Stmt r)) : Set (Input r s) := {z | ∃ st ∈ Z, z = Sum.inl st}

omit [Finite r.PMsg] in
theorem holds_cast_of_eq {A B : KnowledgeState} (h : A = B) (w : B.Witness) :
    A.holds (cast (congrArg KnowledgeState.Witness h).symm w) ↔ B.holds w := by
  subst h
  rfl

/-- **Selvage's FS/SR keystone from ArkLib's state-restoration theorem** (finite prover-message
alphabets). For every Selvage reduction with `Finite r.PMsg`, every RBR knowledge-soundness
instance, statement set `Z`, and nonnegative uniform bound `εrbr` on the round errors over `Z`,
Selvage's straightline state-restoration knowledge soundness holds at `(t + k) · εrbr δ`, with
the extractor `srExtract rbr` (one extractor for every salt size, budget, proximity bound and
adversary). The probability argument is ArkLib's `restored_extraction_bound`; nothing from
`Selvage/Depth.lean`'s probability tower is used. -/
theorem straightlineSrKnowledgeSoundness_of_arklib (rbr : RbrKnowledgeSoundness r)
    (Z : Set (Stmt r)) (εrbr : ℝ → ℝ)
    (hnn : ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, 0 ≤ εrbr δ)
    (herr : ∀ (i : Fin r.k) (st : Stmt r), st ∈ Z →
      ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, rbr.err i st δ ≤ εrbr δ) :
    StraightlineSrKnowledgeSoundness r Z (fun _s t δ => ((t : ℝ) + (r.k : ℝ)) * εrbr δ) := by
  refine ⟨fun s => srExtract rbr s, fun s t δ hδ P => ?_⟩
  let state : Input r s → KnowledgeState := fun z => kstateAt rbr δ (stmtOf z) ⟨[], none⟩
  let extractor : (z : Input r s) →
      RoundExtractor (protocol (List.replicate r.k (round r))).tree (state z) :=
    fun z => selvageExtractor rbr δ (stmtOf z) r.k []
  let terminalWitness : (z : Input r s) →
      (path : (protocol (List.replicate r.k (round r))).tree.ExecutionPath) →
        r.W → ((extractor z).terminalState path).Witness :=
    fun z path => toTerminal rbr δ (stmtOf z) r.k [] path
  have hArk := restored_extraction_bound (Salt := Minidregg.Selvage.Salt s) state extractor
    (inputSet Z) (ENNReal.ofReal (εrbr δ))
    (fun z _ => selvageExtractor_isProverPreserving rbr hδ (stmtOf z) r.k [] (by simp))
    (fun z hz => by
      obtain ⟨st, hst, rfl⟩ := hz
      exact selvageExtractor_isLocallyBounded rbr hδ st (εrbr δ)
        (fun i => herr i st hst δ hδ) r.k [] (by simp))
    terminalWitness (adversary P t) t (adversary_queryBound P t)
  -- the ArkLib event, named
  let arkEvent : Input r s × (protocol (List.replicate r.k (round r))).tree.ExecutionPath × r.W →
      Prop := fun result =>
    result.1 ∈ inputSet Z ∧
      ((extractor result.1).terminalState result.2.1).holds
        (terminalWitness result.1 result.2.1 result.2.2) ∧
      ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1
        (terminalWitness result.1 result.2.1 result.2.2))
  -- Selvage's event, named
  let selEvent : (Fin t → r.Chal) × (Fin r.k → r.Chal) → Prop := fun coins =>
    let log := srTrace P coins.1
    let o := P.out (log.map Prod.snd)
    let ρs : Fin r.k → r.Chal := srFinalChal P coins.1 coins.2
    o.stmt ∈ Z ∧
    ¬ RelaxedMem r.R δ o.stmt.idx o.stmt.x o.stmt.y (srExtract rbr s o ρs log) ∧
    ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
      r.verify o.stmt.idx o.stmt.x o.stmt.y o.πs ρs = some (x', y') ∧
      RelaxedMem r.R' δ o.stmt.idx x' y' o.w'
  -- the run on every coin vector
  let cOf : (Fin (t + r.k) → r.Chal) → Fin t → r.Chal := fun v i => v (i.castLE (by omega))
  let dOf : (Fin (t + r.k) → r.Chal) → Fin r.k → r.Chal := fun v i => v (i.natAdd t)
  choose cacheOf pathOf hrun hpath using fun v : Fin (t + r.k) → r.Chal =>
    restoredExecution_run P t (cOf v) (dOf v)
  -- pointwise: the ArkLib event on the run is Selvage's event on the split coins
  have hevent : ∀ v, arkEvent (Sum.inl (srOut P (cOf v)).stmt, pathOf v, (srOut P (cOf v)).w') ↔
      selEvent (cOf v, dOf v) := by
    intro v
    set st := (srOut P (cOf v)).stmt
    have hterm := holds_cast_of_eq (terminalState_selvageExtractor rbr δ st r.k [] (pathOf v))
      (srOut P (cOf v)).w'
    have hext := extractWitness_selvageExtractor rbr δ st r.k [] (pathOf v) (srOut P (cOf v)).w'
    simp only [List.nil_append, hpath v] at hterm hext
    rw [backward_nil_eq_wAt] at hext
    have hfull := rbr.kstate.full_iff δ hδ st (srOut P (cOf v)).πs (srFinalChal P (cOf v) (dOf v))
      (srOut P (cOf v)).w'
    have hmem : (Sum.inl st : Input r s) ∈ inputSet Z ↔ st ∈ Z :=
      ⟨fun ⟨a, ha, h⟩ => Sum.inl_injective h ▸ ha, fun h => ⟨st, h, rfl⟩⟩
    have hA : ((extractor (Sum.inl st)).terminalState (pathOf v)).holds
        (terminalWitness (Sum.inl st) (pathOf v) (srOut P (cOf v)).w') ↔
          ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
            r.verify st.idx st.x st.y (srOut P (cOf v)).πs (srFinalChal P (cOf v) (dOf v)) =
              some (x', y') ∧ RelaxedMem r.R' δ st.idx x' y' (srOut P (cOf v)).w' :=
      hterm.trans (by
        show rbr.kstate.state δ st ⟨pathRounds r.k (pathOf v), none⟩ (srOut P (cOf v)).w' = true ↔ _
        rw [hpath v]
        exact hfull)
    have hB : (state (Sum.inl st)).holds ((extractor (Sum.inl st)).extractWitness (pathOf v)
        (terminalWitness (Sum.inl st) (pathOf v) (srOut P (cOf v)).w')) ↔
          RelaxedMem r.R δ st.idx st.x st.y (wAt rbr st (List.ofFn fun i =>
            ((srOut P (cOf v)).πs i, srFinalChal P (cOf v) (dOf v) i)) (srOut P (cOf v)).w' 0) := by
      change rbr.kstate.state δ st Transcript.empty
        ((extractor (Sum.inl st)).extractWitness (pathOf v)
          (terminalWitness (Sum.inl st) (pathOf v) (srOut P (cOf v)).w')) = true ↔ _
      have hext' : (extractor (Sum.inl st)).extractWitness (pathOf v)
          (terminalWitness (Sum.inl st) (pathOf v) (srOut P (cOf v)).w') =
            wAt rbr st (List.ofFn fun i => ((srOut P (cOf v)).πs i,
              srFinalChal P (cOf v) (dOf v) i)) (srOut P (cOf v)).w' 0 := hext
      rw [hext']
      exact rbr.kstate.empty_iff δ hδ st _
    change ((Sum.inl st : Input r s) ∈ inputSet Z ∧ _ ∧ ¬ _) ↔
      (st ∈ Z ∧ ¬ RelaxedMem r.R δ st.idx st.x st.y (wAt rbr st (List.ofFn fun i =>
          ((srOut P (cOf v)).πs i, srFinalChal P (cOf v) (dOf v) i)) (srOut P (cOf v)).w' 0) ∧
        ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
          r.verify st.idx st.x st.y (srOut P (cOf v)).πs (srFinalChal P (cOf v) (dOf v)) =
            some (x', y') ∧ RelaxedMem r.R' δ st.idx x' y' (srOut P (cOf v)).w')
    rw [hmem, hA, hB]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h3, h2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h3, h2⟩
  -- couple ArkLib's game to the coin vector
  have hcoup := StepCoins.evalDist_run_randomOracle_eq_stepCoins (C := r.Chal)
    (key_challenge_eq r.k) (restoredExecution (List.replicate r.k (round r)) (adversary P t))
    ∅ (t + r.k)
  have hprob : Pr{let result ← (simulateQ randomOracle
        (restoredExecution (List.replicate r.k (round r)) (adversary P t))).run' ∅}[
          arkEvent result] = ENNReal.ofReal (uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal))
            selEvent) := by
    let _ : MeasurableSpace (Input r s × (protocol (List.replicate r.k (round r))).tree.ExecutionPath
      × r.W) := ⊤
    rw [StateT.run'_eq, prEvent_map]
    rw [(EvalDistEq.of_evalDist_eq hcoup).prEvent_eq]
    have hcomp : (do
          let l ← AnswerTape.tapeList r.Chal (t + r.k)
          let z ← (simulateQ (stepImpl r s)
            (restoredExecution (List.replicate r.k (round r)) (adversary P t))).run (∅, l)
          return (z.1, z.2.1)) =
        (fun v => ((Sum.inl (srOut P (cOf v)).stmt, pathOf v, (srOut P (cOf v)).w'),
          cacheOf v)) <$> AnswerTape.answerTape r.Chal (t + r.k) := by
      rw [AnswerTape.tapeList_eq_map_answerTape, bind_map_left, map_eq_bind_pure_comp]
      refine bind_congr fun v => ?_
      rw [show List.ofFn v = List.ofFn (cOf v) ++ List.ofFn (dOf v) from List.ofFn_add, hrun v,
        pure_bind]
      rfl
    rw [hcomp, prEvent_map]
    rw [prEvent_answerTape_eq_ofReal]
    congr 1
    rw [← uniformProb_equiv (Fin.appendEquiv t r.k)]
    apply uniformProb_congr
    intro cd
    rw [hevent]
    have hc : cOf (Fin.appendEquiv t r.k cd) = cd.1 := by
      funext i
      simp only [cOf, Fin.appendEquiv, Equiv.coe_fn_mk]
      exact Fin.append_left cd.1 cd.2 i
    have hd : dOf (Fin.appendEquiv t r.k cd) = cd.2 := by
      funext i
      simp only [dOf, Fin.appendEquiv, Equiv.coe_fn_mk]
      exact Fin.append_right cd.1 cd.2 i
    rw [hc, hd]
  -- read the bound back in ℝ
  have hbound : ENNReal.ofReal (uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal)) selEvent) ≤
      ENNReal.ofReal (((t : ℝ) + (r.k : ℝ)) * εrbr δ) := by
    rw [← hprob]
    refine hArk.trans (le_of_eq ?_)
    rw [List.length_replicate, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add
      (by positivity) (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (hnn δ hδ))).mp hbound

/-- The same keystone in Selvage's Fiat–Shamir form (`FsOfRbrSound`'s conclusion), through
Selvage's own game equivalence `fsStraightline_iff_sr`. -/
theorem fsStraightlineKnowledgeSoundness_of_arklib (rbr : RbrKnowledgeSoundness r)
    (Z : Set (Stmt r)) (εrbr : ℝ → ℝ)
    (hnn : ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, 0 ≤ εrbr δ)
    (herr : ∀ (i : Fin r.k) (st : Stmt r), st ∈ Z →
      ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, rbr.err i st δ ≤ εrbr δ) :
    FsStraightlineKnowledgeSoundness r Z (fun _s t δ => ((t : ℝ) + (r.k : ℝ)) * εrbr δ) :=
  (fsStraightline_iff_sr r Z _).mpr
    (straightlineSrKnowledgeSoundness_of_arklib rbr Z εrbr hnn herr)

end SelvageArkLib.StateRestoration

/-- info: 'SelvageArkLib.StateRestoration.straightlineSrKnowledgeSoundness_of_arklib' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SelvageArkLib.StateRestoration.straightlineSrKnowledgeSoundness_of_arklib

/-- info: 'SelvageArkLib.StateRestoration.fsStraightlineKnowledgeSoundness_of_arklib' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SelvageArkLib.StateRestoration.fsStraightlineKnowledgeSoundness_of_arklib
