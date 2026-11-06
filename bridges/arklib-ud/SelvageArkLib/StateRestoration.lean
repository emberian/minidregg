import ArkLib.Interaction.Oracle.Security.StateRestorationGame
import Selvage.FiatShamir

/-!
# Selvage's state-restoration keystone from ArkLib's

ArkLib proves round-by-round knowledge soundness implies state-restoration knowledge soundness
(`Interaction.Oracle.Security.StateRestoration.restored_extraction_bound`, and its verifier form
`stateRestoration_knowledge_soundness`, ArkLib #1263) at `(Q + k) * error`. Selvage proves the
same bound for its own game (`Minidregg.Selvage.OB2_depth_composition_nonneg_proved`, WARP
ePrint 2025/753 Thm B.4). This file derives Selvage's statement from ArkLib's.

## Translation

* A Selvage `Reduction` with `k` rounds is the ArkLib fixed-round protocol
  `protocol (List.replicate r.k (round r))`: each round is an oracle prover message of type
  `r.PMsg` (identity interface) followed by a uniform public challenge in `r.Chal`.
* At proximity `δ` and statement `st`, the knowledge state at a prefix is Selvage's bit
  `kstate.state δ st tr` on the matching `Transcript`, over the constant carrier `r.W`.
  The backward map is the identity at prover messages and `rbr.extract` at challenges
  (`selvageExtractor`). Selvage's `prover_monotone` is ArkLib's `IsProverPreserving`
  (`selvageExtractor_isProverPreserving`), and Selvage's `extract_sound` event is ArkLib's
  `badChallenge` verbatim, so `IsLocallyBounded` holds at `ENNReal.ofReal ε`
  (`selvageExtractor_isLocallyBounded`).

ArkLib requires a finite message type (`Round.finiteMessage`); Selvage allows any nonempty
`PMsg`. This file assumes `[Finite r.PMsg]` and says so in each statement that needs it.
-/

noncomputable section

open Classical

namespace SelvageArkLib.StateRestoration

open Minidregg.Selvage
open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration

variable (r : Reduction)

/-- A prover message is an oracle whose single query returns the message itself. -/
@[instance_reducible] def messageInterface : OracleInterface r.PMsg where
  Query := Unit
  toOC := { spec := fun _ => r.PMsg, impl := fun _ message => message }

/-- One Selvage round as an ArkLib fixed round: an oracle prover message, then a uniform
challenge. -/
@[implicit_reducible] def round [Finite r.PMsg] : Round where
  Message := r.PMsg
  Challenge := r.Chal
  interface := messageInterface r
  decEqMessage := Classical.decEq _
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := SampleableType.ofFintype r.Chal

/-- The `k`-round ArkLib presentation of a Selvage reduction. -/
abbrev rounds [Finite r.PMsg] : List Round := List.replicate r.k (round r)

variable {r}

/-- Selvage's knowledge-state bit at `δ`, `st` and `tr`, as an ArkLib knowledge state over the
constant carrier `r.W`. -/
def kstateAt (rbr : RbrKnowledgeSoundness r) (δ : ℝ) (st : Stmt r)
    (tr : Transcript r.PMsg r.Chal) : KnowledgeState where
  Witness := r.W
  holds := fun w => rbr.kstate.state δ st tr w = true

/-- The named backward extractor: identity at prover messages, `rbr.extract` at challenges.
`rs` is the list of completed rounds before the current prefix. -/
def selvageExtractor [Finite r.PMsg] (rbr : RbrKnowledgeSoundness r) (δ : ℝ) (st : Stmt r) :
    (n : ℕ) → (rs : List (r.PMsg × r.Chal)) →
    RoundExtractor (protocol (List.replicate n (round r))).tree (kstateAt rbr δ st ⟨rs, none⟩)
  | 0, _ => PUnit.unit
  | n + 1, rs => fun (message : r.PMsg) =>
      ⟨kstateAt rbr δ st ⟨rs, some message⟩, id, fun (challenge : r.Chal) =>
        ⟨kstateAt rbr δ st ⟨rs ++ [(message, challenge)], none⟩,
          rbr.extract st ⟨rs ++ [(message, challenge)], none⟩,
          selvageExtractor rbr δ st n (rs ++ [(message, challenge)])⟩⟩

/-- Selvage's `prover_monotone` is ArkLib's prover preservation, at every prefix of a `k`-round
interaction. -/
theorem selvageExtractor_isProverPreserving [Finite r.PMsg] (rbr : RbrKnowledgeSoundness r)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (st : Stmt r) :
    (n : ℕ) → (rs : List (r.PMsg × r.Chal)) → rs.length + n = r.k →
    (selvageExtractor rbr δ st n rs).IsProverPreserving
      (protocol (List.replicate n (round r))).roles
  | 0, _, _ => trivial
  | n + 1, rs, hlen => by
      refine ⟨fun (message : r.PMsg) (w : r.W) hafter => ?_,
        fun (message : r.PMsg) => ⟨?_, fun (challenge : r.Chal) => ?_⟩⟩
      · change rbr.kstate.state δ st ⟨rs, some message⟩ w = true at hafter
        change rbr.kstate.state δ st ⟨rs, none⟩ w = true
        by_contra hbefore
        have hfalse : rbr.kstate.state δ st ⟨rs, none⟩ w = false := by
          simpa using hbefore
        have := rbr.kstate.prover_monotone δ hδ st rs w (by omega) hfalse message
        rw [this] at hafter
        exact Bool.false_ne_true hafter
      · intro challenge hsender
        nomatch hsender
      · exact selvageExtractor_isProverPreserving rbr hδ st n _ (by simp; omega)

/-- Selvage's counting probability is VCVio's uniform-sample probability. -/
theorem ofReal_uniformProb_eq_prEvent (C : Type) [Fintype C] [Nonempty C]
    [SampleableType C] (p : C → Prop) :
    ENNReal.ofReal (uniformProb C p) = Pr{let c ← $ᵗ C}[p c] := by
  rw [SampleableType.prEvent_uniformSample p]
  unfold uniformProb
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos)]
  rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-- Selvage's `extract_sound` is ArkLib's all-prefix local bound, at every prefix of a `k`-round
interaction, with error `ENNReal.ofReal ε` for any real `ε` dominating the round errors at `st`. -/
theorem selvageExtractor_isLocallyBounded [Finite r.PMsg] (rbr : RbrKnowledgeSoundness r)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (st : Stmt r) (ε : ℝ)
    (herr : ∀ i : Fin r.k, rbr.err i st δ ≤ ε) :
    (n : ℕ) → (rs : List (r.PMsg × r.Chal)) → rs.length + n = r.k →
    (selvageExtractor rbr δ st n rs).IsLocallyBounded
      (protocol (List.replicate n (round r))).roles
      (uniformSchedule (ENNReal.ofReal ε) (List.replicate n (round r)))
  | 0, _, _ => trivial
  | n + 1, rs, hlen => fun (message : r.PMsg) => by
      refine ⟨?_, fun challenge =>
        selvageExtractor_isLocallyBounded rbr hδ st ε herr n _ (by simp; omega)⟩
      apply (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mpr
      intro _ _
      change Pr{let ρ ← $ᵗ (round r).Challenge}[
        RoundExtractor.badChallenge
          ((selvageExtractor rbr δ st (n + 1) rs message).2.2) ρ] ≤ ENNReal.ofReal ε
      let _ : SampleableType r.Chal := SampleableType.ofFintype r.Chal
      change Pr{let ρ ← $ᵗ r.Chal}[∃ w : r.W,
          ¬ (rbr.kstate.state δ st ⟨rs, some message⟩
              (rbr.extract st ⟨rs ++ [(message, ρ)], none⟩ w) = true) ∧
          rbr.kstate.state δ st ⟨rs ++ [(message, ρ)], none⟩ w = true] ≤ ENNReal.ofReal ε
      simp only [Bool.not_eq_true]
      rw [← ofReal_uniformProb_eq_prEvent]
      have hi : rs.length < r.k := by omega
      exact ENNReal.ofReal_le_ofReal
        ((rbr.extract_sound δ hδ st ⟨rs.length, hi⟩ rs rfl message).trans (herr _))

/-! ## Backward extraction is Selvage's Construction B.5 -/

/-- The completed rounds read off an ArkLib execution path of the `n`-round presentation. -/
def pathRounds [Finite r.PMsg] :
    (n : ℕ) → (protocol (List.replicate n (round r))).tree.ExecutionPath →
      List (r.PMsg × r.Chal)
  | 0, _ => []
  | n + 1, path => (⟨path.1, path.2.1⟩ : r.PMsg × r.Chal) :: pathRounds n path.2.2

@[simp] theorem pathRounds_length [Finite r.PMsg] :
    (n : ℕ) → (path : (protocol (List.replicate n (round r))).tree.ExecutionPath) →
      (pathRounds n path).length = n
  | 0, _ => rfl
  | n + 1, path => by simp [pathRounds, pathRounds_length n path.2.2]

/-- The terminal knowledge state of an execution path is Selvage's state on the full
transcript it records. -/
theorem terminalState_selvageExtractor [Finite r.PMsg] (rbr : RbrKnowledgeSoundness r) (δ : ℝ)
    (st : Stmt r) : (n : ℕ) → (rs : List (r.PMsg × r.Chal)) →
    (path : (protocol (List.replicate n (round r))).tree.ExecutionPath) →
    (selvageExtractor rbr δ st n rs).terminalState path =
      kstateAt rbr δ st ⟨rs ++ pathRounds n path, none⟩
  | 0, rs, _ => by
      change kstateAt rbr δ st ⟨rs, none⟩ = _
      simp [pathRounds]
  | n + 1, rs, path => by
      change (selvageExtractor rbr δ st n
        (rs ++ [(⟨path.1, path.2.1⟩ : r.PMsg × r.Chal)])).terminalState path.2.2 = _
      rw [terminalState_selvageExtractor rbr δ st n _ path.2.2]
      simp [pathRounds]

/-- A Selvage witness, carried to the terminal carrier of a path (an identity cast). -/
def toTerminal [Finite r.PMsg] (rbr : RbrKnowledgeSoundness r) (δ : ℝ) (st : Stmt r) (n : ℕ)
    (rs : List (r.PMsg × r.Chal))
    (path : (protocol (List.replicate n (round r))).tree.ExecutionPath) (w : r.W) :
    ((selvageExtractor rbr δ st n rs).terminalState path).Witness :=
  cast (congrArg KnowledgeState.Witness (terminalState_selvageExtractor rbr δ st n rs path)).symm w

/-- Construction B.5 with the completed prefix `rs` explicit: walk `rest` forward, extract
backward. -/
def backward (rbr : RbrKnowledgeSoundness r) (st : Stmt r) :
    List (r.PMsg × r.Chal) → List (r.PMsg × r.Chal) → r.W → r.W
  | _, [], w => w
  | rs, x :: rest, w => rbr.extract st ⟨rs ++ [x], none⟩ (backward rbr st (rs ++ [x]) rest w)

/-- ArkLib's named backward extraction along `selvageExtractor` is Selvage's backward fold.
The right side does not mention `δ`: one extractor serves every proximity bound. -/
theorem extractWitness_selvageExtractor [Finite r.PMsg] (rbr : RbrKnowledgeSoundness r)
    (δ : ℝ) (st : Stmt r) : (n : ℕ) → (rs : List (r.PMsg × r.Chal)) →
    (path : (protocol (List.replicate n (round r))).tree.ExecutionPath) → (w : r.W) →
    (selvageExtractor rbr δ st n rs).extractWitness path (toTerminal rbr δ st n rs path w) =
      backward rbr st rs (pathRounds n path) w
  | 0, _, _, _ => rfl
  | n + 1, rs, path, w =>
      congrArg (rbr.extract st ⟨rs ++ [(⟨path.1, path.2.1⟩ : r.PMsg × r.Chal)], none⟩)
        (extractWitness_selvageExtractor rbr δ st n _ path.2.2 w)

/-- The backward fold from position `i` is Selvage's `wAt` at `i`. -/
theorem backward_take_drop_eq_wAt (rbr : RbrKnowledgeSoundness r) (st : Stmt r)
    (rounds : List (r.PMsg × r.Chal)) (w : r.W) :
    ∀ m i, rounds.length - i = m → i ≤ rounds.length →
      backward rbr st (rounds.take i) (rounds.drop i) w = wAt rbr st rounds w i
  | 0, i, hm, hi => by
      have hi' : i = rounds.length := by omega
      subst hi'
      rw [List.drop_length, wAt_of_le rbr st rounds w le_rfl]
      rfl
  | m + 1, i, hm, hi => by
      have hlt : i < rounds.length := by omega
      rw [List.drop_eq_getElem_cons hlt, wAt_of_lt rbr st rounds w hlt]
      change rbr.extract st ⟨rounds.take i ++ [rounds[i]], none⟩
          (backward rbr st (rounds.take i ++ [rounds[i]]) (rounds.drop (i + 1)) w) = _
      rw [List.take_concat_get' rounds i hlt,
        backward_take_drop_eq_wAt rbr st rounds w m (i + 1) (by omega) (by omega)]

/-- Selvage's `srExtract` reads exactly the backward fold of the final transcript. -/
theorem backward_nil_eq_wAt (rbr : RbrKnowledgeSoundness r) (st : Stmt r)
    (rounds : List (r.PMsg × r.Chal)) (w : r.W) :
    backward rbr st [] rounds w = wAt rbr st rounds w 0 := by
  simpa using backward_take_drop_eq_wAt rbr st rounds w _ 0 rfl (Nat.zero_le _)

end SelvageArkLib.StateRestoration

/-- info: 'SelvageArkLib.StateRestoration.selvageExtractor_isProverPreserving' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SelvageArkLib.StateRestoration.selvageExtractor_isProverPreserving

/-- info: 'SelvageArkLib.StateRestoration.selvageExtractor_isLocallyBounded' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SelvageArkLib.StateRestoration.selvageExtractor_isLocallyBounded

/-- info: 'SelvageArkLib.StateRestoration.extractWitness_selvageExtractor' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SelvageArkLib.StateRestoration.extractWitness_selvageExtractor
