/-
# Selvage.DagPcd — proof-carrying data over DAGs, with knowledge soundness

`AccRbrInstance` builds the accumulator CHAIN as one WARP `Reduction` (one round per link)
and `Depth.OB2_depth_composition_nonneg_proved` lifts its round-by-round knowledge soundness
to straightline state-restoration knowledge soundness. This file does the same for an
arbitrary DAG of accumulation steps: a tree, a Mina-style scan state, or any DAG with shared
nodes.

**The object.** A `Dag N` is `N` nodes numbered topologically (`pred i` lists node `i`'s
predecessors, all `< i`, without repetition). An `AccScheme` is one accumulation step in the
abstract: node `i` folds the accumulators of its predecessors together with its own local
claim `x i` at a fresh challenge `ρ`, using the prover's round message `π`; a straightline
node extractor turns a witness of the folded accumulator into a local witness and witnesses
for the input accumulators, except with probability `err a` over `ρ`, where `a` is the
node's fan-in (`AccScheme.node_sound`).

**The reduction** `dagReduction S G` has one round per node, in topological order. Its source
relation is DAG compliance (every node's local claim has a witness); its target relation is
that every SINK's accumulator has a witness. The verifier recomputes every accumulator from
the messages and challenges (`accAt`), which is the IOR resolution, exactly as
`accReduction`'s verifier recomputes the chain aggregate.

**The knowledge state is where the DAG enters.** After `m` rounds the state demands
witnesses for the local claims of the unprocessed nodes and for the accumulators of the LIVE
nodes: processed nodes that are sinks or still feed an unprocessed node (`Live`). A shared
node stays live until its last consumer folds it; at the full transcript the live set is the
sink set, which is Def 4.1's third clause. The round extractor for node `i` replaces node
`i`'s local witness and its predecessors' accumulator witnesses by the node extractor's
output and leaves everything else alone; the round-bad event then lies inside the node's bad
event (`dag_round_bad_sub`).

**What is proved.**
* `dagRbr` — `RbrKnowledgeSoundness (dagReduction S G hN)` with round error
  `S.err (G.pred i).length`.
* `dag_pcd_knowledge_sound` — straightline SR knowledge soundness of the DAG with error
  `(t + N) · ε` for any `ε ≥ max_i S.err (fanin i)`, via OB-2′ (the game-slot method).
* `dag_pcd_fs_knowledge_sound` — the same for the Fiat–Shamir compilation, via
  `fsOfRbrSound_iff_depth`.
* `linScheme` — a concrete scheme: the exact-word, shared-functional γ-fold (WHIR Constr. 5.5
  shape, Horner order), with `node_sound` proved from `card_batch_satisfying_le`, error
  `a / |F|` at fan-in `a`; and a diamond DAG on which the prover, verifier and extractor run
  under `#guard`.

**The error is per node and depth-free.** Shared predecessors are paid once (one round each),
and nothing depends on the DAG's depth: the backward extractor is straightline from the one
oracle log, so the classical PCD bounded-depth restriction (a rewinding extractor whose
running time multiplies per level) does not arise. The extraction time is `Σᵢ etᵢ`.

**Modelled assumption, stated.** All nodes draw their challenges from ONE random oracle, and
the extractor reads its log. In a deployed PCD each node's verifier runs inside the next
node's circuit and computes the hash itself; reading those in-circuit hash evaluations as
queries to the same oracle is the standard flattening of recursive FS arguments. This file
proves soundness of the flattened protocol; the flattening is not proved here.
-/
import Selvage.Rbr
import Selvage.Depth
import Selvage.FiatShamir
import Selvage.ConstrainedCode

namespace Minidregg.Selvage
namespace DagPcd

/-! ## DAGs, sinks and the live frontier -/

/-- A DAG on `N` nodes, numbered topologically. -/
structure Dag (N : ℕ) where
  /-- The predecessors of each node, in the order the node folds them. -/
  pred : Fin N → List (Fin N)
  /-- Topological numbering: every predecessor has a smaller index. -/
  topo : ∀ i, ∀ j ∈ pred i, j < i
  /-- No predecessor is listed twice. -/
  nodup : ∀ i, (pred i).Nodup

variable {N : ℕ}

/-- A sink: no node folds it. Sinks are what the final verifier is handed. -/
def IsSink (G : Dag N) (j : Fin N) : Prop := ∀ s, j ∉ G.pred s

/-- After `m` rounds, node `j` is live when it has been processed and is either a sink or
still feeds a node that has not been processed. -/
def Live (G : Dag N) (m : ℕ) (j : Fin N) : Prop :=
  (j : ℕ) < m ∧ (IsSink G j ∨ ∃ s : Fin N, m ≤ (s : ℕ) ∧ j ∈ G.pred s)

/-- The node processed in round `i` is live right after it. -/
theorem live_succ_self (G : Dag N) (i : Fin N) : Live G ((i : ℕ) + 1) i := by
  refine ⟨Nat.lt_succ_self _, ?_⟩
  by_cases h : IsSink G i
  · exact Or.inl h
  · right
    unfold IsSink at h
    push Not at h
    obtain ⟨s, hs⟩ := h
    exact ⟨s, G.topo s i hs, hs⟩

/-- A node live before round `i` and not folded by node `i` is still live after it. -/
theorem live_succ_of_not_pred (G : Dag N) (i j : Fin N) (h : Live G i j)
    (hj : j ∉ G.pred i) : Live G ((i : ℕ) + 1) j := by
  obtain ⟨hlt, hsink | ⟨s, hs, hmem⟩⟩ := h
  · exact ⟨Nat.lt_succ_of_lt hlt, Or.inl hsink⟩
  · refine ⟨Nat.lt_succ_of_lt hlt, Or.inr ⟨s, ?_, hmem⟩⟩
    rcases Nat.lt_or_ge (i : ℕ) (s : ℕ) with hlt' | hge
    · exact hlt'
    · have : s = i := Fin.ext (le_antisymm hge hs)
      subst this
      exact absurd hmem hj

/-- At the full transcript the live set is the sink set. -/
theorem live_full_iff (G : Dag N) (j : Fin N) : Live G N j ↔ IsSink G j := by
  constructor
  · rintro ⟨-, hsink | ⟨s, hs, -⟩⟩
    · exact hsink
    · exact absurd s.isLt (not_lt.mpr hs)
  · exact fun h => ⟨j.isLt, Or.inl h⟩

/-- Nothing is live before the first round. -/
theorem not_live_zero (G : Dag N) (j : Fin N) : ¬ Live G 0 j :=
  fun h => Nat.not_lt_zero _ h.1

/-! ## One accumulation step, in the abstract -/

/-- One accumulation step with a straightline node extractor and its fan-in-indexed
round error. -/
structure AccScheme where
  /-- Accumulator instances (public). -/
  Acc : Type
  /-- Accumulator witnesses. -/
  AccW : Type
  /-- Local claims, one per node (the node's compliance statement). -/
  Loc : Type
  /-- Local witnesses. -/
  LocW : Type
  /-- The prover's round message at a node. -/
  PMsg : Type
  /-- The fold challenge. -/
  Chal : Type
  [chalFintype : Fintype Chal]
  [chalInh : Inhabited Chal]
  [pmsgInh : Inhabited PMsg]
  [locWInh : Inhabited LocW]
  [accWInh : Inhabited AccW]
  AccRel : Acc → AccW → Prop
  LocRel : Loc → LocW → Prop
  /-- The node's accumulation verifier: fold the input accumulators and the local claim. -/
  fold : List Acc → Loc → PMsg → Chal → Acc
  /-- Node extractor, local half. -/
  extLoc : List Acc → Loc → PMsg → Chal → AccW → LocW
  /-- Node extractor, input half: the witness for the `k`-th input accumulator. -/
  extIn : List Acc → Loc → PMsg → Chal → AccW → ℕ → AccW
  /-- Round error at fan-in `a` (rational, so a concrete scheme stays computable). -/
  err : ℕ → ℚ
  /-- The node bound: over a uniform challenge, the chance that SOME witness of the folded
  accumulator exists while the node extractor's output fails the local claim or an input
  accumulator is at most `err (fan-in)`. -/
  node_sound : ∀ (ins : List Acc) (x : Loc) (π : PMsg),
    uniformProb Chal (fun ρ => ∃ wa : AccW, AccRel (fold ins x π ρ) wa ∧
      ¬ (LocRel x (extLoc ins x π ρ wa) ∧
         ∀ k (hk : k < ins.length), AccRel ins[k] (extIn ins x π ρ wa k)))
      ≤ (err ins.length : ℝ)

attribute [instance] AccScheme.chalFintype AccScheme.chalInh AccScheme.pmsgInh
  AccScheme.locWInh AccScheme.accWInh

variable (S : AccScheme) (G : Dag N)

/-! ## The accumulators a transcript determines -/

/-- The accumulator of node `i` under local claims `x` and transcript rounds `rs`: node
`i` folds its predecessors' accumulators with its own round's message and challenge. -/
def accAt (x : Fin N → S.Loc) (rs : List (S.PMsg × S.Chal)) (i : Fin N) : S.Acc :=
  S.fold ((G.pred i).attach.map fun j => accAt x rs j.1) (x i)
    (rs.getD i default).1 (rs.getD i default).2
termination_by (i : ℕ)
decreasing_by exact G.topo i j.1 j.2

theorem accAt_eq (x : Fin N → S.Loc) (rs : List (S.PMsg × S.Chal)) (i : Fin N) :
    accAt S G x rs i = S.fold ((G.pred i).map (accAt S G x rs)) (x i)
      (rs.getD i default).1 (rs.getD i default).2 := by
  rw [accAt]
  congr 1
  conv_rhs => rw [← List.attach_map_subtype_val (G.pred i)]
  rw [List.map_map]
  rfl

/-- A node's accumulator depends only on the transcript up to and including its round. -/
theorem accAt_append (x : Fin N → S.Loc) (rs e : List (S.PMsg × S.Chal)) :
    ∀ (n : ℕ) (i : Fin N), (i : ℕ) = n → (i : ℕ) < rs.length →
      accAt S G x (rs ++ e) i = accAt S G x rs i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hlt
    rw [accAt_eq, accAt_eq]
    have hmap : (G.pred i).map (accAt S G x (rs ++ e)) = (G.pred i).map (accAt S G x rs) := by
      apply List.map_congr_left
      intro j hj
      have hji : (j : ℕ) < i := G.topo i j hj
      exact ih j (hi ▸ hji) j rfl (lt_trans hji hlt)
    rw [hmap]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]

theorem accAt_append' (x : Fin N → S.Loc) (rs e : List (S.PMsg × S.Chal)) (i : Fin N)
    (hlt : (i : ℕ) < rs.length) : accAt S G x (rs ++ e) i = accAt S G x rs i :=
  accAt_append S G x rs e i i rfl hlt

/-- The accumulator of the node processed in round `rs.length`. -/
theorem accAt_snoc_self (x : Fin N → S.Loc) (rs : List (S.PMsg × S.Chal)) (i : Fin N)
    (hlen : rs.length = i) (π : S.PMsg) (ρ : S.Chal) :
    accAt S G x (rs ++ [(π, ρ)]) i =
      S.fold ((G.pred i).map (accAt S G x rs)) (x i) π ρ := by
  rw [accAt_eq]
  have hmap : (G.pred i).map (accAt S G x (rs ++ [(π, ρ)])) =
      (G.pred i).map (accAt S G x rs) := by
    apply List.map_congr_left
    intro j hj
    exact accAt_append' S G x rs _ j (hlen ▸ G.topo i j hj)
  have hget : (rs ++ [(π, ρ)]).getD i default = (π, ρ) := by
    rw [← hlen]; simp
  rw [hmap, hget]

/-! ## The reduction -/

/-- The whole DAG as one WARP reduction: one round per node, in topological order.
Source relation: DAG compliance (every local claim has a witness). Target relation: every
sink's accumulator has a witness. The implicit-instance words are `Unit`, so the
δ-relaxation is inert and all slack lives in the scheme. -/
@[reducible] def dagReduction (hN : 0 < N) : Reduction where
  Idx := Unit
  X := Fin N → S.Loc
  A := Unit
  X' := Fin N → S.Acc
  A' := Unit
  W := (Fin N → S.LocW) × (Fin N → S.AccW)
  n := 1
  n' := 1
  n_pos := one_pos
  n'_pos := one_pos
  R := fun _ x _ w => ∀ j, S.LocRel (x j) (w.1 j)
  R' := fun _ accs _ w => ∀ j, IsSink G j → S.AccRel (accs j) (w.2 j)
  k := N
  k_pos := hN
  PMsg := S.PMsg
  Chal := S.Chal
  pmsgNonempty := ⟨default⟩
  chalFintype := S.chalFintype
  chalNonempty := ⟨default⟩
  δstar := 1
  δstar_pos := one_pos
  δstar_le_one := le_rfl
  verify := fun _ x _ πs ρs =>
    some (accAt S G x (List.ofFn fun i => (πs i, ρs i)), fun _ => ())

/-- The knowledge-state proposition after the rounds `rs`: the unprocessed nodes' local
claims and the live nodes' accumulators are witnessed. -/
def StateProp (x : Fin N → S.Loc) (rs : List (S.PMsg × S.Chal))
    (w : (Fin N → S.LocW) × (Fin N → S.AccW)) : Prop :=
  (∀ j : Fin N, rs.length ≤ (j : ℕ) → S.LocRel (x j) (w.1 j)) ∧
  (∀ j : Fin N, Live G rs.length j → S.AccRel (accAt S G x rs j) (w.2 j))

open Classical in
/-- The knowledge-state bit. -/
noncomputable def dagState (x : Fin N → S.Loc) (rs : List (S.PMsg × S.Chal))
    (w : (Fin N → S.LocW) × (Fin N → S.AccW)) : Bool :=
  decide (StateProp S G x rs w)

open Classical in
theorem dagState_eq_true (x : Fin N → S.Loc) (rs : List (S.PMsg × S.Chal))
    (w : (Fin N → S.LocW) × (Fin N → S.AccW)) :
    dagState S G x rs w = true ↔ StateProp S G x rs w := by
  unfold dagState; exact decide_eq_true_iff

open Classical in
theorem dagState_eq_false (x : Fin N → S.Loc) (rs : List (S.PMsg × S.Chal))
    (w : (Fin N → S.LocW) × (Fin N → S.AccW)) :
    dagState S G x rs w = false ↔ ¬ StateProp S G x rs w := by
  unfold dagState; exact decide_eq_false_iff_not

/-- Def 4.1 for the DAG. Pending-blind, so `prover_monotone` is immediate. -/
noncomputable def dagKState (hN : 0 < N) : KStateFn (dagReduction S G hN) where
  state := fun _ st tr w => dagState S G st.x tr.rounds w
  empty_iff := by
    intro δ hδ st w
    show dagState S G st.x [] w = true ↔ _
    rw [dagState_eq_true]
    simp only [StateProp, List.length_nil]
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨st.y, fun j => h1 j (Nat.zero_le _), by rw [fracHamming_self]; exact le_of_lt hδ.1⟩
    · rintro ⟨_, hR, -⟩
      exact ⟨fun j _ => hR j, fun j hj => absurd hj (not_live_zero G j)⟩
  prover_monotone := by
    intro δ _ st rs w _ h π
    exact h
  full_iff := by
    intro δ hδ st πs ρs w
    show dagState S G st.x (List.ofFn fun i => (πs i, ρs i)) w = true ↔ _
    rw [dagState_eq_true]
    simp only [StateProp, List.length_ofFn]
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨_, fun _ => (), rfl, fun _ => (), ?_, by rw [fracHamming_self]; exact le_of_lt hδ.1⟩
      intro j hj
      exact h2 j ((live_full_iff G j).mpr hj)
    · rintro ⟨x', y', hv, _, hR, -⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, -⟩ := hv
      refine ⟨fun j hj => absurd j.isLt (not_lt.mpr hj), ?_⟩
      intro j hj
      exact hR j ((live_full_iff G j).mp hj)

/-! ## The round extractor -/

/-- The round extractor, on a transcript ending with node `i`'s round `(π, ρ)`: node `i`'s
local witness and its predecessors' accumulator witnesses come from the node extractor,
everything else is kept. Computable. -/
def dagExtract (x : Fin N → S.Loc) (rs : List (S.PMsg × S.Chal))
    (w : (Fin N → S.LocW) × (Fin N → S.AccW)) : (Fin N → S.LocW) × (Fin N → S.AccW) :=
  match rs.getLast? with
  | none => w
  | some (π, ρ) =>
    if h : rs.length - 1 < N then
      let i : Fin N := ⟨rs.length - 1, h⟩
      let ins := (G.pred i).map (accAt S G x rs)
      (Function.update w.1 i (S.extLoc ins (x i) π ρ (w.2 i)),
       fun j => if j ∈ G.pred i then S.extIn ins (x i) π ρ (w.2 i) ((G.pred i).idxOf j)
         else w.2 j)
    else w

theorem dagExtract_snoc (x : Fin N → S.Loc) (rs : List (S.PMsg × S.Chal)) (i : Fin N)
    (hlen : rs.length = i) (π : S.PMsg) (ρ : S.Chal)
    (w : (Fin N → S.LocW) × (Fin N → S.AccW)) :
    dagExtract S G x (rs ++ [(π, ρ)]) w =
      let ins := (G.pred i).map (accAt S G x rs)
      (Function.update w.1 i (S.extLoc ins (x i) π ρ (w.2 i)),
       fun j => if j ∈ G.pred i then S.extIn ins (x i) π ρ (w.2 i) ((G.pred i).idxOf j)
         else w.2 j) := by
  have hi : (rs ++ [(π, ρ)]).length - 1 = i := by simp [hlen]
  have hlt : (rs ++ [(π, ρ)]).length - 1 < N := hi ▸ i.isLt
  have hfin : (⟨(rs ++ [(π, ρ)]).length - 1, hlt⟩ : Fin N) = i := Fin.ext hi
  have hmap : (G.pred i).map (accAt S G x (rs ++ [(π, ρ)])) =
      (G.pred i).map (accAt S G x rs) := by
    apply List.map_congr_left
    intro j hj
    exact accAt_append' S G x rs _ j (hlen ▸ G.topo i j hj)
  unfold dagExtract
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
  simp only [hlt, ↓reduceDIte]
  simp only [hfin, hmap]

/-- **The DAG's round-bad event lies inside the node's bad event.** If some witness `w`
is valid after node `i`'s round while the round extractor's output is invalid before it,
then `w`'s accumulator witness for node `i` is a witness of the folded accumulator on which
the node extractor fails. -/
theorem dag_round_bad_sub (x : Fin N → S.Loc) (i : Fin N) (rs : List (S.PMsg × S.Chal))
    (hlen : rs.length = i) (π : S.PMsg) (ρ : S.Chal)
    (w : (Fin N → S.LocW) × (Fin N → S.AccW))
    (hpost : StateProp S G x (rs ++ [(π, ρ)]) w)
    (hpre : ¬ StateProp S G x rs (dagExtract S G x (rs ++ [(π, ρ)]) w)) :
    S.AccRel (S.fold ((G.pred i).map (accAt S G x rs)) (x i) π ρ) (w.2 i) ∧
      ¬ (S.LocRel (x i) (S.extLoc ((G.pred i).map (accAt S G x rs)) (x i) π ρ (w.2 i)) ∧
         ∀ k (hk : k < ((G.pred i).map (accAt S G x rs)).length),
           S.AccRel ((G.pred i).map (accAt S G x rs))[k]
             (S.extIn ((G.pred i).map (accAt S G x rs)) (x i) π ρ (w.2 i) k)) := by
  have hlen' : (rs ++ [(π, ρ)]).length = (i : ℕ) + 1 := by simp [hlen]
  refine ⟨?_, ?_⟩
  · have h := hpost.2 i (by rw [hlen']; exact live_succ_self G i)
    rwa [accAt_snoc_self S G x rs i hlen π ρ] at h
  · rintro ⟨hloc, hins⟩
    apply hpre
    rw [dagExtract_snoc S G x rs i hlen π ρ w]
    refine ⟨?_, ?_⟩
    · intro j hj
      by_cases hji : j = i
      · subst hji
        simpa using hloc
      · have hgt : (i : ℕ) + 1 ≤ j := by
          rw [hlen] at hj
          exact Nat.succ_le_of_lt (lt_of_le_of_ne hj (fun h => hji (Fin.ext h.symm)))
        simp only [Function.update_of_ne hji]
        exact hpost.1 j (hlen' ▸ hgt)
    · intro j hlive
      simp only
      split_ifs with hmem
      · have hk : (G.pred i).idxOf j < ((G.pred i).map (accAt S G x rs)).length := by
          rw [List.length_map]; exact List.idxOf_lt_length_of_mem hmem
        have h := hins _ hk
        have hget : ((G.pred i).map (accAt S G x rs))[(G.pred i).idxOf j] = accAt S G x rs j := by
          rw [List.getElem_map, List.getElem_idxOf]
        rwa [hget] at h
      · rw [hlen] at hlive
        have h := hpost.2 j (by rw [hlen']; exact live_succ_of_not_pred G i j hlive hmem)
        rwa [accAt_append' S G x rs _ j (hlen ▸ hlive.1)] at h

/-! ## Round-by-round knowledge soundness of the DAG -/

open Classical in
/-- **Def 4.2 for the DAG**, with round error the node scheme's error at that node's
fan-in. -/
noncomputable def dagRbr (hN : 0 < N) : RbrKnowledgeSoundness (dagReduction S G hN) where
  kstate := dagKState S G hN
  extract := fun st tr w => dagExtract S G st.x tr.rounds w
  err := fun i _ _ => (S.err (G.pred i).length : ℝ)
  extractTime := fun _ => 1
  extract_sound := by
    intro δ _ st i rs hlen π
    have hnode := S.node_sound ((G.pred i).map (accAt S G st.x rs)) (st.x i) π
    refine le_trans (uniformProb_mono ?_) (le_trans hnode (le_of_eq (by rw [List.length_map])))
    rintro ρ ⟨w, hpre, hpost⟩
    have hpre' : dagState S G st.x rs (dagExtract S G st.x (rs ++ [(π, ρ)]) w) = false := hpre
    have hpost' : dagState S G st.x (rs ++ [(π, ρ)]) w = true := hpost
    rw [dagState_eq_false] at hpre'
    rw [dagState_eq_true] at hpost'
    refine ⟨w.2 i, ?_⟩
    exact dag_round_bad_sub S G st.x i rs hlen π ρ w hpost' hpre'

/-! ## Headlines -/

/-- **DAG PCD knowledge soundness** (state-restoration, straightline). For every DAG `G` of
`N ≥ 1` accumulation steps of scheme `S`, every bound `ε ≥ 0` on the node errors at the
DAG's fan-ins, and every statement set `Z`: there is ONE straightline extractor such that
every `t`-query state-restoration prover makes the verifier accept with a valid witness for
every sink accumulator while the extracted witnesses fail some node's local claim with
probability at most `(t + N) · ε`. Proved by the game-slot method: `dagRbr` fed to OB-2′. -/
theorem dag_pcd_knowledge_sound (hN : 0 < N) (Z : Set (Stmt (dagReduction S G hN)))
    (ε : ℝ) (hε : 0 ≤ ε) (hdom : ∀ i : Fin N, (S.err (G.pred i).length : ℝ) ≤ ε) :
    StraightlineSrKnowledgeSoundness (dagReduction S G hN) Z
      (fun _ t _ => ((t : ℝ) + (N : ℝ)) * ε) :=
  OB2_depth_composition_nonneg_proved (dagReduction S G hN) (dagRbr S G hN) Z (fun _ => ε)
    (fun _ _ => hε) (fun i _ _ _ _ => hdom i)

/-- **DAG PCD knowledge soundness of the Fiat–Shamir compilation**, same bound. -/
theorem dag_pcd_fs_knowledge_sound (hN : 0 < N) (Z : Set (Stmt (dagReduction S G hN)))
    (ε : ℝ) (hε : 0 ≤ ε) (hdom : ∀ i : Fin N, (S.err (G.pred i).length : ℝ) ≤ ε) :
    FsStraightlineKnowledgeSoundness (dagReduction S G hN) Z
      (fun _ t _ => ((t : ℝ) + (N : ℝ)) * ε) :=
  (fsOfRbrSound_iff_depth.mpr OB2_depth_composition_nonneg_proved) (dagReduction S G hN)
    (dagRbr S G hN) Z (fun _ => ε) (fun _ _ => hε) (fun i _ _ _ _ => hdom i)

/-! ## A concrete scheme: the shared-functional γ-fold

Claims are pairs `(σ, f)` read "`⟨φ, f⟩ = σ`" for one public functional `φ`. A node folds
its input accumulators and its local claim, in Horner order, at the challenge `ρ`; the local
claim's word is the node's round message. This is WHIR Construction 5.5's same-functional
batch at exact-word resolution (`C = ⊤`). The node error at fan-in `a` is `a / |F|`: the fold
of `a + 1` claims passes with some claim false only at a root of the nonzero defect
polynomial, of degree at most `a` (`card_batch_satisfying_le`, reused). -/

section LinScheme

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Folded target, Horner order. -/
def foldT (ρ : F) : List (F × (ι → F)) → F
  | [] => 0
  | c :: cs => c.1 + ρ * foldT ρ cs

/-- Folded word, Horner order. -/
def foldW (ρ : F) : List (F × (ι → F)) → (ι → F)
  | [] => 0
  | c :: cs => c.2 + ρ • foldW ρ cs

/-- Each claim's defect `⟨φ, f⟩ - σ`, as a one-coordinate constraint with target `0`. -/
def defects (φ : ι → F) (cs : List (F × (ι → F))) : List (LinearConstraint Unit F) :=
  cs.map fun c => ⟨fun _ => dotWt φ c.2 - c.1, 0⟩

omit [Fintype F] [DecidableEq F] [DecidableEq ι] in
theorem defects_batch_iff (φ : ι → F) (ρ : F) (cs : List (F × (ι → F))) :
    Satisfies (fun _ : Unit => (1 : F)) (batchConstraint ρ (defects φ cs)) ↔
      dotWt φ (foldW ρ cs) = foldT ρ cs := by
  have hwt : ∀ cs : List (F × (ι → F)),
      batchWt ρ (defects φ cs) () = dotWt φ (foldW ρ cs) - foldT ρ cs ∧
      batchTarget ρ (defects φ cs) = 0 := by
    intro cs
    induction cs with
    | nil => simp [defects, batchWt, batchTarget, foldW, foldT, dotWt]
    | cons c cs ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩
      · simp only [defects, List.map_cons, batchWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          foldW, foldT] at ih1 ⊢
        rw [ih1]
        simp only [dotWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib]
        rw [show (∑ i, φ i * (ρ * foldW ρ cs i)) = ρ * ∑ i, φ i * foldW ρ cs i by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
        ring
      · simp only [defects, List.map_cons, batchTarget] at ih2 ⊢
        rw [ih2]; ring
  obtain ⟨h1, h2⟩ := hwt cs
  unfold Satisfies batchConstraint
  simp only [dotWt, Finset.univ_unique, Finset.sum_singleton, mul_one]
  rw [show (default : Unit) = () from rfl, h1, h2, sub_eq_zero]
  exact Iff.rfl

omit [Fintype F] [DecidableEq F] [DecidableEq ι] in
theorem defects_violated_iff (φ : ι → F) (cs : List (F × (ι → F))) :
    (∃ c ∈ defects φ cs, ¬ Satisfies (fun _ : Unit => (1 : F)) c) ↔
      ∃ c ∈ cs, dotWt φ c.2 ≠ c.1 := by
  simp only [defects, List.mem_map, Satisfies, dotWt, Finset.univ_unique,
    Finset.sum_singleton, mul_one]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, h⟩
    exact ⟨c, hc, fun he => h (by simp [he])⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨_, ⟨c, hc, rfl⟩, fun he => h (sub_eq_zero.mp (by simpa using he))⟩

/-- The shared-functional γ-fold as an `AccScheme`. Accumulators are public claims
`(σ, f)`; the knowledge sits in the local witnesses, which the node extractor reads off the
round message. -/
def linScheme (φ : ι → F) : AccScheme where
  Acc := F × (ι → F)
  AccW := Unit
  Loc := F
  LocW := ι → F
  PMsg := ι → F
  Chal := F
  chalInh := ⟨0⟩
  pmsgInh := ⟨0⟩
  locWInh := ⟨0⟩
  accWInh := ⟨()⟩
  AccRel := fun a _ => dotWt φ a.2 = a.1
  LocRel := fun τ g => dotWt φ g = τ
  fold := fun ins τ g ρ => (foldT ρ (ins ++ [(τ, g)]), foldW ρ (ins ++ [(τ, g)]))
  extLoc := fun _ _ g _ _ => g
  extIn := fun _ _ _ _ _ _ => ()
  err := fun a => (a : ℚ) / (Fintype.card F : ℚ)
  node_sound := by
    intro ins τ g
    classical
    set cs := ins ++ [(τ, g)] with hcs
    by_cases hv : ∃ c ∈ cs, dotWt φ c.2 ≠ c.1
    · have hcard := card_batch_satisfying_le (f := fun _ : Unit => (1 : F))
        ((defects_violated_iff φ cs).mpr hv)
      have hlen : (defects φ cs).length - 1 = ins.length := by
        simp [defects, hcs]
      rw [hlen] at hcard
      unfold uniformProb
      push_cast
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      calc (Nat.card {ρ : F // _} : ℝ)
          ≤ (Nat.card {ρ : F // Satisfies (fun _ : Unit => (1 : F))
              (batchConstraint ρ (defects φ cs))} : ℝ) := by
            apply card_mono_of_imp
            rintro ρ ⟨_, hacc, -⟩
            exact (defects_batch_iff φ ρ cs).mpr hacc
        _ = ((Finset.univ.filter fun ρ : F => Satisfies (fun _ : Unit => (1 : F))
              (batchConstraint ρ (defects φ cs))).card : ℝ) := by
            rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        _ ≤ (ins.length : ℝ) := by exact_mod_cast hcard
    · push Not at hv
      rw [uniformProb_false]
      · push_cast; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · rintro ρ ⟨_, -, hfail⟩
        apply hfail
        refine ⟨hv (τ, g) (by simp [hcs]), ?_⟩
        intro k hk
        exact hv ins[k] (by simp [hcs, List.getElem_mem])

omit [DecidableEq ι] in
/-- The fan-in-`a` node error of `linScheme` is `a / |F|`, by definition. -/
theorem linScheme_err (φ : ι → F) (a : ℕ) :
    ((linScheme φ).err a : ℝ) = (a : ℝ) / (Fintype.card F : ℝ) := by
  simp [linScheme]

omit [DecidableEq ι] in
/-- **DAG PCD for the shared-functional fold.** Every DAG whose fan-ins are at most `amax`
has straightline SR knowledge error `(t + N) · amax / |F|`. -/
theorem lin_dag_pcd_knowledge_sound (φ : ι → F) (G : Dag N) (hN : 0 < N) (amax : ℕ)
    (hfan : ∀ i, (G.pred i).length ≤ amax)
    (Z : Set (Stmt (dagReduction (linScheme φ) G hN))) :
    StraightlineSrKnowledgeSoundness (dagReduction (linScheme φ) G hN) Z
      (fun _ t _ => ((t : ℝ) + (N : ℝ)) * ((amax : ℝ) / (Fintype.card F : ℝ))) :=
  dag_pcd_knowledge_sound (linScheme φ) G hN Z _
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun i => by
      rw [linScheme_err]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hfan i) (Nat.cast_nonneg _))

end LinScheme

/-! ## Executable consumer: a diamond with a shared node, over `ZMod 7`

Node 0 is a leaf feeding nodes 1 and 2 (shared); node 3 folds 1 and 2 and is the only
sink. Local claims are `⟨φ, g⟩ = τ` with `φ = (1, 2)`. -/

section Diamond

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The diamond `0 → 1, 0 → 2, {1, 2} → 3`. -/
def diamond : Dag 4 where
  pred := ![[], [0], [0], [1, 2]]
  topo := by decide
  nodup := by decide

theorem diamond_sinks (j : Fin 4) : IsSink diamond j ↔ j = 3 := by
  unfold IsSink; revert j; decide

/-- Node 0 is shared: it is folded by two nodes, so it is live after round 1 and after
round 2, and dead after round 3. -/
theorem diamond_shared_live : Live diamond 2 0 ∧ ¬ Live diamond 3 0 := by
  unfold Live IsSink; decide

/-- The public functional. -/
def φ7 : Fin 2 → ZMod 7 := ![1, 2]

/-- Honest local words and targets. -/
def gs : Fin 4 → Fin 2 → ZMod 7 := ![![1, 1], ![2, 0], ![0, 3], ![4, 5]]
def τs : Fin 4 → ZMod 7 := fun i => dotWt φ7 (gs i)

/-- A cheating prover: node 1's local word misses its claim. -/
def gsBad : Fin 4 → Fin 2 → ZMod 7 := Function.update gs 1 ![3, 0]

/-- The transcript of the prover with words `g` under challenges `ρs`. -/
def runT (g : Fin 4 → Fin 2 → ZMod 7) (ρs : Fin 4 → ZMod 7) : List ((Fin 2 → ZMod 7) × ZMod 7) :=
  List.ofFn fun i => (g i, ρs i)

/-- The verifier's verdict on the sink: recompute the accumulators, check the sink claim. -/
def sinkAccepts (g : Fin 4 → Fin 2 → ZMod 7) (ρs : Fin 4 → ZMod 7) : Bool :=
  let acc := accAt (linScheme φ7) diamond τs (runT g ρs) 3
  decide (dotWt φ7 acc.2 = acc.1)

/-- All `7⁴` challenge vectors. -/
def allChal : List (Fin 4 → ZMod 7) :=
  (List.finRange 7).flatMap fun a => (List.finRange 7).flatMap fun b =>
    (List.finRange 7).flatMap fun c => (List.finRange 7).map fun d =>
      ![(a : ZMod 7), (b : ZMod 7), (c : ZMod 7), (d : ZMod 7)]

/-- The backward extraction (Construction B.5 over `dagExtract`): from the full transcript
down to the empty one. -/
def backward (x : Fin 4 → ZMod 7) (rs : List ((Fin 2 → ZMod 7) × ZMod 7)) :
    ℕ → ((Fin 4 → Fin 2 → ZMod 7) × (Fin 4 → Unit)) →
      ((Fin 4 → Fin 2 → ZMod 7) × (Fin 4 → Unit))
  | 0, w => w
  | m + 1, w => backward x rs m (dagExtract (linScheme φ7) diamond x (rs.take (m + 1)) w)

-- Completeness: the honest prover is accepted at every one of the 2401 challenge vectors.
#guard allChal.length = 2401
#guard allChal.all (sinkAccepts gs)
-- The cheating prover is accepted at exactly 343 = 2401 / 7 vectors: those with ρ₁ = 0,
-- where node 1's defect is multiplied away. That is node 1's fan-in-1 error 1/7, attained.
#guard (allChal.filter (sinkAccepts gsBad)).length = 343
#guard (allChal.filter (sinkAccepts gsBad)).all fun ρs => ρs 1 = 0
-- The straightline extractor recovers every node's local word from the honest transcript,
-- starting from an arbitrary candidate.
#guard (List.finRange 4).all fun j =>
  (List.finRange 2).all fun k =>
    (backward τs (runT gs ![3, 1, 4, 1]) 4 (fun _ => 0, fun _ => ())).1 j k = gs j k
-- On the cheating transcript it recovers the cheating word, which fails node 1's claim:
-- the extraction failure is the event the theorem bounds.
#guard decide ((backward τs (runT gsBad ![3, 0, 4, 1]) 4 (fun _ => 0, fun _ => ())).1 1 = ![3, 0])
#guard decide (dotWt φ7 (gsBad 1) ≠ τs 1)

/-- The headline, instantiated on the diamond: error `(t + 4) · 2/7`. -/
theorem diamond_pcd_knowledge_sound (Z : Set (Stmt (dagReduction (linScheme φ7) diamond
    (by norm_num)))) :
    StraightlineSrKnowledgeSoundness (dagReduction (linScheme φ7) diamond (by norm_num)) Z
      (fun _ t _ => ((t : ℝ) + 4) * ((2 : ℝ) / 7)) := by
  have h := lin_dag_pcd_knowledge_sound φ7 diamond (by norm_num) 2
    (by intro i; fin_cases i <;> decide) Z
  simpa [ZMod.card] using h

end Diamond

/-! ## Shapes: chain, tree, Mina scan state

All three aggregate `L` leaf steps. The tree uses queue-merge numbering (leaves `0..L-1`,
internal node `L + k` folds nodes `2k` and `2k+1`), which is a topological order for every
`L ≥ 1` and is the merge order of Mina's scan state. The scan state over `T` blocks of `B`
leaves is that tree per block plus a ledger chain: the block-`b` ledger node folds the
previous ledger node and block `b`'s tree root. -/

/-- The chain: node `i` folds node `i - 1`. -/
def chainDag (L : ℕ) : Dag L where
  pred := fun i => if h : (i : ℕ) = 0 then [] else [⟨i - 1, by omega⟩]
  topo := by
    intro i j hj
    split_ifs at hj with h
    · simp at hj
    · simp at hj; subst hj; show (i : ℕ) - 1 < i; omega
  nodup := by intro i; split_ifs <;> simp

/-- The queue-merge binary tree over `L` leaves (`2L - 1` nodes). -/
def treeDag (L : ℕ) : Dag (2 * L - 1) where
  pred := fun m => if h : (m : ℕ) < L then [] else
    [⟨2 * ((m : ℕ) - L), by omega⟩, ⟨2 * ((m : ℕ) - L) + 1, by omega⟩]
  topo := by
    intro m j hj
    split_ifs at hj with h
    · simp at hj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have hm := m.isLt
      rcases hj with rfl | rfl
      · show 2 * ((m : ℕ) - L) < m; omega
      · show 2 * ((m : ℕ) - L) + 1 < m; omega
  nodup := by
    intro m; split_ifs
    · simp
    · simp [Fin.ext_iff]

/-- Fan-in of every node of the tree is at most 2; of the chain, at most 1. -/
theorem treeDag_fanin (L : ℕ) (m : Fin (2 * L - 1)) : ((treeDag L).pred m).length ≤ 2 := by
  unfold treeDag; dsimp only; split_ifs <;> simp

theorem chainDag_fanin (L : ℕ) (i : Fin L) : ((chainDag L).pred i).length ≤ 1 := by
  unfold chainDag; dsimp only; split_ifs <;> simp

/-- The edge count: total fan-in, i.e. the number of child-verifier copies a recursive
prover pays for. -/
def Dag.edges (G : Dag N) : ℕ := ∑ i : Fin N, (G.pred i).length

/-- The longest path ending at node `i`, counted in nodes. -/
def Dag.depthAt (G : Dag N) (i : Fin N) : ℕ :=
  ((G.pred i).attach.map fun j => G.depthAt j.1).foldr max 0 + 1
termination_by (i : ℕ)
decreasing_by exact G.topo i j.1 j.2

/-- The depth: the longest path, in nodes (the sequential latency of proving). -/
def Dag.depth (G : Dag N) : ℕ := (List.finRange N).foldr (fun i m => max (G.depthAt i) m) 0

theorem scan_divmod (m B : ℕ) (hB : 0 < B) :
    m / (2 * B - 1) * (2 * B - 1) + m % (2 * B - 1) = m ∧ m % (2 * B - 1) < 2 * B - 1 :=
  ⟨by rw [mul_comm]; exact Nat.div_add_mod m _, Nat.mod_lt _ (by omega)⟩

theorem scan_root_lt (T B b : ℕ) (hB : 0 < B) (hb : b < T) :
    b * (2 * B - 1) + (2 * B - 1 - 1) < T * (2 * B - 1) := by
  have h := Nat.mul_le_mul_right (2 * B - 1) (Nat.succ_le_of_lt hb)
  rw [Nat.succ_mul] at h
  omega

/-- Mina's scan state: `T` blocks of `B` leaves. Block `b`'s tree occupies nodes
`b(2B-1) .. b(2B-1) + 2B - 2` in queue-merge order, its root last; ledger node `b` sits at
`T(2B-1) + b` and folds the previous ledger node and block `b`'s root. -/
def scanDag (T B : ℕ) (hB : 0 < B) : Dag (T * (2 * B - 1) + T) where
  pred := fun m =>
    if h : (m : ℕ) < T * (2 * B - 1) then
      if hr : (m : ℕ) % (2 * B - 1) < B then [] else
        [⟨(m : ℕ) / (2 * B - 1) * (2 * B - 1) + 2 * ((m : ℕ) % (2 * B - 1) - B), by
            have := scan_divmod (m : ℕ) B hB; omega⟩,
         ⟨(m : ℕ) / (2 * B - 1) * (2 * B - 1) + 2 * ((m : ℕ) % (2 * B - 1) - B) + 1, by
            have := scan_divmod (m : ℕ) B hB; omega⟩]
    else
      if hb0 : (m : ℕ) - T * (2 * B - 1) = 0 then
        [⟨((m : ℕ) - T * (2 * B - 1)) * (2 * B - 1) + (2 * B - 1 - 1), by
          have := scan_root_lt T B ((m : ℕ) - T * (2 * B - 1)) hB (by omega); omega⟩]
      else
        [⟨(m : ℕ) - 1, by omega⟩,
         ⟨((m : ℕ) - T * (2 * B - 1)) * (2 * B - 1) + (2 * B - 1 - 1), by
          have := scan_root_lt T B ((m : ℕ) - T * (2 * B - 1)) hB (by omega); omega⟩]
  topo := by
    intro m j hj
    have hm := m.isLt
    split_ifs at hj with h1 h2 h3
    · simp at hj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have := scan_divmod (m : ℕ) B hB
      rcases hj with rfl | rfl
      · show (m : ℕ) / (2 * B - 1) * (2 * B - 1) + 2 * ((m : ℕ) % (2 * B - 1) - B) < m
        omega
      · show (m : ℕ) / (2 * B - 1) * (2 * B - 1) + 2 * ((m : ℕ) % (2 * B - 1) - B) + 1 < m
        omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      have := scan_root_lt T B ((m : ℕ) - T * (2 * B - 1)) hB (by omega)
      show ((m : ℕ) - T * (2 * B - 1)) * (2 * B - 1) + (2 * B - 1 - 1) < m
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have := scan_root_lt T B ((m : ℕ) - T * (2 * B - 1)) hB (by omega)
      rcases hj with rfl | rfl
      · show (m : ℕ) - 1 < m; omega
      · show ((m : ℕ) - T * (2 * B - 1)) * (2 * B - 1) + (2 * B - 1 - 1) < m
        omega
  nodup := by
    intro m
    have hm := m.isLt
    split_ifs with h1 h2 h3
    · simp
    · simp [Fin.ext_iff]
    · simp
    · have := scan_root_lt T B ((m : ℕ) - T * (2 * B - 1)) hB (by omega)
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true,
        List.nodup_nil, and_true, Fin.ext_iff]
      omega

theorem scanDag_fanin (T B : ℕ) (hB : 0 < B) (m : Fin (T * (2 * B - 1) + T)) :
    ((scanDag T B hB).pred m).length ≤ 2 := by
  unfold scanDag; dsimp only; split_ifs <;> simp

/-! ### The three shapes priced by the theorem

For `L` leaf steps over a field `F` and a `t`-query adversary: the chain pays
`(t + L) · 1/|F|`, the tree `(t + 2L - 1) · 2/|F|`, the scan state over `T` blocks of `B`
`(t + T(2B - 1) + T) · 2/|F|`. Depth never enters. Against `t ≫ L` the tree and the scan
state cost one bit over the chain, for the fan-in, and nothing for the depth. -/

theorem chain_pcd_knowledge_sound {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] (φ : ι → F) (L : ℕ) (hL : 0 < L)
    (Z : Set (Stmt (dagReduction (linScheme φ) (chainDag L) hL))) :
    StraightlineSrKnowledgeSoundness (dagReduction (linScheme φ) (chainDag L) hL) Z
      (fun _ t _ => ((t : ℝ) + (L : ℝ)) * ((1 : ℝ) / (Fintype.card F : ℝ))) := by
  simpa using lin_dag_pcd_knowledge_sound φ (chainDag L) hL 1 (chainDag_fanin L) Z

theorem tree_pcd_knowledge_sound {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] (φ : ι → F) (L : ℕ) (hL : 0 < 2 * L - 1)
    (Z : Set (Stmt (dagReduction (linScheme φ) (treeDag L) hL))) :
    StraightlineSrKnowledgeSoundness (dagReduction (linScheme φ) (treeDag L) hL) Z
      (fun _ t _ => ((t : ℝ) + ((2 * L - 1 : ℕ) : ℝ)) * ((2 : ℝ) / (Fintype.card F : ℝ))) := by
  simpa using lin_dag_pcd_knowledge_sound φ (treeDag L) hL 2 (treeDag_fanin L) Z

theorem scan_pcd_knowledge_sound {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] (φ : ι → F) (T B : ℕ) (hB : 0 < B)
    (hN : 0 < T * (2 * B - 1) + T)
    (Z : Set (Stmt (dagReduction (linScheme φ) (scanDag T B hB) hN))) :
    StraightlineSrKnowledgeSoundness (dagReduction (linScheme φ) (scanDag T B hB) hN) Z
      (fun _ t _ => ((t : ℝ) + ((T * (2 * B - 1) + T : ℕ) : ℝ)) *
        ((2 : ℝ) / (Fintype.card F : ℝ))) := by
  simpa using lin_dag_pcd_knowledge_sound φ (scanDag T B hB) hN 2 (scanDag_fanin T B hB) Z

-- Edges (child-verifier copies) and depth (sequential latency), at 64 leaf steps.
#guard (chainDag 64).edges = 63 ∧ (chainDag 64).depth = 64
#guard (treeDag 64).edges = 126 ∧ (treeDag 64).depth = 7
#guard (scanDag 8 8 (by decide)).edges = 8 * 14 + 15 ∧ (scanDag 8 8 (by decide)).depth = 12
-- Shared nodes: the diamond pays node 0 once (4 rounds) where a tree unfolding pays it twice.
#guard diamond.edges = 4

/-- info: 'Minidregg.Selvage.DagPcd.dag_pcd_knowledge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dag_pcd_knowledge_sound
/-- info: 'Minidregg.Selvage.DagPcd.dag_pcd_fs_knowledge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dag_pcd_fs_knowledge_sound
/-- info: 'Minidregg.Selvage.DagPcd.lin_dag_pcd_knowledge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lin_dag_pcd_knowledge_sound

end DagPcd
end Minidregg.Selvage
