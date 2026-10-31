/-
# Theory.OracleGame — proof systems in the random-oracle model, with operational costs

A non-interactive proof system whose prover, verifier, simulator and extractor are OBJECTS with a
size, not Lean functions: each is an `OCircuit`, a straight-line list of bit operations, coin
draws, oracle queries and (for a simulator) oracle programmings, evaluated by a fold. No pure Lean
callback can hide work inside one: the size counts every operation and every queried or
programmed bit. An unbounded simulator could recover a unique witness; one of bounded size
cannot. The statement and witness codecs (`Codec`) and the relation are the CALLER's fixed
definitions, never the backend's, so no decode can search for a witness.

Adversaries are the opposite: shallow programs (`Adv`, a free monad of coins, oracle queries and
proof requests) of unbounded running time, bounded only in queries, requests and coins
(`Adv.Within`). Security is statistical in the random-oracle model; every bound is the caller's
(the theorem's label), never the backend's.

* `Tape`: the finite sample space, fresh coins and the lazily sampled oracle's fresh answers. A
  query answers from the table if the point was queried or programmed, else with the next fresh
  answer; programming a point already defined sets `conflict` and keeps the old value. Each
  security notion holds for every tape at least the caller's sizes, so a short tape cannot make
  the experiment degenerate.
* `System`: per public statement width, the four circuits.
* `Complete`; `KnowledgeSound` (straight-line extraction from the statement, the proof and the
  oracle log, failure probability at most `num/den` against every bounded forger);
  `ZeroKnowledge` (adaptive multi-theorem: the adversary's requests are answered by the prover
  with the witness in the real world and by one fixed simulator from the statement alone in the
  ideal one, sharing the oracle with the adversary; fresh coins per proof by construction);
  `Sized` (each circuit's size at most the caller's bound at the statement width; only the
  simulator programs).

ATLAS fields: satisfiable `Echo` (the relation "the witness is the statement": empty proofs, an
extractor copying the statement) meets all four at bound 0; teeth `reveal_refuted` (a prover
whose proof is its witness is not zero knowledge below one half on a statement with two
witnesses, against ANY simulator) and `acceptAll_refuted` (a verifier accepting everything is not
knowledge sound for an empty relation below one).
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Theory.OracleGame

set_option autoImplicit false

/-! ## The sample space and the lazily sampled oracle -/

/-- `C` fresh coins and `N` fresh oracle answers of `lam` bits each, uniformly drawn. -/
abbrev Tape (C N lam : Nat) := (Fin C → Bool) × (Fin N → Fin lam → Bool)

/-- The experiment's state: the next coin, the next fresh answer, the oracle's table (most recent
first) and whether a programming hit a point already defined. -/
structure OState where
  coin : Nat
  fresh : Nat
  table : List (List Bool × List Bool)
  conflict : Bool

def OState.init : OState := ⟨0, 0, [], false⟩

variable {C N lam : Nat}

/-- The next coin. -/
def drawCoin (t : Tape C N lam) (s : OState) : Bool × OState :=
  (if h : s.coin < C then t.1 ⟨s.coin, h⟩ else false, { s with coin := s.coin + 1 })

/-- An oracle query: the table's answer, else the next fresh answer, recorded. -/
def oracle (t : Tape C N lam) (s : OState) (q : List Bool) : List Bool × OState :=
  match s.table.lookup q with
  | some a => (a, s)
  | none =>
      let a := if h : s.fresh < N then List.ofFn (t.2 ⟨s.fresh, h⟩) else List.replicate lam false
      (a, { s with fresh := s.fresh + 1, table := (q, a) :: s.table })

/-- A programming: define the oracle at `q` as `a` (padded or cut to `lam` bits); a point already
defined is a conflict and keeps its value. -/
def programAt (lam : Nat) (s : OState) (q a : List Bool) : OState :=
  match s.table.lookup q with
  | some _ => { s with conflict := true }
  | none => { s with table := (q, (a ++ List.replicate lam false).take lam) :: s.table }

/-! ## Oracle circuits: the costed objects -/

/-- One operation. Every operation appends its outputs to the wire list; operands are earlier
wire indices (a missing wire reads `false`). -/
inductive Op where
  /-- Bit `i` of the input. -/
  | input (i : Nat)
  | const (b : Bool)
  | xor (a b : Nat)
  | and (a b : Nat)
  /-- A fresh coin. -/
  | coin
  /-- The oracle at the bits of `ins`: appends its `lam` answer wires. -/
  | query (ins : List Nat)
  /-- Program the oracle at the bits of `ins` to the bits of `outs`: appends nothing. -/
  | program (ins outs : List Nat)
  deriving DecidableEq, Repr

/-- A straight-line oracle circuit and its output wires. -/
structure OCircuit where
  ops : List Op
  outs : List Nat
  deriving DecidableEq, Repr

/-- The cost of one operation: one, plus every bit it queries or programs. -/
def Op.cost : Op → Nat
  | .query ins => 1 + ins.length
  | .program ins outs => 1 + ins.length + outs.length
  | _ => 1

/-- **The size**: every operation, every queried or programmed bit, and every output. -/
def OCircuit.size (c : OCircuit) : Nat := (c.ops.map Op.cost).sum + c.outs.length

def Op.programs : Op → Bool
  | .program _ _ => true
  | _ => false

/-- A circuit that never programs the oracle (only a simulator may). -/
def OCircuit.Plain (c : OCircuit) : Prop := ∀ op ∈ c.ops, op.programs = false

/-- One operation's step on the wires and the state. -/
def Op.step (lam : Nat) (t : Tape C N lam) (input : List Bool) :
    List Bool × OState → Op → List Bool × OState
  | (w, s), .input i => (w ++ [input.getD i false], s)
  | (w, s), .const b => (w ++ [b], s)
  | (w, s), .xor a b => (w ++ [Bool.xor (w.getD a false) (w.getD b false)], s)
  | (w, s), .and a b => (w ++ [w.getD a false && w.getD b false], s)
  | (w, s), .coin => ((w ++ [(drawCoin t s).1]), (drawCoin t s).2)
  | (w, s), .query ins => (w ++ (oracle t s (ins.map (w.getD · false))).1, (oracle t s (ins.map (w.getD · false))).2)
  | (w, s), .program ins outs => (w, programAt lam s (ins.map (w.getD · false)) (outs.map (w.getD · false)))

/-- **The evaluation**: a fold of the operations; the output bits and the final state. -/
def OCircuit.run (lam : Nat) (t : Tape C N lam) (c : OCircuit) (input : List Bool) (s : OState) :
    List Bool × OState :=
  let r := c.ops.foldl (Op.step lam t input) ([], s)
  (c.outs.map (r.1.getD · false), r.2)

/-! ## Adversaries: shallow, query-bounded -/

/-- An adversary: coins, oracle queries and requests for a proof of a statement with a witness. -/
inductive Adv (Stmt Wit α : Type) where
  | done (a : α)
  | coin (next : Bool → Adv Stmt Wit α)
  | query (q : List Bool) (next : List Bool → Adv Stmt Wit α)
  | ask (x : Stmt) (w : Wit) (next : List Bool → Adv Stmt Wit α)

namespace Adv

variable {Stmt Wit α : Type}

/-- At most `q` queries, `m` requests and `c` coins along every path. -/
def Within : Adv Stmt Wit α → Nat → Nat → Nat → Prop
  | .done _, _, _, _ => True
  | .coin next, q, m, c => 0 < c ∧ ∀ b, (next b).Within q m (c - 1)
  | .query _ next, q, m, c => 0 < q ∧ ∀ a, (next a).Within (q - 1) m c
  | .ask _ _ next, q, m, c => 0 < m ∧ ∀ π, (next π).Within q (m - 1) c

/-- Every request is of a statement and witness in the relation. -/
def AsksTrue (rel : Stmt → Wit → Prop) : Adv Stmt Wit α → Prop
  | .done _ => True
  | .coin next => ∀ b, (next b).AsksTrue rel
  | .query _ next => ∀ a, (next a).AsksTrue rel
  | .ask x w next => rel x w ∧ ∀ π, (next π).AsksTrue rel

/-- The run, answering each request by `answer` on the shared state. -/
def run (t : Tape C N lam) (answer : Stmt → Wit → OState → List Bool × OState) :
    Adv Stmt Wit α → OState → α × OState
  | .done a, s => (a, s)
  | .coin next, s => (next (drawCoin t s).1).run t answer (drawCoin t s).2
  | .query q next, s => (next (oracle t s q).1).run t answer (oracle t s q).2
  | .ask x w next, s => (next (answer x w s).1).run t answer (answer x w s).2

end Adv

/-! ## Proof systems -/

/-- **The caller's codec**: the statement's bits (their number is the public width the circuits
are chosen by), the witness's bits, and the witness read back from an extractor's output. -/
structure Codec (Stmt Wit : Type) where
  encode : Stmt → List Bool
  encodeWit : Wit → List Bool
  decodeWit : List Bool → Wit

/-- A proof system: per statement width, the prover (input: statement bits, then witness bits),
the verifier (statement bits, then proof bits; output bit 0 decides), the simulator (statement
bits) and the extractor (statement bits, proof bits, then the oracle log). -/
structure System where
  prover : Nat → OCircuit
  verifier : Nat → OCircuit
  simulator : Nat → OCircuit
  extractor : Nat → OCircuit

variable {Stmt Wit : Type}

/-- A bit string, self-delimiting: each bit after a `true`, then a `false`. -/
def framed (bits : List Bool) : List Bool := bits.flatMap (fun b => [true, b]) ++ [false]

/-- The oracle log as bits: each entry's point and answer, framed. -/
def logBits (table : List (List Bool × List Bool)) : List Bool :=
  table.flatMap fun e => framed e.1 ++ framed e.2

/-- The verifier's decision on a statement and a proof, on the shared oracle. -/
def System.verify (sys : System) (codec : Codec Stmt Wit) (lam : Nat) (t : Tape C N lam) (x : Stmt)
    (π : List Bool) (s : OState) : Bool × OState :=
  let r := (sys.verifier (codec.encode x).length).run lam t (codec.encode x ++ π) s
  (r.1.headD false, r.2)

/-- The honest prover's answer to a request. -/
def System.prove (sys : System) (codec : Codec Stmt Wit) (lam : Nat) (t : Tape C N lam) (x : Stmt) (w : Wit) (s : OState) :
    List Bool × OState :=
  (sys.prover (codec.encode x).length).run lam t (codec.encode x ++ codec.encodeWit w) s

/-- The simulator's answer: from the statement only. -/
def System.simulate (sys : System) (codec : Codec Stmt Wit) (lam : Nat) (t : Tape C N lam) (x : Stmt) (_ : Wit) (s : OState) :
    List Bool × OState :=
  (sys.simulator (codec.encode x).length).run lam t (codec.encode x) s

/-- **Perfect completeness**: on every tape and state, an honest proof of a true statement verifies. -/
def Complete (codec : Codec Stmt Wit) (sys : System) (lam : Nat) (rel : Stmt → Wit → Prop) : Prop :=
  ∀ (C N : Nat) (t : Tape C N lam) (x : Stmt) (w : Wit) (s : OState), rel x w →
    (sys.verify codec lam t x (sys.prove codec lam t x w s).1 (sys.prove codec lam t x w s).2).1 = true

/-- The probability of an event over the tapes is at most `num/den`. -/
def ProbAtMost (Ω : Type) [Fintype Ω] (num den : Nat) (event : Ω → Prop) : Prop :=
  0 < Fintype.card Ω ∧ 0 < den ∧
    (by classical exact (Finset.univ.filter event).card) * den ≤ num * Fintype.card Ω

/-- The number of tapes on which an experiment says yes. -/
def yes {Ω : Type} [Fintype Ω] (experiment : Ω → Bool) : Nat :=
  (Finset.univ.filter fun t => experiment t = true).card

/-- The gap between two experiments over the tapes is at most `num/den`. -/
def GapOn (Ω : Type) [Fintype Ω] (num den : Nat) (left right : Ω → Bool) : Prop :=
  0 < Fintype.card Ω ∧ 0 < den ∧
    yes left * den ≤ yes right * den + num * Fintype.card Ω ∧
    yes right * den ≤ yes left * den + num * Fintype.card Ω

/-- A cheating prover: an adversary that returns a statement and a proof (its requests, which
`Within _ 0 _` excludes, are answered by nothing). -/
abbrev Forger (Stmt Wit : Type) := Adv Stmt Wit (Stmt × List Bool)

/-- **The knowledge-soundness failure**: the forger's proof verifies on the shared oracle, and the
extractor, from the statement, the proof and the oracle log after verification, does not output a
witness. -/
def ksFails (codec : Codec Stmt Wit) (sys : System) (lam : Nat) (rel : Stmt → Wit → Prop) (P : Forger Stmt Wit)
    (t : Tape C N lam) : Prop :=
  let forged := P.run t (fun _ _ s => ([], s)) OState.init
  let checked := sys.verify codec lam t forged.1.1 forged.1.2 forged.2
  checked.1 = true ∧
    ¬ rel forged.1.1 (codec.decodeWit ((sys.extractor (codec.encode forged.1.1).length).run lam t
      (codec.encode forged.1.1 ++ forged.1.2 ++ logBits checked.2.table) checked.2).1)

/-- **Straight-line knowledge soundness** at `num/den` against every forger making at most `q`
queries and drawing at most `c` coins, on every tape of at least `C₀` coins and `N₀` answers. -/
def KnowledgeSound (codec : Codec Stmt Wit) (sys : System) (lam : Nat) (rel : Stmt → Wit → Prop) (q c C₀ N₀ num den : Nat) : Prop :=
  ∀ C N, C₀ ≤ C → N₀ ≤ N → ∀ P : Forger Stmt Wit, P.Within q 0 c →
    ProbAtMost (Tape C N lam) num den (ksFails codec (C := C) (N := N) sys lam rel P)

/-- The real experiment: requests answered by the honest prover; the adversary's bit. -/
def real (codec : Codec Stmt Wit) (sys : System) (lam : Nat) (A : Adv Stmt Wit Bool) (t : Tape C N lam) : Bool :=
  (A.run t (sys.prove codec lam t) OState.init).1

/-- The ideal experiment: requests answered by the simulator from the statement alone. -/
def ideal (codec : Codec Stmt Wit) (sys : System) (lam : Nat) (A : Adv Stmt Wit Bool) (t : Tape C N lam) : Bool :=
  (A.run t (sys.simulate codec lam t) OState.init).1

/-- **Adaptive multi-theorem zero knowledge** at `num/den` against every adversary asking only
true statements, with at most `q` queries, `m` requests and `c` coins, on every tape of at least
`C₀` coins and `N₀` answers. The simulator is the system's, fixed before the adversary. -/
def ZeroKnowledge (codec : Codec Stmt Wit) (sys : System) (lam : Nat) (rel : Stmt → Wit → Prop) (q m c C₀ N₀ num den : Nat) : Prop :=
  ∀ C N, C₀ ≤ C → N₀ ≤ N → ∀ A : Adv Stmt Wit Bool, A.Within q m c → A.AsksTrue rel →
    GapOn (Tape C N lam) num den (real codec sys lam A) (ideal codec sys lam A)

/-- **Operational size**: the prover, verifier and extractor never program; each circuit's size is
at most the caller's bound at the statement width. -/
structure Sized (sys : System) (proverBound verifierBound simulatorBound extractorBound : Nat → Nat) : Prop where
  plain : ∀ n, (sys.prover n).Plain ∧ (sys.verifier n).Plain ∧ (sys.extractor n).Plain
  prover : ∀ n, (sys.prover n).size ≤ proverBound n
  verifier : ∀ n, (sys.verifier n).size ≤ verifierBound n
  simulator : ∀ n, (sys.simulator n).size ≤ simulatorBound n
  extractor : ∀ n, (sys.extractor n).size ≤ extractorBound n

/-! ## Evaluation lemmas -/

theorem foldl_inputs (lam : Nat) (t : Tape C N lam) (input : List Bool) :
    ∀ (l : List Nat) (w : List Bool) (s : OState),
      (l.map Op.input).foldl (Op.step lam t input) (w, s) = (w ++ l.map (input.getD · false), s)
  | [], w, s => by simp
  | i :: l, w, s => by
      simp only [List.map_cons, List.foldl_cons, Op.step]
      rw [foldl_inputs lam t input l]
      simp

theorem card_pos (C N lam : Nat) : 0 < Fintype.card (Tape C N lam) := Fintype.card_pos

/-! ## The satisfiable pole: the witness is the statement -/

namespace Echo

/-- The identity circuit on the first `n` input bits. -/
def copy (n : Nat) : OCircuit := ⟨(List.range n).map Op.input, List.range n⟩

/-- The circuit outputting one `true`. -/
def accept : OCircuit := ⟨[.const true], [0]⟩

def empty : OCircuit := ⟨[], []⟩

def bits : Codec (List Bool) (List Bool) := ⟨id, id, id⟩

/-- Empty proofs, a verifier that accepts, an extractor that copies the statement. -/
def system : System := ⟨fun _ => empty, fun _ => accept, fun _ => empty, copy⟩

def rel : List Bool → List Bool → Prop := fun x w => w = x

theorem copy_run (lam : Nat) (t : Tape C N lam) (x rest : List Bool) (s : OState) :
    ((copy x.length).run lam t (x ++ rest) s).1 = x := by
  simp only [OCircuit.run, copy]
  rw [foldl_inputs]
  simp only [List.nil_append]
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, h₁]

theorem complete : Complete bits system 0 rel := by
  intro C N t x w s _
  rfl

theorem knowledgeSound (q c C₀ N₀ den : Nat) (positive : 0 < den) :
    KnowledgeSound bits system 0 rel q c C₀ N₀ 0 den := by
  intro C N _ _ P _
  refine ⟨card_pos C N 0, positive, ?_⟩
  have none : ∀ t : Tape C N 0, ¬ ksFails bits system 0 rel P t := by
    intro t fails
    simp only [ksFails] at fails
    apply fails.2
    simp only [system, bits, rel, id]
    rw [List.append_assoc, copy_run]
  classical
  rw [Finset.filter_false_of_mem (fun t _ => none t)]
  simp

theorem zeroKnowledge (q m c C₀ N₀ den : Nat) (positive : 0 < den) :
    ZeroKnowledge bits system 0 rel q m c C₀ N₀ 0 den := by
  intro C N _ _ A _ _
  have answers : ∀ t : Tape C N 0, system.prove bits 0 t = system.simulate bits 0 t := by
    intro t; funext x w s; rfl
  have same : real bits system 0 A = (ideal bits system 0 A : Tape C N 0 → Bool) := by
    funext t
    simp only [real, ideal, answers]
  refine ⟨card_pos C N 0, positive, ?_, ?_⟩ <;> rw [same] <;> omega

theorem sized : Sized system (fun _ => 0) (fun _ => 2) (fun _ => 0) (fun n => 2 * n) := by
  refine ⟨fun n => ⟨?_, ?_, ?_⟩, fun n => by simp [system, empty, OCircuit.size],
    fun n => by simp [system, accept, OCircuit.size, Op.cost], fun n => by simp [system, empty, OCircuit.size], fun n => ?_⟩
  · intro op member; simp [system, empty] at member
  · intro op member; simp [system, accept] at member; subst member; rfl
  · intro op member; simp only [system, copy, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member; rfl
  · simp only [system, copy, OCircuit.size, List.map_map, List.length_range]
    have : (List.map (Op.cost ∘ Op.input) (List.range n)).sum = n := by
      induction n with
      | zero => rfl
      | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; rfl
    rw [this]
    omega

end Echo

/-! ## Teeth -/

section Teeth

/-- A knowledge-sound verifier must refuse something: a verifier accepting every proof is not
knowledge sound below one for a relation with no witness. -/
theorem acceptAll_refuted (codec : Codec Stmt Wit) (sys : System) (lam : Nat) (x : Stmt)
    (accepts : ∀ n, sys.verifier n = Echo.accept) (q c C₀ N₀ num den : Nat) (small : num < den) :
    ¬ KnowledgeSound codec sys lam (fun _ _ => False) q c C₀ N₀ num den := by
  intro sound
  obtain ⟨positive, _, bound⟩ := sound C₀ N₀ le_rfl le_rfl (.done (x, [])) trivial
  have all : ∀ t : Tape C₀ N₀ lam, ksFails codec sys lam (fun _ _ => False) (.done (x, [])) t := by
    intro t
    simp only [ksFails, Adv.run, System.verify, accepts, not_false_eq_true, and_true]
    rfl
  classical
  simp only [Finset.filter_true_of_mem (fun t _ => all t), Finset.card_univ] at bound
  have : num * Fintype.card (Tape C₀ N₀ lam) < den * Fintype.card (Tape C₀ N₀ lam) :=
    Nat.mul_lt_mul_of_pos_right small positive
  rw [Nat.mul_comm (Fintype.card _) den] at bound
  omega

/-- The prover whose proof is its witness (the `k` witness bits after the statement's `n`). -/
def revealProver (k n : Nat) : OCircuit := ⟨((List.range k).map (n + ·)).map Op.input, List.range k⟩

/-- The adversary requesting one proof of `x` with `w` and saying yes iff the proof is `w`'s bits. -/
def askOnce (codec : Codec Stmt Wit) (x : Stmt) (w : Wit) : Adv Stmt Wit Bool :=
  .ask x w fun π => .done (π == codec.encodeWit w)

theorem revealProver_run (lam : Nat) (t : Tape C N lam) (x w : List Bool) (s : OState) :
    ((revealProver w.length x.length).run lam t (x ++ w) s).1 = w := by
  simp only [OCircuit.run, revealProver]
  rw [foldl_inputs]
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, h₁]

/-- **Teeth**: if the prover's proof is the witness, the system is not zero knowledge below one
half against the two one-request adversaries, whatever its simulator, on a statement with two
witnesses of one encoding length. -/
theorem reveal_refuted (codec : Codec Stmt Wit) (sys : System) (lam : Nat) (rel : Stmt → Wit → Prop)
    (x : Stmt) (w₁ w₂ : Wit) (h₁ : rel x w₁) (h₂ : rel x w₂)
    (distinct : codec.encodeWit w₁ ≠ codec.encodeWit w₂)
    (width : (codec.encodeWit w₁).length = (codec.encodeWit w₂).length)
    (reveals : sys.prover (codec.encode x).length = revealProver (codec.encodeWit w₁).length (codec.encode x).length)
    (q m c C₀ N₀ num den : Nat) (one : 0 < m) (small : 2 * num < den) :
    ¬ ZeroKnowledge codec sys lam rel q m c C₀ N₀ num den := by
  intro zk
  have within : ∀ w, (askOnce codec x w).Within q m c := fun w => ⟨one, fun _ => trivial⟩
  have asks : ∀ w, rel x w → (askOnce codec x w).AsksTrue rel := fun w h => ⟨h, fun _ => trivial⟩
  obtain ⟨positive, _, first, _⟩ := zk C₀ N₀ le_rfl le_rfl _ (within w₁) (asks w₁ h₁)
  obtain ⟨_, _, second, _⟩ := zk C₀ N₀ le_rfl le_rfl _ (within w₂) (asks w₂ h₂)
  have realYes : ∀ w, (codec.encodeWit w).length = (codec.encodeWit w₁).length →
      yes (real codec sys lam (askOnce codec x w) : Tape C₀ N₀ lam → Bool) = Fintype.card (Tape C₀ N₀ lam) := by
    intro w len
    have : ∀ t : Tape C₀ N₀ lam, real codec sys lam (askOnce codec x w) t = true := by
      intro t
      simp only [real, askOnce, Adv.run, System.prove, reveals, ← len, revealProver_run, beq_self_eq_true]
    simp [yes, this]
  rw [realYes w₁ rfl] at first
  rw [realYes w₂ width.symm] at second
  let guess : Tape C₀ N₀ lam → List Bool := fun t =>
    ((sys.simulator (codec.encode x).length).run lam t (codec.encode x) OState.init).1
  have idealIs : ∀ w (t : Tape C₀ N₀ lam), ideal codec sys lam (askOnce codec x w) t = (guess t == codec.encodeWit w) := by
    intro w t; rfl
  have split : yes (ideal codec sys lam (askOnce codec x w₁) : Tape C₀ N₀ lam → Bool) +
      yes (ideal codec sys lam (askOnce codec x w₂) : Tape C₀ N₀ lam → Bool) ≤ Fintype.card (Tape C₀ N₀ lam) := by
    simp only [yes, idealIs]
    have disjoint : Disjoint (Finset.univ.filter fun t : Tape C₀ N₀ lam => (guess t == codec.encodeWit w₁) = true)
        (Finset.univ.filter fun t : Tape C₀ N₀ lam => (guess t == codec.encodeWit w₂) = true) := by
      rw [Finset.disjoint_filter]
      intro t _ a b
      simp only [beq_iff_eq] at a b
      exact distinct (a.symm.trans b)
    rw [← Finset.card_union_of_disjoint disjoint]
    exact Finset.card_le_univ _
  have scaled := Nat.mul_le_mul_right den split
  rw [Nat.add_mul] at scaled
  have : Fintype.card (Tape C₀ N₀ lam) * den ≤ Fintype.card (Tape C₀ N₀ lam) * (2 * num) := by nlinarith
  have := Nat.le_of_mul_le_mul_left this positive
  omega

end Teeth

#assert_axioms Echo.complete
#assert_axioms Echo.knowledgeSound
#assert_axioms Echo.zeroKnowledge
#assert_axioms Echo.sized
#assert_axioms acceptAll_refuted
#assert_axioms reveal_refuted

end Minidregg.Theory.OracleGame
