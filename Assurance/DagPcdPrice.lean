/-
# Assurance.DagPcdPrice — chain, tree and Mina scan state, priced by the cost function

`Selvage.DagPcd` proves that the straightline knowledge error of a DAG of `N` accumulation
steps with fan-in at most `a` is `(t + N) · a / |F|` for the shared-functional fold
(`lin_dag_pcd_knowledge_sound`), with no depth term. This file prices the three shapes ember
named (chain, tree, Mina's scan state) with `Assurance.CostModel`, the costmodel lane's
function, at the same number of leaf steps `L`:

* **work**: a recursive prover verifies every child once, so the in-circuit verifier copies
  are the DAG's edges, `Σᵢ fanin(i)`, each costing `verifierCounts p child`
  (`recursionStepCounts`);
* **latency**: the depth, in sequential proving steps;
* **soundness**: the fold term of `lin_dag_pcd_knowledge_sound` at the challenge field
  `|F| = p.challengeCard` and `t = A.hashQueries`, read in bits by `bitsOf`, next to the
  decider proof's own `udrBits`.

Every number below is a compiled check over concrete data.
-/
import Assurance.CostModel
import Selvage.DagPcd

namespace Minidregg.Assurance.DagPcdPrice

open Minidregg.Assurance.Cost
open Minidregg.Selvage.DagPcd

variable {N : ℕ}

/-- Native counts of all recursion steps of a DAG: node `i` verifies its `fanin(i)` children. -/
def dagStepCounts (G : Dag N) (p : Params) (child : Shape) : Counts :=
  (List.finRange N).foldr (fun i c => recursionStepCounts (G.pred i).length p child + c) 0

/-- The fold term of `lin_dag_pcd_knowledge_sound`, `(t + N) · a / |F|`, at `t` hash queries,
fan-in bound `a` and the challenge field of `p`. -/
def foldErr (A : Adversary) (p : Params) (N a : ℕ) : ℚ :=
  ((A.hashQueries + N : ℕ) : ℚ) * a / p.challengeCard

/-- Its bits. -/
def foldBits (A : Adversary) (p : Params) (N a : ℕ) : ℕ := bitsOf (foldErr A p N a)

/-- The 1024-leaf shapes: a chain, the queue-merge tree, and a scan state of 32 blocks of 32. -/
def chain1k : Dag 1024 := chainDag 1024
def tree1k : Dag (2 * 1024 - 1) := treeDag 1024
def scan1k : Dag (32 * (2 * 32 - 1) + 32) := scanDag 32 32 (by decide)

-- Edges (child-verifier copies) and depth (sequential steps).
#guard chain1k.edges = 1023 ∧ chain1k.depth = 1024
#guard tree1k.edges = 2046 ∧ tree1k.depth = 11
#guard scan1k.edges = 2047 ∧ scan1k.depth = 38

-- Work: the recursion counts ARE edges times one child verifier, on every shape.
#guard dagStepCounts chain1k ud100 refLeaf = 1023 • verifierCounts ud100 refLeaf
#guard dagStepCounts tree1k ud100 refLeaf = 2046 • verifierCounts ud100 refLeaf
#guard dagStepCounts scan1k ud100 refLeaf = 2047 • verifierCounts ud100 refLeaf

-- Soundness at ud100 (BabyBear⁶ challenges): the fold term sits near 2^-144 on every shape,
-- so the decider's 100 bits bind and the shape is a pure work/latency choice.
#guard udrBits deployedAdversary ud100 refLeaf = 100
#guard foldBits deployedAdversary ud100 1024 1 = 145
#guard foldBits deployedAdversary ud100 2047 2 = 144
#guard foldBits deployedAdversary ud100 2048 2 = 144

-- At the deployed extension (BabyBear⁴, `ir2Params`, |F| ≈ 2^123) the fold term alone caps a
-- fan-in-2 DAG at 82 bits and a chain at 83, whatever the queries: 100-bit aggregation needs
-- the degree-6 challenge field.
#guard foldBits deployedAdversary ir2Params 2047 2 = 82
#guard foldBits deployedAdversary ir2Params 1024 1 = 83

-- At the deployed extension (BabyBear⁴, ir2Params) the fold term alone caps a fan-in-2 DAG
-- below 100 bits, whatever the queries: aggregation needs the degree-6 challenge field.

end Minidregg.Assurance.DagPcdPrice
