/-
# Compiler.Tower256SuccinctProver -- the honest succinct prover at any `ell`, `m`

`Tower256SuccinctHonestRun` hand-writes one receipt at `ell = 2`, `m = 1` and runs its guards in
the interpreter. This module is the same prover for every shape, written to be compiled (the
runner `Tower256SuccinctProverRun` is a `lean_exe`):

* the statement's basis is the unit coordinates `βⱼ = 2ʲ` (`unitBasis`), independent for every
  `ell ≤ 256` (`unitBasis_independent`): the leaf bits of a coordinate are an additive map to
  `ℕ → ZMod 2` (`leafBit_add`), and they send `2ʲ` to the `j`-th indicator (`leafBit_ofNat`);
* the level-0 word is a polynomial of fewer than `D · 2ᵐ` coefficients on the level-0 domain;
  each round commits a word as an array, draws its challenge from the transcript over the roots
  so far, and folds; the last word is interpolated through its first `D` domain points by
  Gaussian elimination, and its root is the final polynomial's (`lastRootC`);
* seeds come from the transcript, and each round opening carries the two leaves of its pair and
  the low leaf's `cubePath` without its leaf-level sibling.

Nothing here is trusted: `check` decides the receipt (`check_iff`). The prover's correctness is
observed, not proved; the runner exits nonzero when an observation fails.
-/

import Compiler.Tower256SuccinctHonestRun
import Compiler.Tower256SuccinctReceiptCodec
import Mathlib.Algebra.Module.ZMod

namespace Minidregg.Compiler.Tower256SuccinctProver

open Minidregg.Theory
open Minidregg.Compiler.Tower256AdditiveFriController (TranscriptPins Tower256)
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256CoordinateMerkle
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8 toField evalCoeffs)
open Minidregg.Compiler.Tower256SuccinctCheck
open Minidregg.Compiler.Tower256SuccinctHonestRun (invC)
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate capacity)
open Minidregg.Theory.BinaryCubeAddress (binaryAddressBits binaryCubeIndexEquiv)
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

instance : Inhabited C8 := ⟨Coordinate.zero 8⟩

/-! ## The unit basis is independent -/

/-- Leaf `i` of a coordinate, little-endian: the low half holds leaves below `2ᵏ`. -/
def leafBit : (k : Nat) → Coordinate k → Nat → ZMod 2
  | 0, c, i => if i = 0 ∧ Coordinate.bitOf c = true then 1 else 0
  | k + 1, c, i =>
      if i < 2 ^ k then leafBit k (Coordinate.low c) i else leafBit k (Coordinate.high c) (i - 2 ^ k)

theorem leafBit_add : ∀ (k : Nat) (a b : Coordinate k) (i : Nat),
    leafBit k (Coordinate.add k a b) i = leafBit k a i + leafBit k b i
  | 0, .bit x, .bit y, i => by
      by_cases h : i = 0 <;> cases x <;> cases y <;>
        simp [leafBit, Coordinate.add, Coordinate.bitOf, h] <;> decide
  | k + 1, .pair al ah, .pair bl bh, i => by
      simp only [leafBit, Coordinate.add, Coordinate.low_pair, Coordinate.high_pair]
      split
      · exact leafBit_add k al bl i
      · exact leafBit_add k ah bh _

theorem leafBit_ofNat : ∀ (k n i : Nat), i < 2 ^ k →
    leafBit k (Coord.ofNat k n) i = if n.testBit i then 1 else 0
  | 0, n, i, hi => by
      have h0 : i = 0 := by simpa using hi
      subst h0
      by_cases h : n % 2 = 1 <;> simp [leafBit, Coord.ofNat, Coordinate.bitOf, Nat.testBit_zero, h]
  | k + 1, n, i, hi => by
      simp only [leafBit, Coord.ofNat, Coordinate.low_pair, Coordinate.high_pair, capacity]
      split
      · rename_i h
        rw [leafBit_ofNat k _ i h, Nat.testBit_mod_two_pow]
        simp [h]
      · rename_i h
        have h2 : i - 2 ^ k < 2 ^ k := by
          rw [pow_succ] at hi
          generalize 2 ^ k = t at hi h ⊢
          omega
        rw [leafBit_ofNat k _ _ h2, Nat.testBit_div_two_pow,
          Nat.sub_add_cancel (Nat.le_of_not_lt h)]

/-- The leaf bits of a field element, as an additive map. -/
noncomputable def leafHom : Tower256 →+ (Nat → ZMod 2) :=
  AddMonoidHom.mk' (fun x => leafBit 8 (toField.symm x)) (by
    intro x y
    have h : toField.symm (x + y) = addC (toField.symm x) (toField.symm y) := by
      apply toField.injective
      simp
    funext i
    simp only [h, addC, leafBit_add, Pi.add_apply])

/-- The basis `βⱼ = 2ʲ`: coordinate `j` alone. -/
def unitBasis (ell : Nat) : Fin ell → C8 := fun j => Coord.ofNat 8 (2 ^ (j : Nat))

theorem leafHom_unitBasis (ell : Nat) (h : ell ≤ 256) (i j : Fin ell) :
    leafHom (betaF (unitBasis ell) (i : Nat)) (j : Nat) = if i = j then 1 else 0 := by
  have hj : (j : Nat) < 2 ^ 8 := by have := j.isLt; norm_num; omega
  unfold betaF
  rw [dif_pos i.isLt]
  show leafBit 8 (toField.symm (toField (unitBasis ell ⟨i, i.isLt⟩))) j = _
  rw [Equiv.symm_apply_apply, unitBasis, leafBit_ofNat 8 _ _ hj, Nat.testBit_two_pow]
  by_cases hij : i = j
  · subst hij; simp
  · have : (i : Nat) ≠ j := fun e => hij (Fin.ext e)
    simp [hij, this]

/-- **The unit basis is independent** over `ZMod 2`, for every `ell ≤ 256`. -/
theorem unitBasis_independent (ell : Nat) (h : ell ≤ 256) :
    LinearIndependent (ZMod 2) (fun j : Fin ell => betaF (unitBasis ell) j) := by
  apply LinearIndependent.of_comp (AddMonoidHom.toZModLinearMap 2 leafHom)
  rw [linearIndependent_iff']
  intro s g hsum j hj
  have hj' := congrFun hsum (j : Nat)
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply,
    AddMonoidHom.coe_toZModLinearMap, leafHom_unitBasis ell h, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', if_pos hj, Pi.zero_apply] at hj'
  exact hj'

/-! ## Interpolation -/

/-- Solve `rows · c = rhs` over coordinates, rows given as `coefficients ++ [rhs]`: Gaussian
elimination with a nonzero pivot per column; `none` if a column has none. -/
def gaussSolve (n : Nat) (rows0 : Array (Array C8)) : Option (Array C8) := Id.run do
  let zero := Coordinate.zero 8
  let mut rows := rows0
  for col in [0:n] do
    match (List.range' col (n - col)).find? (fun r => (rows[r]!)[col]! != zero) with
    | none => return none
    | some p =>
      let tmp := rows[p]!
      rows := (rows.set! p rows[col]!).set! col tmp
      let inv := invC (rows[col]!)[col]!
      rows := rows.set! col (rows[col]!.map fun x => mulC x inv)
      for r in [0:n] do
        if r != col then
          let f := (rows[r]!)[col]!
          if f != zero then
            rows := rows.set! r ((rows[r]!.zip rows[col]!).map fun (x, y) => addC x (mulC f y))
  return some ((List.range n).map (fun r => (rows[r]!)[n]!)).toArray

/-- The coefficients of the polynomial of fewer than `points.size` terms through `points`. -/
def interpolate (points : Array (C8 × C8)) : Option (List C8) :=
  let n := points.size
  let rows := points.map fun (x, y) =>
    ((List.range n).foldl (fun (acc : Array C8 × C8) _ => (acc.1.push acc.2, mulC acc.2 x))
      (#[], Coordinate.one 8)).1.push y
  (gaussSolve n rows).map Array.toList

/-! ## The prover -/

variable {ell m queryCount : Nat}

/-- A level-`j` word as an array in `additiveFriLevelEquivPowerTwo` order. -/
def readWord (j : Nat) (w : Array C8) (c : AdditiveFriLevels ell j) : C8 :=
  w[(additiveFriLevelEquivPowerTwo ell j c).val]!

/-- The same word as a Merkle column. -/
def columnOf (j : Nat) (w : Array C8) : (Fin (ell - j) → Bool) → C8 :=
  fun address => w[(binaryCubeIndexEquiv (ell - j) address).val]!

def tabulate (j : Nat) (f : AdditiveFriLevels ell j → C8) : Array C8 :=
  Array.ofFn fun i : Fin (2 ^ (ell - j)) => f ((additiveFriLevelEquivPowerTwo ell j).symm i)

def zeroRoot : Digest := ⟨0⟩

def stubReceipt (roots : Array Digest) (challenges : Array C8) (coeffs : List C8)
    (seeds : Fin queryCount → PowerTwoFriLevels ell 1) :
    CReceipt ell m queryCount where
  roots := fun n => roots.getD n zeroRoot
  challenges := fun j => challenges.getD j (Coordinate.zero 8)
  querySeed := seeds
  opening := fun _ _ => ⟨Coordinate.zero 8, Coordinate.zero 8, []⟩
  finalCoeffs := coeffs

/-- The statement the prover answers, for the unit basis (any offset; degree bound `n` is
`degree[n]`, zero past the list). -/
def statement (ell m : Nat) (hm : m ≤ ell) (hell : ell ≤ 256) (offset : C8) (degree : List Nat)
    (queryCount : Nat) (root0 : Digest) : CStatement ell m where
  beta := unitBasis ell
  offset := offset
  degree := fun n => degree.getD n 0
  queryCount := queryCount
  initialRoot := root0
  independent := unitBasis_independent ell hell
  rounds_le := hm

/-- One prover run: the statement, the receipt, and every committed word (levels `0..m`). -/
structure Run (ell m queryCount : Nat) where
  stmt : CStatement ell m
  receipt : CReceipt ell m queryCount
  words : Array (Array C8)
  /-- The root of the last folded word, before it is replaced by the final polynomial's. -/
  foldedLastRoot : Digest

/-- The honest prover over `poly` (the level-0 word's coefficients), with an optional mutant:
`delta = some (j, d)` commits the level-`j` word plus `d` (then folds honestly from it). -/
def prove (ell m queryCount : Nat) (hm : m ≤ ell) (hell : ell ≤ 256) (offset : C8)
    (degree : List Nat) (pins : TranscriptPins) (poly : List C8) (delta : Option (Nat × C8)) :
    Option (Run ell m queryCount) := Id.run do
  let beta := unitBasis ell
  let off := offset
  let finalDegree := degree.getD m 0
  let w0 : Array C8 := tabulate (ell := ell) 0 fun c => evalCoeffs poly (domC beta off 0 c)
  let root0 := cubeRoot merkleDomainsC codecC (columnOf (ell := ell) 0 w0)
  let s := statement ell m hm hell off degree queryCount root0
  let zeroSeeds : Fin queryCount → PowerTwoFriLevels ell 1 := fun _ => ⟨0, by positivity⟩
  let mut words : Array (Array C8) := #[w0]
  let mut roots : Array Digest := #[root0]
  let mut challenges : Array C8 := #[]
  for hj : j in [0:m] do
    let jm : Fin m := ⟨j, hj.upper⟩
    let alpha := challengeC s pins (stubReceipt roots challenges [] zeroSeeds) jm
    let w := words[j]!
    let pinv := invC (pivotC beta j)
    let next0 : Array C8 := tabulate (ell := ell) (j + 1) fun k =>
      let lo := liftBitC s jm 0 k
      let left := readWord j w lo
      let right := readWord j w (liftBitC s jm 1 k)
      addC left (mulC (mulC (addC (domC beta off j lo) alpha) (addC left right)) pinv)
    let next := match delta with
      | some (dj, d) => if dj = j + 1 then next0.map (addC d) else next0
      | none => next0
    challenges := challenges.push alpha
    words := words.push next
    if j + 1 < m then
      roots := roots.push (cubeRoot merkleDomainsC codecC (columnOf (ell := ell) (j + 1) next))
  let wm := words[m]!
  let foldedLast := cubeRoot merkleDomainsC codecC (columnOf (ell := ell) m wm)
  let points : Array (C8 × C8) := (List.range finalDegree).toArray.map fun n =>
    (domC beta off m ((additiveFriLevelEquivPowerTwo ell m).symm ⟨n % 2 ^ (ell - m),
      Nat.mod_lt _ (by positivity)⟩), wm[n]!)
  let some coeffs := interpolate points | return none
  roots := roots.push (lastRootC beta off m coeffs)
  let seeds := fun a => seedC s pins (stubReceipt roots challenges coeffs zeroSeeds) a
  let r0 : CReceipt ell m queryCount := stubReceipt roots challenges coeffs seeds
  let opening := fun (j : Fin m) (a : Fin queryCount) =>
    let w := words[(j : Nat)]!
    let k := additiveCoherentRound s.rounds_le j seeds a
    let lo := liftBitC s j 0 k
    ({ left := readWord j w lo
       right := readWord j w (liftBitC s j 1 k)
       pairPath := (cubePath merkleDomainsC codecC (columnOf (ell := ell) j w)
         (binaryAddressBits (ell - j) (additiveFriLevelEquivPowerTwo ell j lo))).dropLast } :
      CPairOpening)
  return some
    { stmt := s
      receipt := { r0 with opening := opening }
      words := words
      foldedLastRoot := foldedLast }

/-! ## Observations -/

/-- The full checks of round `j`, query `a`, separately: left, derived next, right, fold. -/
def parts (s : CStatement ell m) (r : CReceipt ell m queryCount) (j : Fin m) (a : Fin queryCount) :
    Bool × Bool × Bool × Bool :=
  let k := additiveCoherentRound s.rounds_le j r.querySeed a
  let o := r.opening j a
  let nx := r.nextOf s j a
  (recomputesC j (r.roots ⟨j, by omega⟩) (liftBitC s j 0 k) o.left o.leftFull,
   recomputesC ((j : Nat) + 1) (r.roots ⟨(j : Nat) + 1, by omega⟩) k nx.1 nx.2,
   recomputesC j (r.roots ⟨j, by omega⟩) (liftBitC s j 1 k) o.right o.rightFull,
   decide (mulC (addC nx.1 o.left) (pivotC s.beta j) =
     mulC (addC (domC s.beta s.offset j (liftBitC s j 0 k)) (r.challenges j))
       (addC o.left o.right)))

/-- Every round and query's parts, round-major. -/
def allParts (s : CStatement ell m) (r : CReceipt ell m queryCount) :
    List (Nat × Nat × (Bool × Bool × Bool × Bool)) :=
  (List.finRange m).flatMap fun (j : Fin m) => (List.finRange queryCount).map fun (a : Fin queryCount) =>
    ((j : Nat), (a : Nat), parts s r j a)

/-- For every round below the last and every query, the derived next-level leaf is the
committed level-`j+1` word's value at the query, with that word's own full path: the
`j + 1 < m` branch of `CReceipt.nextOf`, checked against the prover's tables. Returns the
number of (round, query) pairs compared and whether all agreed. -/
def nextBranchAgrees (run : Run ell m queryCount) : Nat × Bool :=
  let s := run.stmt
  let r := run.receipt
  let cases := (List.finRange m).flatMap fun (j : Fin m) =>
    (List.finRange queryCount).filterMap fun (a : Fin queryCount) =>
    if (j : Nat) + 1 < m then
      let k := additiveCoherentRound s.rounds_le j r.querySeed a
      let w := run.words[(j : Nat) + 1]!
      let path := cubePath merkleDomainsC codecC (columnOf (ell := ell) ((j : Nat) + 1) w)
        (binaryAddressBits (ell - ((j : Nat) + 1)) (additiveFriLevelEquivPowerTwo ell _ k))
      some (r.nextOf s j a == (readWord ((j : Nat) + 1) w k, path))
    else none
  (cases.length, cases.all id)

/-! ## Teeth, interpreted, at the smallest shape with two rounds

The runner checks the large shapes compiled; here the elaborator checks `ell = 3`, `m = 2`. -/

def tinyPoly : List C8 := (List.range 4).map fun n => Coord.ofNat 8 (7 + 11 * n)

def tiny : Option (Run 3 2 2) :=
  prove 3 2 2 (by norm_num) (by norm_num) (Coordinate.zero 8) [4, 2, 1]
    Tower256AdditiveFriRawDeployment.bootstrapPins tinyPoly none

#guard match tiny with
  | none => false
  | some run => check run.stmt Tower256AdditiveFriRawDeployment.bootstrapPins run.receipt &&
      run.foldedLastRoot == run.receipt.roots (Fin.last 2) &&
      nextBranchAgrees run == (2, true)

/-- info: 'Minidregg.Compiler.Tower256SuccinctProver.unitBasis_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unitBasis_independent

end Minidregg.Compiler.Tower256SuccinctProver
