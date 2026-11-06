/-
# Compiler.Tower256SuccinctHonestRun -- an accepting one-fold receipt, and one mutant per clause

`Tower256SuccinctCheck`'s bootstrap teeth have no folding round, so the challenge, seed and fold
clauses of `check` are empty there. This file is a small honest prover at `ell = 2`, `m = 1`,
two queries: it commits a level-0 word, draws the challenge from the transcript, folds, interpolates
the level-1 word into a two-coefficient final polynomial, draws the query seeds, and opens. The
compiled checker accepts it, and each of three mutants, built by the same prover so that every
other clause still holds, fails exactly its own clause:

* `alphaBad`: the prover folds with a challenge other than the transcript's;
* `seedBad`: the prover opens at query positions other than the transcript's;
* `delta`: the prover commits a level-1 word that is the fold plus a constant (still of degree
  below two, so the last-root and degree clauses hold, and every Merkle opening verifies).
-/

import Compiler.Tower256SuccinctCheck

namespace Minidregg.Compiler.Tower256SuccinctHonestRun

open Minidregg.Theory
open Minidregg.Compiler.Tower256AdditiveFriController (TranscriptPins Tower256)
open Minidregg.Compiler.Tower256AdditiveFriRawDeployment (bootstrapPins)
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256CoordinateMerkle
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8 toField evalCoeffs)
open Minidregg.Compiler.Tower256SuccinctCheck
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate coordinateFieldEquiv_one)
open Minidregg.Theory.BinaryCubeAddress (binaryAddressBits binaryCubeIndexEquiv)
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- `p ^ (2^256 - 2)`, the inverse of a nonzero `p`: the prover's only division. -/
def invC (p : C8) : C8 :=
  ((List.range 255).foldl (fun (st : C8 × C8) _ =>
    let x := mulC st.1 st.1
    (x, mulC st.2 x)) (p, Coordinate.one 8)).2

/-! ## The statement: basis `[1, g]` with `g` the integer-2 coordinate -/

def gen : C8 := Coord.ofNat 8 2

def beta2 : Fin 2 → C8 := ![Coordinate.one 8, gen]

theorem betaF_beta2 :
    (fun j : Fin 2 => betaF beta2 j) = ![toField (Coordinate.one 8), toField gen] := by
  funext j
  fin_cases j <;> rfl

theorem indep : LinearIndependent (ZMod 2) (fun j : Fin 2 => betaF beta2 j) := by
  rw [betaF_beta2, LinearIndependent.pair_iff, show toField (Coordinate.one 8) = 1 from
    coordinateFieldEquiv_one 8]
  have hg0 : toField gen ≠ 0 := by
    rw [← toField_zeroC]
    exact fun h => absurd (toField.injective h) (by decide)
  have hg1 : toField gen ≠ 1 := by
    rw [← show toField (Coordinate.one 8) = 1 from coordinateFieldEquiv_one 8]
    exact fun h => absurd (toField.injective h) (by decide)
  intro s t hst
  have two : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hs := two s
  have ht := two t
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp only [zero_smul, one_smul, zero_add, add_zero] at hst
  · exact ⟨rfl, rfl⟩
  · exact absurd hst hg0
  · exact absurd hst one_ne_zero
  · exact absurd (show toField gen = 1 by
      linear_combination hst - (CharTwo.two_eq_zero : (2 : Tower256) = 0)) hg1

def mkStatement (root0 : Digest) : CStatement 2 1 where
  beta := beta2
  offset := Coordinate.zero 8
  degree := fun _ => 2
  queryCount := 2
  initialRoot := root0
  independent := indep
  rounds_le := by norm_num

/-! ## The prover -/

def word0 (c : AdditiveFriLevels 2 0) : C8 :=
  Coord.ofNat 8 (3 + 5 * (additiveFriLevelEquivPowerTwo 2 0 c).val)

def col0 (address : Fin (2 - 0) → Bool) : C8 :=
  word0 ((additiveFriLevelEquivPowerTwo 2 0).symm (binaryCubeIndexEquiv (2 - 0) address))

def root0 : Digest := cubeRoot merkleDomainsC codecC col0

def path0 (c : AdditiveFriLevels 2 0) : List UInt8 :=
  merkleDomainsC.proofCodec.encode
    (cubePath merkleDomainsC codecC col0 (binaryAddressBits (2 - 0) (additiveFriLevelEquivPowerTwo 2 0 c)))

def s0 : CStatement 2 1 := mkStatement root0

def zeroOpening : FriQueryOpening C8 (List UInt8) (List UInt8) :=
  ⟨Coordinate.zero 8, Coordinate.zero 8, Coordinate.zero 8, [], [], []⟩

def stub (roots : Fin 2 → Digest) (chal : Fin 1 → C8) (seed : Fin 2 → PowerTwoFriLevels 2 1)
    (op : Fin 2 → FriQueryOpening C8 (List UInt8) (List UInt8)) (coeffs : List C8) :
    CReceipt 2 1 2 :=
  ⟨roots, chal, seed, fun _ a => op a, coeffs⟩

def zeroSeed : Fin 2 → PowerTwoFriLevels 2 1 := fun _ => ⟨0, by norm_num⟩

def flipSeed (x : PowerTwoFriLevels 2 1) : PowerTwoFriLevels 2 1 :=
  ⟨(x.val + 1) % 2 ^ (2 - 1), Nat.mod_lt _ (by positivity)⟩

/-- The prover. `alphaBad`, `seedBad` and `delta` select the mutants; the honest prover is
`prove none false (Coordinate.zero 8)`. -/
def prove (pins : TranscriptPins) (alphaBad : Option C8) (seedBad : Bool) (delta : C8) :
    CReceipt 2 1 2 :=
  let alpha := alphaBad.getD
    (challengeC s0 pins (stub (fun _ => root0) (fun _ => Coordinate.zero 8) zeroSeed
      (fun _ => zeroOpening) []) 0)
  let pinv := invC (pivotC beta2 0)
  let word1 : AdditiveFriLevels 2 1 → C8 := fun k =>
    let lo := liftBitC s0 0 0 k
    let hi := liftBitC s0 0 1 k
    let x := domC beta2 (Coordinate.zero 8) 0 lo
    addC (addC (word0 lo) (mulC (mulC (addC x alpha) (addC (word0 lo) (word0 hi))) pinv)) delta
  let k0 : AdditiveFriLevels 2 1 := fun _ => 0
  let k1 : AdditiveFriLevels 2 1 := fun _ => 1
  let x0 := domC beta2 (Coordinate.zero 8) 1 k0
  let x1 := domC beta2 (Coordinate.zero 8) 1 k1
  let c1 := mulC (addC (word1 k0) (word1 k1)) (invC (addC x0 x1))
  let c0 := addC (word1 k0) (mulC c1 x0)
  let coeffs := [c0, c1]
  let root1 := lastRootC beta2 (Coordinate.zero 8) 1 coeffs
  let roots : Fin 2 → Digest := ![root0, root1]
  let honestSeed := fun a =>
    seedC s0 pins (stub roots (fun _ => alpha) zeroSeed (fun _ => zeroOpening) coeffs) a
  let seeds := if seedBad then fun a => flipSeed (honestSeed a) else honestSeed
  let col1 : (Fin (2 - 1) → Bool) → C8 := fun address =>
    evalCoeffs coeffs (domC beta2 (Coordinate.zero 8) 1
      ((additiveFriLevelEquivPowerTwo 2 1).symm (binaryCubeIndexEquiv (2 - 1) address)))
  let op : Fin 2 → FriQueryOpening C8 (List UInt8) (List UInt8) := fun a =>
    let k : AdditiveFriLevels 2 1 := additiveCoherentRound s0.rounds_le 0 seeds a
    let lo := liftBitC s0 0 0 k
    let hi := liftBitC s0 0 1 k
    { left := word0 lo
      right := word0 hi
      next := evalCoeffs coeffs (domC beta2 (Coordinate.zero 8) 1 k)
      leftPath := path0 lo
      rightPath := path0 hi
      nextPath := merkleDomainsC.proofCodec.encode
        (cubePath merkleDomainsC codecC col1
          (binaryAddressBits (2 - 1) (additiveFriLevelEquivPowerTwo 2 1 k))) }
  stub roots (fun _ => alpha) seeds op coeffs

/-! ## Per-clause views, for attributing each mutant's rejection -/

def challengeClause (s : CStatement 2 1) (pins : TranscriptPins) (r : CReceipt 2 1 2) : Bool :=
  decide (∀ j, r.challenges j = challengeC s pins r j)

def seedClause (s : CStatement 2 1) (pins : TranscriptPins) (r : CReceipt 2 1 2) : Bool :=
  decide (∀ a, r.querySeed a = seedC s pins r a)

def openedClause (s : CStatement 2 1) (r : CReceipt 2 1 2) : Bool :=
  decide (∀ (j : Fin 1) (a : Fin 2),
    openedC s r j (additiveCoherentRound s.rounds_le j r.querySeed a) (r.opening j a) = true)

/-! ## Teeth -/

-- The prover's inverse is an inverse at the round pivot.
#guard mulC (pivotC beta2 0) (invC (pivotC beta2 0)) == Coordinate.one 8

-- The honest one-fold receipt is accepted, with every clause exercised.
#guard check s0 bootstrapPins (prove bootstrapPins none false (Coordinate.zero 8))

-- Wrong challenge, used consistently: only the challenge clause fails.
#guard
  let r := prove bootstrapPins (some (Coordinate.one 8)) false (Coordinate.zero 8)
  !check s0 bootstrapPins r && !challengeClause s0 bootstrapPins r &&
    seedClause s0 bootstrapPins r && openedClause s0 r

-- Wrong query positions, opened consistently: only the seed clause fails.
#guard
  let r := prove bootstrapPins none true (Coordinate.zero 8)
  !check s0 bootstrapPins r && challengeClause s0 bootstrapPins r &&
    !seedClause s0 bootstrapPins r && openedClause s0 r

-- A committed level-1 word off the fold by a constant: every Merkle opening verifies, the
-- final polynomial matches its root, and only the fold equation fails.
#guard
  let r := prove bootstrapPins none false (Coordinate.one 8)
  !check s0 bootstrapPins r && challengeClause s0 bootstrapPins r &&
    seedClause s0 bootstrapPins r && !openedClause s0 r

end Minidregg.Compiler.Tower256SuccinctHonestRun
