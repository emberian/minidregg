/-
# Compiler.Tower256FinalPolynomialCheck -- the final-polynomial clause, decided computably

`Tower256AdditiveFriRawController.Accepts` ends with two clauses about
`receipt.finalPolynomial : Polynomial Tower256`: its degree is below `statement.degree m`, and
it agrees with the last committed word at every domain point. `Polynomial Tower256` and the
field `Tower256` are both noncomputable, so neither clause can be checked by running Lean.

Here the final polynomial travels as a coefficient list over `Coordinate 8`. `finalCheck` is a
`Bool` function over coordinates that runs in the kernel and in compiled code, using
`Coordinate.add` and `Coordinate.mul` from `Theory.BinaryTowerCoordinateArith`.

* `finalCheck_iff`: `finalCheck` is true exactly when the list fits the degree bound and the
  polynomial it denotes takes every listed value.
* `finalClauses_of_finalCheck`: when the listed points cover the domain and denote the
  statement's domain and word, a `true` check gives `Accepts`' last two clauses for the
  polynomial the list denotes.
* `finalCheck_of_finalClauses`: the converse, so an honest receipt passes.

The domain points and word values enter as coordinates together with their denotations. Making
those data rather than functions is the succinct-statement step, which this file does not do.
-/

import Theory.BinaryTowerCoordinateArith
import Compiler.Tower256AdditiveFriRawController

namespace Minidregg.Compiler.Tower256FinalPolynomialCheck

open Polynomial
open Minidregg.Theory
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate coordinateFieldEquiv
  coordinateFieldEquiv_add coordinateFieldEquiv_mul coordinateFieldEquiv_zero)
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256AdditiveFriRawController

set_option autoImplicit false

/-- A Tower256 element in Fan--Paar coordinates. -/
abbrev C8 := Coordinate 8

/-- The denotation of a coordinate. -/
noncomputable abbrev toField : C8 ≃ Tower256 := coordinateFieldEquiv 8

/-! ## Coefficient lists and the polynomials they denote -/

/-- The polynomial with the given coefficients, constant term first. -/
noncomputable def polyOf : List Tower256 → Polynomial Tower256
  | [] => 0
  | c :: cs => C c + X * polyOf cs

theorem coeff_polyOf : ∀ (cs : List Tower256) (n : Nat), (polyOf cs).coeff n = cs.getD n 0
  | [], n => by simp only [polyOf, coeff_zero, List.getD_nil]
  | c :: cs, 0 => by
      simp only [polyOf, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero, List.getD_cons_zero]
  | c :: cs, n + 1 => by
      simp only [polyOf, coeff_add, coeff_C_succ, coeff_X_mul, zero_add, List.getD_cons_succ,
        coeff_polyOf cs n]

theorem degree_polyOf_lt (cs : List Tower256) : (polyOf cs).degree < cs.length := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_polyOf, List.getD_eq_getElem?_getD, List.getElem?_eq_none hn, Option.getD_none]

theorem eval_polyOf (x : Tower256) :
    ∀ cs : List Tower256, (polyOf cs).eval x = cs.foldr (fun c acc => c + x * acc) 0
  | [] => by simp only [polyOf, eval_zero, List.foldr_nil]
  | c :: cs => by
      simp only [polyOf, eval_add, eval_C, eval_mul, eval_X, List.foldr_cons, eval_polyOf x cs]

/-! ## The computable evaluation -/

/-- Horner evaluation over coordinates. -/
def evalCoeffs (cs : List C8) (x : C8) : C8 :=
  cs.foldr (fun c acc => Coordinate.add 8 c (Coordinate.mul 8 x acc)) (Coordinate.zero 8)

theorem toField_evalCoeffs (x : C8) :
    ∀ cs : List C8, toField (evalCoeffs cs x) = (polyOf (cs.map toField)).eval (toField x)
  | [] => by simp [evalCoeffs, polyOf, toField, coordinateFieldEquiv_zero]
  | c :: cs => by
      have ih := toField_evalCoeffs x cs
      simp only [evalCoeffs, List.foldr_cons] at ih ⊢
      rw [coordinateFieldEquiv_add, coordinateFieldEquiv_mul, ih]
      simp [polyOf]

/-- **The checker.** The coefficient list fits the degree bound and takes every listed value. -/
def finalCheck (cs : List C8) (degreeBound : Nat) (points : List (C8 × C8)) : Bool :=
  decide (cs.length ≤ degreeBound) && points.all fun p => evalCoeffs cs p.1 == p.2

theorem finalCheck_iff (cs : List C8) (degreeBound : Nat) (points : List (C8 × C8)) :
    finalCheck cs degreeBound points = true ↔
      cs.length ≤ degreeBound ∧
        ∀ p ∈ points, (polyOf (cs.map toField)).eval (toField p.1) = toField p.2 := by
  simp only [finalCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
  refine and_congr Iff.rfl (forall₂_congr fun p _ => ?_)
  rw [← toField_evalCoeffs, Equiv.apply_eq_iff_eq]

/-! ## The tie to `Accepts`' final clauses -/

variable {ell m queryCount : Nat}

/-- A `true` check gives the two final clauses of `Accepts` for the polynomial the coefficient
list denotes, once the listed points cover the domain with their true denotations. -/
theorem finalClauses_of_finalCheck (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (receipt : Receipt ell m queryCount) (cs : List C8) (points : List (C8 × C8))
    (hpoly : receipt.finalPolynomial = polyOf (cs.map toField))
    (hcover : ∀ point, ∃ p ∈ points, toField p.1 = statement.tower.dom m point ∧
      toField p.2 = statement.transcript.wordAt receipt.challenges m le_rfl point)
    (hcheck : finalCheck cs (statement.degree m) points = true) :
    receipt.finalPolynomial.degree < (statement.degree m : WithBot Nat) ∧
      ∀ point, statement.transcript.wordAt receipt.challenges m le_rfl point =
        receipt.finalPolynomial.eval (statement.tower.dom m point) := by
  obtain ⟨hlen, hvals⟩ := (finalCheck_iff cs _ points).mp hcheck
  refine ⟨?_, fun point => ?_⟩
  · rw [hpoly]
    refine lt_of_lt_of_le (degree_polyOf_lt _) ?_
    rw [List.length_map]
    exact_mod_cast hlen
  · obtain ⟨p, hp, hdom, hword⟩ := hcover point
    rw [← hword, ← hdom, hpoly, hvals p hp]

/-- Completeness: an honest final polynomial passes, at any listing of honest points. -/
theorem finalCheck_of_finalClauses (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (receipt : Receipt ell m queryCount) (cs : List C8) (points : List (C8 × C8))
    (hpoly : receipt.finalPolynomial = polyOf (cs.map toField))
    (hlen : cs.length ≤ statement.degree m)
    (hhonest : ∀ p ∈ points, ∃ point, toField p.1 = statement.tower.dom m point ∧
      toField p.2 = statement.transcript.wordAt receipt.challenges m le_rfl point)
    (hagree : ∀ point, statement.transcript.wordAt receipt.challenges m le_rfl point =
        receipt.finalPolynomial.eval (statement.tower.dom m point)) :
    finalCheck cs (statement.degree m) points = true := by
  refine (finalCheck_iff cs _ points).mpr ⟨hlen, fun p hp => ?_⟩
  obtain ⟨point, hdom, hword⟩ := hhonest p hp
  rw [hdom, hword, hagree point, hpoly]

/-! ## Kernel-evaluated instances

The deployment witness `Tower256AdditiveFriRawDeployment` commits the zero word at degree
bound 1: the empty coefficient list passes at a zero value and fails at a nonzero one. The
positive instance is the degree-1 polynomial `1 + g·X` (`g = fpGen 7`, bit 128) at `X = 1`,
which exercises `Coordinate.mul` at level 8. -/

/-- The bootstrap shape: zero polynomial, degree bound 1, zero word. -/
example : finalCheck [] 1 [(Coordinate.one 8, Coordinate.zero 8)] = true := by decide

/-- The same shape rejects a nonzero claimed value. -/
example : finalCheck [] 1 [(Coordinate.one 8, Coordinate.one 8)] = false := by decide

-- A degree-1 polynomial whose evaluation needs a level-8 product. Evaluated, not kernel-reduced:
-- `decide +kernel` here made the kernel unfold a level-8 Fan--Paar product (3^8 leaf products
-- over tree data), the module's whole memory peak.
#guard finalCheck [Coordinate.one 8, Coordinate.topGenerator 7] 2
    [(Coordinate.one 8, Coordinate.add 8 (Coordinate.one 8) (Coordinate.topGenerator 7))]

/-- The degree bound has teeth: the same list fails at bound 1. -/
example : finalCheck [Coordinate.one 8, Coordinate.topGenerator 7] 1 [] = false := by decide

/-- info: 'Minidregg.Compiler.Tower256FinalPolynomialCheck.finalCheck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finalCheck_iff
/-- info: 'Minidregg.Compiler.Tower256FinalPolynomialCheck.finalClauses_of_finalCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finalClauses_of_finalCheck
/-- info: 'Minidregg.Compiler.Tower256FinalPolynomialCheck.finalCheck_of_finalClauses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finalCheck_of_finalClauses

end Minidregg.Compiler.Tower256FinalPolynomialCheck
