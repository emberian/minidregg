/-
# `Compiler/AirRange.lean` — [AIR-range]: the range-check gadget, DERIVED through the DSL

Note-spend values and amounts are RANGE-BOUNDED (`x ∈ [0, 2^k)`); the standard
arithmetization is bit-decomposition: `k` boolean wires plus one recomposition constraint.
This file grows that gadget on the `Compiler/Air` rung.

**Substrate, said out loud: this is Lean-authored arithmetization.** Every constraint here is
a `Term (AirSig F Idx)` built from the DSL surface (`vr`/`cst`/`add'`/`mul'`) and read through
the one fold (`eval = fold evalAlg`); the gadget is a LIST of such assertions
(`ConstraintSystem`), and its meaning comes from rung 1's initiality keystone
(`accepts_iff_semHolds`, lifted to systems below) plus `boolGadget_correct` — reused, never
re-derived. NO constraint is hand-authored outside the DSL: no Rust, no bespoke
`air_accepts`, no parallel executor.

## The construction

`x ∈ [0, 2^k)` iff there are bits `b₀ … b_{k−1}`, each boolean, with `x = Σᵢ bᵢ·2ⁱ`. The
gadget over wire indices (`xi` the value wire, `bits i` the bit wires) is the system

* `boolGadget (bits i)` for each `i < k` — booleanity `bᵢ·(bᵢ−1) ≐ 0`, rung 1's gadget;
* `recompTerm xi bits` — the recomposition `Σᵢ vr (bits i)·2ⁱ − vr xi ≐ 0`, the weighted sum
  built by folding DSL constructors over `List.finRange k`.

## Statement-first (the ATLAS fields)

* `rangeGadget_correct` — the keystone iff: the system accepts `asg` **iff** every bit wire
  is boolean AND `asg xi = Σᵢ asg (bits i)·2ⁱ`. The gadget means
  boolean-decomposition-summing-to-x — nothing more, nothing less.
* `rangeGadget_bounds` — the range reading, honest general form: an accepted `asg xi` equals
  the field CAST of an integer `n < 2^k`. Over a field of characteristic `≤ 2^k` that cast is
  lossy, so this is the sharpest field-generic statement that is TRUE.
* `rangeGadget_val_lt` — the integer lift, CLOSED for prime fields: over `ZMod p` with
  `2^k ≤ p`, acceptance forces `(asg xi).val < 2^k` — the genuine integer bound. The would-be
  `[AIR-range-lift]` residual closes here; what remains for other fields is not a proof gap
  but a real property (in characteristic `≤ 2^k` no integer reading exists — deployment must
  pick `k` with `2^k ≤ p`, and the hypothesis says so on the label).
* `rangeGadget_complete` — premise-inhabitation: EVERY `n < 2^k` is accepted by some
  assignment (its binary digits), so the intended range is inhabited wholesale, not sampled.
* Keystone witnesses, BUILT over `ZMod 11` (`2^3 ≤ 11`): satisfiable (`x = 5`, bits
  `(1,0,1)`, computed); teeth — a non-boolean bit is rejected EVEN WHEN the recomposition
  holds (booleanity is load-bearing), an all-boolean wrong recomposition is rejected
  (recomposition is load-bearing), and at `k = 2` NO bit assignment whatsoever makes `x = 5`
  accepted (the range genuinely bounds).

Residuals unchanged upstream: `[AIR-sumcheck]`, `[AIR-poseidon]`, `[AIR-membership]`.
-/
import Compiler.Air
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u} {k : ℕ}

/-! ## §1. Constraint systems — a gadget is a LIST of assertions, each read `t ≐ 0`. -/

/-- A constraint SYSTEM: finitely many DSL assertions, the conjunction of their `= 0`
readings. Gadgets compose by list append. -/
abbrev ConstraintSystem (F : Type u) (Idx : Type u) : Type u :=
  List (Term (AirSig F Idx))

/-- The CIRCUIT reading of a system: every assertion accepts. -/
def systemAccepts (asg : Idx → F) (sys : ConstraintSystem F Idx) : Prop :=
  ∀ t ∈ sys, accepts asg t

/-- The EXECUTOR reading of a system: every assertion's semantic relation holds. -/
def systemSemHolds (asg : Idx → F) (sys : ConstraintSystem F Idx) : Prop :=
  ∀ t ∈ sys, semHolds asg t

/-- Rung 1's drift-impossibility lifted to systems: the circuit reading IS the executor
reading, pointwise `accepts_iff_semHolds` — no new induction, no new trust. -/
theorem systemAccepts_iff_systemSemHolds (asg : Idx → F) (sys : ConstraintSystem F Idx) :
    systemAccepts asg sys ↔ systemSemHolds asg sys :=
  forall_congr' fun t => imp_congr_right fun _ => accepts_iff_semHolds asg t

/-- Acceptance of one assertion computes (`F` with decidable equality) — keystones below are
`decide`d against the REAL fold, not a hand mirror. -/
instance (asg : Idx → F) (t : Term (AirSig F Idx)) [DecidableEq F] :
    Decidable (accepts asg t) :=
  inferInstanceAs (Decidable (eval asg t = 0))

instance (asg : Idx → F) (sys : ConstraintSystem F Idx) [DecidableEq F] :
    Decidable (systemAccepts asg sys) :=
  inferInstanceAs (Decidable (∀ t ∈ sys, accepts asg t))

/-! ## §2. Computation rules — `eval` on the DSL surface, all definitional (`fold_mk` is
`rfl`, so the circuit reading of each constructor is a `rfl` too). -/

@[simp] theorem eval_cst (asg : Idx → F) (c : F) :
    eval asg (cst c (Idx := Idx)) = c := rfl

@[simp] theorem eval_vr (asg : Idx → F) (i : Idx) :
    eval asg (vr i (F := F)) = asg i := rfl

@[simp] theorem eval_add' (asg : Idx → F) (a b : Term (AirSig F Idx)) :
    eval asg (add' a b) = eval asg a + eval asg b := rfl

@[simp] theorem eval_mul' (asg : Idx → F) (a b : Term (AirSig F Idx)) :
    eval asg (mul' a b) = eval asg a * eval asg b := rfl

/-! ## §3. The recomposition assertion — `Σᵢ vr (bits i)·2ⁱ − vr xi ≐ 0`. -/

/-- The weighted-sum EXPRESSION `Σᵢ vr (bits i)·2ⁱ`, built by folding DSL constructors over
`List.finRange k` — a term of the DSL, evaluated only through the one fold. -/
def weightedSum (bits : Fin k → Idx) : Term (AirSig F Idx) :=
  (List.finRange k).foldr
    (fun i acc => add' (mul' (vr (bits i)) (cst ((2 : F) ^ (i : ℕ)))) acc) (cst 0)

/-- The recomposition assertion: `weightedSum bits + (−1)·vr xi ≐ 0`, i.e.
`Σᵢ bᵢ·2ⁱ − x = 0`. -/
def recompTerm (xi : Idx) (bits : Fin k → Idx) : Term (AirSig F Idx) :=
  add' (weightedSum bits) (mul' (cst (-1)) (vr xi))

private theorem eval_weightedFold (asg : Idx → F) (bits : Fin k → Idx) :
    ∀ l : List (Fin k),
      eval asg (l.foldr
          (fun i acc => add' (mul' (vr (bits i)) (cst ((2 : F) ^ (i : ℕ)))) acc) (cst 0))
        = (l.map fun i => asg (bits i) * (2 : F) ^ (i : ℕ)).sum
  | [] => by simp
  | i :: l => by simp [eval_weightedFold asg bits l]

/-- The circuit reads `weightedSum` as the big-operator sum. -/
theorem eval_weightedSum (asg : Idx → F) (bits : Fin k → Idx) :
    eval asg (weightedSum bits) = ∑ i : Fin k, asg (bits i) * (2 : F) ^ (i : ℕ) := by
  unfold weightedSum
  rw [eval_weightedFold, Fin.sum_univ_def]

/-- The recomposition assertion MEANS recomposition: it accepts iff
`asg xi = Σᵢ asg (bits i)·2ⁱ`. -/
theorem recompTerm_correct (asg : Idx → F) (xi : Idx) (bits : Fin k → Idx) :
    accepts asg (recompTerm xi bits) ↔
      asg xi = ∑ i : Fin k, asg (bits i) * (2 : F) ^ (i : ℕ) := by
  unfold accepts recompTerm
  rw [eval_add', eval_mul', eval_cst, eval_vr, eval_weightedSum, neg_one_mul,
    add_neg_eq_zero]
  exact eq_comm

/-! ## §4. The range gadget and its keystone iff. -/

/-- **The range gadget** `[AIR-range]`: `k` booleanity assertions (rung 1's `boolGadget`,
reused) plus the recomposition assertion — all DSL terms, composed as a system. -/
def rangeGadget (xi : Idx) (bits : Fin k → Idx) : ConstraintSystem F Idx :=
  ((List.finRange k).map fun i => boolGadget (bits i)) ++ [recompTerm xi bits]

/-- **The keystone iff — the gadget means boolean-decomposition-summing-to-x.** The system
accepts `asg` iff every bit wire is `0` or `1` AND `asg xi = Σᵢ asg (bits i)·2ⁱ`. Derived:
`boolGadget_correct` for the bit assertions, `recompTerm_correct` for the recomposition —
no bespoke soundness argument, no new induction. -/
theorem rangeGadget_correct (asg : Idx → F) (xi : Idx) (bits : Fin k → Idx) :
    systemAccepts asg (rangeGadget xi bits) ↔
      ((∀ i, asg (bits i) = 0 ∨ asg (bits i) = 1) ∧
        asg xi = ∑ i : Fin k, asg (bits i) * (2 : F) ^ (i : ℕ)) := by
  unfold systemAccepts rangeGadget
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · exact (boolGadget_correct asg (bits i)).mp
        (h _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))
    · exact (recompTerm_correct asg xi bits).mp
        (h _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · rintro ⟨hbool, hsum⟩ t ht
    rcases List.mem_append.mp ht with ht' | ht'
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht'
      exact (boolGadget_correct asg (bits i)).mpr (hbool i)
    · rw [List.mem_singleton.mp ht']
      exact (recompTerm_correct asg xi bits).mpr hsum

/-- The EXECUTOR reading of the keystone, via rung 1's initiality: the semantic relation of
the range system is the same boolean-decomposition statement — `accepts_iff_semHolds` doing
the load-bearing transfer. -/
theorem rangeGadget_semHolds_correct (asg : Idx → F) (xi : Idx) (bits : Fin k → Idx) :
    systemSemHolds asg (rangeGadget xi bits) ↔
      ((∀ i, asg (bits i) = 0 ∨ asg (bits i) = 1) ∧
        asg xi = ∑ i : Fin k, asg (bits i) * (2 : F) ^ (i : ℕ)) := by
  rw [← systemAccepts_iff_systemSemHolds, rangeGadget_correct]

/-! ## §5. The RANGE reading — accepted values are (casts of) `k`-bit integers. -/

/-- A sum of `k` boolean·`2ⁱ` terms is `< 2^k` — the arithmetic heart of the range bound,
over `ℕ` where "range" genuinely means order. -/
theorem boolDigit_sum_lt : ∀ {k : ℕ} (d : Fin k → ℕ), (∀ i, d i ≤ 1) →
    ∑ i : Fin k, d i * 2 ^ (i : ℕ) < 2 ^ k := by
  intro k
  induction k with
  | zero => intro d _; simp
  | succ m ih =>
    intro d hd
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have h1 : ∑ i : Fin m, d i.castSucc * 2 ^ (i : ℕ) < 2 ^ m :=
      ih (fun i => d i.castSucc) fun i => hd _
    have h2 : d (Fin.last m) * 2 ^ m ≤ 2 ^ m :=
      calc d (Fin.last m) * 2 ^ m ≤ 1 * 2 ^ m := Nat.mul_le_mul_right _ (hd _)
        _ = 2 ^ m := one_mul _
    have h3 : (2 : ℕ) ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
    omega

/-- **The range bound, honest general form**: an accepted `asg xi` equals the field cast of
an integer `n < 2^k`. This is the sharpest TRUE field-generic statement — over a field of
characteristic `≤ 2^k` the cast collides, so "x < 2^k as an integer" is only meaningful
after a lift; `rangeGadget_val_lt` closes that lift where it exists (prime field,
`2^k ≤ p`). -/
theorem rangeGadget_bounds (asg : Idx → F) (xi : Idx) (bits : Fin k → Idx)
    (h : systemAccepts asg (rangeGadget xi bits)) :
    ∃ n : ℕ, n < 2 ^ k ∧ asg xi = (n : F) := by
  classical
  obtain ⟨hbool, hsum⟩ := (rangeGadget_correct asg xi bits).mp h
  refine ⟨∑ i : Fin k, (if asg (bits i) = 1 then 1 else 0) * 2 ^ (i : ℕ), ?_, ?_⟩
  · exact boolDigit_sum_lt _ fun i => by split <;> omega
  · rw [hsum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hbool i with h0 | h1
    · simp [h0]
    · simp [h1]

/-- **The integer lift, CLOSED for prime fields**: over `ZMod p` with `2^k ≤ p`, acceptance
forces `(asg xi).val < 2^k` — the genuine integer range bound, the form a deployment quotes
(and the `2^k ≤ p` hypothesis is the parameter constraint on the label). -/
theorem rangeGadget_val_lt {p : ℕ} [Fact p.Prime] (hp : 2 ^ k ≤ p)
    {Idx : Type} (asg : Idx → ZMod p) (xi : Idx) (bits : Fin k → Idx)
    (h : systemAccepts asg (rangeGadget xi bits)) :
    (asg xi).val < 2 ^ k := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨n, hn, hcast⟩ := rangeGadget_bounds asg xi bits h
  rw [hcast, ZMod.val_cast_of_lt (lt_of_lt_of_le hn hp)]
  exact hn

/-! ## §6. Completeness — every `k`-bit integer IS accepted (premise-inhabitation). -/

/-- Every `n < 2^k` has a boolean digit decomposition over `ℕ` — binary digits, by
induction on `k` (low bit `n % 2`, rest from `n / 2`). -/
theorem exists_boolDigits : ∀ {k : ℕ} (n : ℕ), n < 2 ^ k →
    ∃ d : Fin k → ℕ, (∀ i, d i ≤ 1) ∧ n = ∑ i : Fin k, d i * 2 ^ (i : ℕ) := by
  intro k
  induction k with
  | zero =>
    intro n hn
    exact ⟨fun i => i.elim0, fun i => i.elim0, by simpa using Nat.lt_one_iff.mp hn⟩
  | succ m ih =>
    intro n hn
    obtain ⟨d, hd, hsum⟩ := ih (n / 2) (by have := pow_succ 2 m; omega)
    refine ⟨Fin.cases (n % 2) d, ?_, ?_⟩
    · refine Fin.cases ?_ ?_
      · simp only [Fin.cases_zero]; omega
      · intro j; simpa using hd j
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, Fin.val_zero, pow_zero, mul_one,
        Fin.val_succ]
      have hshift : ∑ j : Fin m, d j * 2 ^ ((j : ℕ) + 1)
          = (∑ j : Fin m, d j * 2 ^ (j : ℕ)) * 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
      rw [hshift, ← hsum]
      omega

/-- Every `n < 2^k` has a boolean decomposition IN THE FIELD — the reusable
premise-inhabitation form: a caller with concrete wire indices builds its accepting
assignment from these `b` values via `rangeGadget_correct.mpr`. -/
theorem exists_boolDecomp (n : ℕ) (hn : n < 2 ^ k) :
    ∃ b : Fin k → F, (∀ i, b i = 0 ∨ b i = 1) ∧
      (n : F) = ∑ i : Fin k, b i * (2 : F) ^ (i : ℕ) := by
  obtain ⟨d, hd, hsum⟩ := exists_boolDigits n hn
  refine ⟨fun i => (d i : F), fun i => ?_, ?_⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hd i) with h | h <;> simp [h]
  · rw [hsum]; push_cast; rfl

/-- **Completeness / premise-inhabitation, assignment form**: on the canonical wire index
(`none` the value wire, `some i` the bit wires, `ULift`ed to stay universe-general), every
`n < 2^k` is accepted by SOME assignment carrying `n` on the value wire. The intended range
is inhabited wholesale — the iff of `rangeGadget_correct` has teeth in BOTH directions. -/
theorem rangeGadget_complete (n : ℕ) (hn : n < 2 ^ k) :
    ∃ asg : Option (ULift.{u} (Fin k)) → F, asg none = (n : F) ∧
      systemAccepts asg (rangeGadget none (fun i => some (ULift.up i))) := by
  obtain ⟨b, hb, hsum⟩ := exists_boolDecomp (F := F) n hn
  refine ⟨fun o => match o with
    | none => (n : F)
    | some i => b i.down, rfl, ?_⟩
  rw [rangeGadget_correct]
  exact ⟨fun i => hb i, hsum⟩

/-! ## §7. Keystone witnesses — BUILT over `ZMod 11` (`2^3 = 8 ≤ 11`), all computing against
the REAL fold via the `Decidable` instances of §1. -/

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Keystone wire assignment on the canonical index `Option (Fin k)`: `none` is the value
wire, `some i` the `i`-th bit wire. -/
def keyAsg (x : ZMod 11) (b : Fin k → ZMod 11) : Option (Fin k) → ZMod 11 :=
  fun o => match o with
  | none => x
  | some i => b i

/-- *Satisfiable, computed*: `x = 5` with bits `(1,0,1)` (`5 = 1 + 4`) accepts at `k = 3`. -/
example : systemAccepts (keyAsg 5 ![1, 0, 1]) (rangeGadget none some) := by decide

/-- *Teeth (booleanity is load-bearing), computed*: bits `(3,1,0)` RECOMPOSE to `5`
(`3 + 2 = 5`) but bit 0 is non-boolean — REJECTED. The boolean constraints are not implied
by the recomposition. -/
example : ¬ systemAccepts (keyAsg 5 ![3, 1, 0]) (rangeGadget none some) := by decide

/-- *…and the attribution is machine-checked, not asserted*: the recomposition assertion
ALONE accepts `(3,1,0)` — so the rejection above is booleanity's doing. -/
example : accepts (keyAsg 5 ![3, 1, 0]) (recompTerm none some) := by decide

/-- *Teeth (recomposition is load-bearing), computed*: all-boolean bits `(1,1,1)` sum to
`7 ≠ 5` — REJECTED. -/
example : ¬ systemAccepts (keyAsg 5 ![1, 1, 1]) (rangeGadget none some) := by decide

/-- *…attribution machine-checked again*: every booleanity assertion ALONE accepts
`(1,1,1)` — the rejection above is the recomposition's doing. -/
example : ∀ i : Fin 3, accepts (keyAsg 5 ![1, 1, 1]) (boolGadget (some i)) := by decide

/-- *Range teeth*: at `k = 2`, NO bit assignment whatsoever makes `x = 5` accepted — `5` is
genuinely outside `[0, 4)`, quantified over every possible bit witness. -/
example : ¬ ∃ b : Fin 2 → ZMod 11, systemAccepts (keyAsg 5 b) (rangeGadget none some) := by
  rintro ⟨b, hb⟩
  obtain ⟨hbool, hsum⟩ := (rangeGadget_correct _ _ _).mp hb
  have h0 := hbool 0
  have h1 := hbool 1
  rw [Fin.sum_univ_two] at hsum
  simp only [keyAsg] at h0 h1 hsum
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] at hsum <;>
    revert hsum <;> decide

/-- *The integer lift, instantiated*: any accepted assignment at `k = 3` over `ZMod 11`
carries a genuine 3-bit integer on the value wire. -/
example (asg : Option (Fin 3) → ZMod 11)
    (h : systemAccepts asg (rangeGadget none some)) : (asg none).val < 2 ^ 3 :=
  rangeGadget_val_lt (by norm_num) asg none some h

/-- *Completeness, instantiated*: every `n < 8` is accepted at `k = 3` — usable downstream
without picking digits by hand. -/
example (n : ℕ) (hn : n < 2 ^ 3) :
    ∃ asg : Option (ULift (Fin 3)) → ZMod 11, asg none = (n : ZMod 11) ∧
      systemAccepts asg (rangeGadget none (fun i => some (ULift.up i))) :=
  rangeGadget_complete n hn

/-! ### Honest scope — what is proved, and what the field/integer boundary really is

The gadget-level iff (`rangeGadget_correct`) and both range directions
(`rangeGadget_bounds` sound, `rangeGadget_complete` complete) are theorems over any field.
The INTEGER reading `x < 2^k` is proved as `rangeGadget_val_lt` for `ZMod p` under the
explicit parameter constraint `2^k ≤ p` — that hypothesis is not a weakness to hide but the
deployment label: pick the field so the range fits, or the bound does not exist (in
characteristic `c ≤ 2^k` the weights `2ⁱ` collapse modulo `c` — e.g. in characteristic 2
every weight above `2⁰` vanishes and the gadget only pins `x ∈ {0, 1}` — so there is no
integer reading of `x < 2^k` to prove; the cast statement `rangeGadget_bounds` is the sharp
one).
`[AIR-range-lift]` is thereby CLOSED, not residual. Residuals unchanged upstream:
`[AIR-sumcheck]` (retire the emitted constraints through `Loom/SumcheckReduction`),
`[AIR-poseidon]`/`[AIR-membership]` (the note-spend gadgets, grown on this rung — range now
available for their amount wires). -/

end Minidregg.Compiler
