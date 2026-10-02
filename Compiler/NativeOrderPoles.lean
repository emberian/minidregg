/-
# Poles of the wide native order comparison, on concrete laws

Every fact below is kernel-checked (`decide`, or a theorem applied to `decide`d
premises). The clock value is the one CLOCK-SUBJECT's run r1 refused at:
`clock/now = 1,790,846,960`.

* The KC row-13 read law over a field holding 200 or 0: in range at width 125,
  admitted by `eval`, hence by the compiled law; at width 29 it was out of range,
  and the refusal now names clause 1 and its two values.
* A cooldown clause (`field 3 <= clock/now`): admitted when the cooldown is over,
  refused (by `eval`, so by the compiled law) when it is not — the verdict `eval`
  gives, at real unix time.
* Two balances `10^12` apart, both orders.
* The edges: the two extremes of `R`, decided; a difference of `2^125 - 1`, in
  range; a difference of `2^125`, refused, naming the clause and its two values.
* A pair delta of `2^127` has the field image of `1` and is named; `R` never aliases.
-/
import Compiler.NativeHostProfile
import Compiler.PredRangeLeaf

namespace Minidregg.Compiler.NativeOrderPoles

open Minidregg.Pred
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostProfile

set_option autoImplicit false

/-- `clock/now` when CLOCK-SUBJECT's r1 refused 20 of 20 reads. -/
def wallNow : Int := 1790846960

/-! ## The KC row-13 read law at real unix time -/

/-- `any [ verb == write, field 1 <= clock/now + 0 ]`. -/
def readLaw : Pred := Pred.any [.eq "request/verb" 2, .leSlotsOff "resource/field/1/after" "clock/now" 0]

/-- A read (verb 1) of a resource whose field 1 holds `field`, judged at `now`. -/
def readAt (field now : Int) : State :=
  ⟨[("request/verb", 1), ("resource/field/1/before", field),
    ("resource/field/1/after", field), ("clock/now", now)]⟩

theorem read200_in_range :
    inputsInRange (.scalar orderWidth) readLaw (readAt 200 wallNow) (readAt 200 wallNow) = true := by
  decide

/-- What r1 hit: at the old width the same read was out of range. -/
theorem read200_out_of_range_at_29 :
    inputsInRange (.scalar 29) readLaw (readAt 200 wallNow) (readAt 200 wallNow) = false := by
  decide

/-- And at the old width it would now be refused naming the clause and both values. -/
theorem read200_named_at_29 :
    LawLeaf.ofRange (.scalar 29) readLaw (readAt 200 wallNow) (readAt 200 wallNow) =
      some ⟨[1], .leSlotsOff "resource/field/1/after" "clock/now" 0, some 200, some wallNow⟩ := by
  decide

theorem read200_eval : Minidregg.Pred.eval readLaw (readAt 200 wallNow) (readAt 200 wallNow) = true := by decide

theorem read200_admitted :
    ∃ A : List ℕ → ℕ → Field,
      systemAccepts (stepAsg (readAt 200 wallNow) (readAt 200 wallNow) A)
        (lower (.scalar orderWidth) readLaw) :=
  (order_agrees_with_eval_on_R (by decide) (by decide)).mpr read200_eval

theorem read0_eval : Minidregg.Pred.eval readLaw (readAt 0 wallNow) (readAt 0 wallNow) = true := by decide

theorem read0_admitted :
    ∃ A : List ℕ → ℕ → Field,
      systemAccepts (stepAsg (readAt 0 wallNow) (readAt 0 wallNow) A)
        (lower (.scalar orderWidth) readLaw) :=
  (order_agrees_with_eval_on_R (by decide) (by decide)).mpr read0_eval

/-! ## A cooldown clause at real unix time -/

/-- `any [ not (verb == write), field 3 <= clock/now + 0 ]`: a write waits for field 3. -/
def cooldownLaw : Pred :=
  Pred.any [.not (.eq "request/verb" 2), .leSlotsOff "resource/field/3/after" "clock/now" 0]

def writeAt (ready now : Int) : State :=
  ⟨[("request/verb", 2), ("resource/field/3/before", ready),
    ("resource/field/3/after", ready), ("clock/now", now)]⟩

theorem cooldown_over_eval : Minidregg.Pred.eval cooldownLaw (writeAt 0 wallNow) (writeAt 0 wallNow) = true := by
  decide

theorem cooldown_over_admitted :
    ∃ A : List ℕ → ℕ → Field,
      systemAccepts (stepAsg (writeAt 0 wallNow) (writeAt 0 wallNow) A)
        (lower (.scalar orderWidth) cooldownLaw) :=
  (order_agrees_with_eval_on_R (by decide) (by decide)).mpr cooldown_over_eval

theorem cooldown_pending_eval :
    Minidregg.Pred.eval cooldownLaw (writeAt (wallNow + 100) wallNow) (writeAt (wallNow + 100) wallNow) = false := by
  decide

/-- The pending cooldown is refused by the compiled law because `eval` refuses it, and
the law-denied refusal names the clause (`firstFailingLeaf`), not an input range. -/
theorem cooldown_pending_refused :
    ¬ ∃ A : List ℕ → ℕ → Field,
      systemAccepts (stepAsg (writeAt (wallNow + 100) wallNow) (writeAt (wallNow + 100) wallNow) A)
        (lower (.scalar orderWidth) cooldownLaw) := by
  rw [order_agrees_with_eval_on_R (by decide) (by decide), cooldown_pending_eval]
  decide

theorem cooldown_pending_named :
    firstFailingLeaf cooldownLaw (writeAt (wallNow + 100) wallNow)
        (writeAt (wallNow + 100) wallNow) = some [] ∧
      LawLeaf.ofRange (.scalar orderWidth) cooldownLaw (writeAt (wallNow + 100) wallNow)
        (writeAt (wallNow + 100) wallNow) = none := by
  decide

/-! ## Two balances `10^12` apart -/

/-- `field 0 <= field 1`. -/
def balanceLaw : Pred := .leSlots "resource/field/0/after" "resource/field/1/after"

def balances (a b : Int) : State :=
  ⟨[("request/verb", 2), ("resource/field/0/after", a), ("resource/field/1/after", b)]⟩

theorem balances_up_admitted :
    ∃ A : List ℕ → ℕ → Field,
      systemAccepts (stepAsg (balances 0 (10 ^ 12)) (balances 0 (10 ^ 12)) A)
        (lower (.scalar orderWidth) balanceLaw) :=
  (order_agrees_with_eval_on_R (by decide) (by decide)).mpr (by decide)

theorem balances_down_refused :
    ¬ ∃ A : List ℕ → ℕ → Field,
      systemAccepts (stepAsg (balances (10 ^ 12) 0) (balances (10 ^ 12) 0) A)
        (lower (.scalar orderWidth) balanceLaw) := by
  rw [order_agrees_with_eval_on_R (by decide) (by decide)]
  decide

theorem balances_out_of_range_at_29 :
    inputsInRange (.scalar 29) balanceLaw (balances 0 (10 ^ 12)) (balances 0 (10 ^ 12)) = false := by
  decide

/-! ## The edges -/

/-- The two extremes of `R` compared with each other, both ways: decided as `eval` decides. -/
theorem R_extremes_admitted :
    ∃ A : List ℕ → ℕ → Field,
      systemAccepts (stepAsg (balances (-rangeBound) (rangeBound - 1))
          (balances (-rangeBound) (rangeBound - 1)) A)
        (lower (.scalar orderWidth) balanceLaw) :=
  (order_agrees_with_eval_on_R (by decide) (by decide)).mpr (by decide)

theorem R_extremes_reversed_refused :
    ¬ ∃ A : List ℕ → ℕ → Field,
      systemAccepts (stepAsg (balances (rangeBound - 1) (-rangeBound))
          (balances (rangeBound - 1) (-rangeBound)) A)
        (lower (.scalar orderWidth) balanceLaw) := by
  rw [order_agrees_with_eval_on_R (by decide) (by decide)]
  decide

/-- One past `R` is no longer covered by `order_agrees_with_eval_on_R`'s premise. -/
theorem one_past_R : ¬ InR rangeBound := by decide

/-- A two-clause law: `verb == write; field 0 <= field 1`. -/
def edgeLaw : Pred := Pred.all [.eq "request/verb" 2, balanceLaw]

/-- The last difference the width decides is in range. -/
theorem width_edge_in_range :
    inputsInRange (.scalar orderWidth) edgeLaw (balances 0 (2 ^ 125 - 1))
      (balances 0 (2 ^ 125 - 1)) = true := by
  decide

/-- One past it refuses, naming clause 1 and the two values. -/
theorem width_edge_plus_one_named :
    LawLeaf.ofRange (.scalar orderWidth) edgeLaw (balances 0 (2 ^ 125)) (balances 0 (2 ^ 125)) =
      some ⟨[1], balanceLaw, some 0, some (2 ^ 125)⟩ := by
  decide

/-- The same past the lower edge. -/
theorem width_lower_edge_named :
    inputsInRange (.scalar orderWidth) edgeLaw (balances 0 (-(2 ^ 125)))
        (balances 0 (-(2 ^ 125))) = true ∧
      LawLeaf.ofRange (.scalar orderWidth) edgeLaw (balances 1 (-(2 ^ 125)))
        (balances 1 (-(2 ^ 125))) = some ⟨[1], balanceLaw, some 1, some (-(2 ^ 125))⟩ := by
  decide

/-! ## Two integers with one field image

A pair delta of `2 * 2^126 = 2^127` reads as `1` in `ZMod (2^127 - 1)`: the cast
check refuses such a step, and `castAlias` names the pair. Inside `R` it never does. -/

theorem pair_delta_aliases_one : castAlias Field [1, 2 ^ 127] ≠ none := by decide

theorem pair_delta_alias_named : castAlias Field [1, 2 ^ 127] = some (1, 2 ^ 127) := by decide

theorem R_never_aliases : castAlias Field [-rangeBound, rangeBound - 1, 0, 1, wallNow] = none := by
  decide

#assert_axioms pair_delta_alias_named
#assert_axioms R_never_aliases
#assert_axioms read200_admitted
#assert_axioms read200_named_at_29
#assert_axioms read0_admitted
#assert_axioms cooldown_over_admitted
#assert_axioms cooldown_pending_refused
#assert_axioms cooldown_pending_named
#assert_axioms balances_up_admitted
#assert_axioms balances_down_refused
#assert_axioms R_extremes_admitted
#assert_axioms R_extremes_reversed_refused
#assert_axioms width_edge_in_range
#assert_axioms width_edge_plus_one_named
#assert_axioms width_lower_edge_named

end Minidregg.Compiler.NativeOrderPoles
