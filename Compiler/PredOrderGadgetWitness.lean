/-
# Inhabitation and adversarial teeth for the forced order gadget

`ZMod 17`, width 2 is a type-visible arithmetic witness, not a deployment profile.
The generic completeness theorem covers every bounded pair and every field; the
generic soundness theorem additionally requires the whole-interval no-wrap law.
These named examples keep both premises honest and show how each can fail.
-/
import Compiler.PredOrderGadget
import Compiler.PredCompile

namespace Minidregg.Compiler.PredOrder.Witness

inductive Wire (k : Nat) where
  | present
  | left
  | right
  | shifted
  | bit (i : Fin (k + 1))
  deriving DecidableEq, Repr

def assignment {F : Type} [Field F] {k : Nat} (present : Bool) (a b : Int)
    (shifted : F) (bits : Fin (k + 1) → F) : Wire k → F
  | .present => if present then 1 else 0
  | .left => (a : F)
  | .right => (b : F)
  | .shifted => shifted
  | .bit i => bits i

def canonical {F : Type} [Field F] (k : Nat) (present : Bool) (a b : Int) :
    Wire k → F :=
  assignment present a b (shiftedNat k present a b : F)
    (fun i => (binaryDigits (k + 1) (shiftedNat k present a b) i : F))

def system {F : Type} [Field F] (k : Nat) : ConstraintSystem F (Wire k) :=
  gadget k (vr .present) (vr .left) (vr .right) .shifted Wire.bit

def output {F : Type} [Field F] (k : Nat) : Term (AirSig F (Wire k)) :=
  indicator k (vr .present) Wire.bit

/-- Non-vacuity for all bounded inputs, not merely the small field examples. -/
theorem canonical_accepts {F : Type} [Field F] {k : Nat} {present : Bool} {a b : Int}
    (h : InputsInRange k present a b) :
    systemAccepts (canonical (F := F) k present a b) (system k) := by
  exact complete (F := F) k (vr .present) (vr .left) (vr .right) .shifted Wire.bit
    (canonical k present a b) present a b h rfl rfl rfl rfl (fun _ => rfl)

/-- The exact output contract holds for the executable witness, in every admissible field. -/
theorem canonical_output {F : Type} [Field F] {k : Nat} {present : Bool} {a b : Int}
    (hnw : NoWrap F k) (h : InputsInRange k present a b) :
    eval (canonical (F := F) k present a b) (output k) =
      if present && decide (a ≤ b) then 1 else 0 := by
  exact forced (F := F) k (vr .present) (vr .left) (vr .right) .shifted Wire.bit
    (canonical k present a b) present a b hnw h rfl rfl rfl (canonical_accepts h)

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem inhabited_no_wrap : NoWrap (ZMod 17) 2 := noWrap_zmod (by decide)

theorem inhabited_source_bounds : InputsInRange 2 true (-2) 1 := by decide

theorem premises_inhabited :
    ∃ a b : Int, NoWrap (ZMod 17) 2 ∧ InputsInRange 2 true a b :=
  ⟨-2, 1, inhabited_no_wrap, inhabited_source_bounds⟩

theorem negative_to_positive_accepts :
    systemAccepts (canonical (F := ZMod 17) 2 true (-2) 1) (system 2) :=
  canonical_accepts (by decide)

theorem negative_to_positive_true :
    eval (canonical (F := ZMod 17) 2 true (-2) 1) (output 2) = 1 := by
  simpa using canonical_output inhabited_no_wrap inhabited_source_bounds

theorem decreasing_accepts_with_false_indicator :
    systemAccepts (canonical (F := ZMod 17) 2 true 1 (-2)) (system 2) ∧
      eval (canonical (F := ZMod 17) 2 true 1 (-2)) (output 2) = 0 := by
  refine ⟨canonical_accepts (by decide), ?_⟩
  simpa using canonical_output inhabited_no_wrap (show InputsInRange 2 true 1 (-2) by decide)

theorem equality_true :
    eval (canonical (F := ZMod 17) 2 true (-2) (-2)) (output 2) = 1 := by
  simpa using canonical_output inhabited_no_wrap
    (show InputsInRange 2 true (-2) (-2) by decide)

theorem inclusive_lower_endpoint_accepts :
    systemAccepts (canonical (F := ZMod 17) 2 true 2 (-2)) (system 2) ∧
      eval (canonical (F := ZMod 17) 2 true 2 (-2)) (output 2) = 0 := by
  refine ⟨canonical_accepts (by decide), ?_⟩
  simpa using canonical_output inhabited_no_wrap (show InputsInRange 2 true 2 (-2) by decide)

/-- Absence is false even when the unused operands are far outside the scalar profile. -/
theorem absence_masks_unbounded_operands (a b : Int) :
    systemAccepts (canonical (F := ZMod 17) 2 false a b) (system 2) ∧
      eval (canonical (F := ZMod 17) 2 false a b) (output 2) = 0 := by
  have h : InputsInRange 2 false a b := by simp [InputsInRange]
  refine ⟨canonical_accepts h, ?_⟩
  simpa using canonical_output inhabited_no_wrap h

/-- Existing Boolean negation reads the false order result correctly. -/
theorem decreasing_under_not_true :
    eval (canonical (F := ZMod 17) 2 true 1 (-2)) (notT (output 2)) = 1 := by
  rw [eval_notT, decreasing_accepts_with_false_indicator.2]
  ring

/-- `any`'s existing indicator algebra can combine the false order result with true. -/
theorem decreasing_under_any_true :
    eval (canonical (F := ZMod 17) 2 true 1 (-2))
      (notT (prodT [notT (output 2), notT (cst 1)])) = 1 := by
  simp [eval_notT, eval_prodT, decreasing_accepts_with_false_indicator.2]

def badBit : Wire 2 → ZMod 17 := assignment true 0 1 5 ![3, 1, 0]

theorem bad_bit_recomposes : accepts badBit (recompTerm .shifted Wire.bit) := by decide

theorem bad_bit_refused : ¬ systemAccepts badBit (system 2) := by decide

def badRecomposition : Wire 2 → ZMod 17 := assignment true 0 1 5 ![1, 1, 1]

theorem wrong_recomposition_all_bits_boolean :
    ∀ i : Fin 3, badRecomposition (.bit i) = 0 ∨ badRecomposition (.bit i) = 1 := by decide

theorem wrong_recomposition_refused : ¬ systemAccepts badRecomposition (system 2) := by decide

/-- The strict upper endpoint cannot be smuggled through by any auxiliary assignment. -/
theorem exclusive_upper_endpoint_refused (asg : Wire 2 → ZMod 17)
    (hp : asg .present = 1) (ha : asg .left = 0) (hb : asg .right = 4) :
    ¬ systemAccepts asg (system 2) := by
  intro h
  obtain ⟨hRange, hbind⟩ :=
    (gadget_correct 2 asg (vr .present) (vr .left) (vr .right) .shifted Wire.bit).mp h
  have hlt := rangeGadget_val_lt (by decide : 2 ^ 3 ≤ 17) asg .shifted Wire.bit hRange
  have hshift : asg .shifted = (8 : ZMod 17) := by
    simpa [shiftedTerm, hp, ha, hb] using hbind
  rw [hshift] at hlt
  have hv : (8 : ZMod 17).val = 8 := by decide
  rw [hv] at hlt
  norm_num at hlt

/-- Source bounds cannot be replaced by equality of scalar field casts. -/
def wrappedSource : Wire 2 → ZMod 17 := assignment true 17 0 4 ![0, 0, 1]

theorem source_bound_is_necessary :
    systemAccepts wrappedSource (system 2) ∧
      eval wrappedSource (output 2) = 1 ∧
      ¬ (17 : Int) ≤ 0 ∧ ¬ InputsInRange 2 true 17 0 := by decide

/-- Even correctly bounded integers are misread if the decomposition wraps in the field. -/
def wrappedField : Wire 2 → ZMod 7 := assignment true 0 3 0 ![0, 0, 0]

theorem field_no_wrap_is_necessary :
    InputsInRange 2 true 0 3 ∧ systemAccepts wrappedField (system 2) ∧
      eval wrappedField (output 2) = 0 ∧ (0 : Int) ≤ 3 := by decide

theorem small_field_fails_no_wrap : ¬ NoWrap (ZMod 7) 2 := by
  intro h
  have impossible := h 0 7 (by decide) (by decide) (by decide)
  omega

/-- info: 'Minidregg.Compiler.PredOrder.Witness.canonical_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonical_accepts
/-- info: 'Minidregg.Compiler.PredOrder.Witness.canonical_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonical_output
/-- info: 'Minidregg.Compiler.PredOrder.Witness.premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms premises_inhabited
/-- info: 'Minidregg.Compiler.PredOrder.Witness.source_bound_is_necessary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_bound_is_necessary
/-- info: 'Minidregg.Compiler.PredOrder.Witness.field_no_wrap_is_necessary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms field_no_wrap_is_necessary
/-- info: 'Minidregg.Compiler.PredOrder.Witness.exclusive_upper_endpoint_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exclusive_upper_endpoint_refused
/-- info: 'Minidregg.Compiler.PredOrder.wrong_indicator_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_indicator_refused

end Minidregg.Compiler.PredOrder.Witness
