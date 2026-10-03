/- Reusable natural-expression AIR, canonical input/output ranges and
constructive expression. Every gadget is from Mini's existing AirRange/Emit.
Arbitrary-witness soundness and general range-witness completeness join the
same source expression. Public program/topology; no encrypted range proof is
inferred merely from ciphertext replay. -/
import Compiler.BendNaturalSource
import Mathlib.Logic.Equiv.Fin.Basic

namespace Minidregg.Compiler.BendNaturalExpression
open Minidregg.Theory
set_option autoImplicit false

abbrev Index (arity maxBits : Nat) := Fin (arity + 1) ⊕
  (Fin (arity + 1) × Fin maxBits)

def packed {n k : Nat} : Index n k ≃ Fin ((n + 1) + (n + 1) * k) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def wire {n k : Nat} (i : Index n k) : Nat := (packed i).val

theorem wire_injective {n k : Nat} : Function.Injective (wire (n := n) (k := k)) :=
  Fin.val_injective.comp packed.injective

def rowWidth {n : Nat} (inputBits maxBits : Nat) (i : Fin (n + 1)) : Nat :=
  if i.val = 0 then maxBits else inputBits

theorem rowWidth_le {n : Nat} (inputBits maxBits : Nat) (fits : inputBits ≤ maxBits)
    (i : Fin (n + 1)) : rowWidth inputBits maxBits i ≤ maxBits := by
  unfold rowWidth; split <;> omega

def rangeBits {n : Nat} {inputBits maxBits : Nat} (fits : inputBits ≤ maxBits)
    (i : Fin (n + 1)) (j : Fin (rowWidth inputBits maxBits i)) : Index n maxBits :=
  .inr (i, ⟨j.val, lt_of_lt_of_le j.isLt (rowWidth_le _ _ fits i)⟩)

def ranges {n : Nat} {F : Type} [Field F] (inputBits maxBits : Nat)
    (fits : inputBits ≤ maxBits) : ConstraintSystem F (Index n maxBits) :=
  (List.finRange (n + 1)).flatMap fun i => rangeGadget (.inl i) (rangeBits fits i)

def equation {n : Nat} {F : Type} [Field F] {maxBits : Nat} (expr : Expr n) :
    Term (AirSig F (Index n maxBits)) :=
  add' (vr (.inl 0)) (mul' (cst (-1)) (expr.air (fun i => .inl i.succ)))

def constraints {n : Nat} {F : Type} [Field F] (inputBits maxBits : Nat)
    (fits : inputBits ≤ maxBits) (expr : Expr n) : ConstraintSystem F (Index n maxBits) :=
  ranges inputBits maxBits fits ++ [equation expr]

def descriptor {n : Nat} {F : Type} [Field F] (inputBits maxBits : Nat)
    (fits : inputBits ≤ maxBits) (expr : Expr n) : ConstraintDescriptor F :=
  emit wire 0 ((n + 1) + (n + 1) * maxBits) (constraints inputBits maxBits fits expr)

theorem ranges_correct {n : Nat} {F : Type} [Field F]
    (inputBits maxBits : Nat) (fits : inputBits ≤ maxBits) (asg : Index n maxBits → F) :
    systemAccepts asg (ranges inputBits maxBits fits) ↔
      ∀ i, systemAccepts asg (rangeGadget (.inl i) (rangeBits fits i)) := by
  constructor
  · intro h i t ht
    apply h t
    rw [ranges, List.mem_flatMap]
    exact ⟨i, List.mem_finRange i, ht⟩
  · intro h t ht
    rw [ranges, List.mem_flatMap] at ht
    obtain ⟨i, _, ht⟩ := ht
    exact h i t ht

theorem equation_correct {n : Nat} {F : Type} [Field F] {maxBits : Nat}
    (expr : Expr n) (asg : Index n maxBits → F) :
    accepts asg (equation expr) ↔ asg (.inl 0) =
      eval asg (expr.air (fun i => .inl i.succ)) := by
  unfold accepts equation
  simp only [eval_add', eval_vr, eval_mul', eval_cst]
  constructor <;> intro h <;> linear_combination h

theorem constraints_correct {n : Nat} {F : Type} [Field F]
    (inputBits maxBits : Nat) (fits : inputBits ≤ maxBits) (expr : Expr n)
    (asg : Index n maxBits → F) :
    systemAccepts asg (constraints inputBits maxBits fits expr) ↔
      (∀ i, systemAccepts asg (rangeGadget (.inl i) (rangeBits fits i))) ∧
      asg (.inl 0) = eval asg (expr.air (fun i => .inl i.succ)) := by
  rw [constraints, systemAccepts_append, ranges_correct]
  simp only [systemAccepts_cons, systemAccepts_nil, and_true, equation_correct]

def inputValues {n k p : Nat} (asg : Index n k → ZMod p) (i : Fin n) : Nat :=
  (asg (.inl i.succ)).val

/-- Complete finite-domain soundness for every satisfying assignment, including
malicious auxiliary wires; source caps and exact output are forced by the AIR. -/
theorem constraints_integer_sound {n p : Nat} [Fact p.Prime]
    (inputBits maxBits : Nat) (fits : inputBits ≤ maxBits) (expr : Expr n)
    (fieldFits : 2 ^ maxBits ≤ p)
    (outputFits : expr.upper (fun _ => 2 ^ inputBits - 1) < 2 ^ maxBits)
    (asg : Index n maxBits → ZMod p)
    (holds : systemAccepts asg (constraints inputBits maxBits fits expr)) :
    (∀ i, inputValues asg i < 2 ^ inputBits) ∧
      (asg (.inl 0)).val = expr.value (inputValues asg) := by
  obtain ⟨ranged, equationHolds⟩ := (constraints_correct _ _ fits expr asg).mp holds
  have inputBound : ∀ i, inputValues asg i < 2 ^ inputBits := by
    intro i
    have widthBound := rowWidth_le inputBits maxBits fits i.succ
    have primeBound : 2 ^ (rowWidth inputBits maxBits i.succ) ≤ p :=
      le_trans (Nat.pow_le_pow_right (by omega) widthBound) fieldFits
    have rangeBound := rangeGadget_val_lt primeBound asg (.inl i.succ)
      (rangeBits fits i.succ) (ranged i.succ)
    simpa [inputValues, rowWidth] using rangeBound
  have naturalBound := value_le expr (inputValues asg) (fun _ => 2 ^ inputBits - 1)
    (fun i => by change inputValues asg i ≤ 2 ^ inputBits - 1; have := inputBound i; omega)
  have finalBound : expr.value (inputValues asg) < p :=
    lt_of_lt_of_le (lt_of_le_of_lt naturalBound outputFits) fieldFits
  have castCorrect := air_correct expr (fun i => Sum.inl i.succ) asg (inputValues asg)
    (fun i => (ZMod.natCast_zmod_val _).symm)
  rw [castCorrect] at equationHolds
  have valCorrect := congrArg ZMod.val equationHolds
  exact ⟨inputBound, by simpa [ZMod.val_cast_of_lt finalBound] using valCorrect⟩

def numbers {n : Nat} (inputs : Fin n → Nat) (output : Nat) (i : Fin (n + 1)) : Nat :=
  if h : i.val = 0 then output else inputs ⟨i.val - 1, by omega⟩

@[simp] theorem numbers_output {n : Nat} (inputs : Fin n → Nat) (output : Nat) :
    numbers inputs output 0 = output := by simp [numbers]
@[simp] theorem numbers_input {n : Nat} (inputs : Fin n → Nat) (output : Nat) (i : Fin n) :
    numbers inputs output i.succ = inputs i := by
  simp [numbers, Fin.val_succ]

/-- All range premises are constructively inhabited by AirRange's generic
binary decomposition theorem. This proof does not posit an accepting witness. -/
theorem ranges_complete {n : Nat} {F : Type} [Field F]
    (inputBits maxBits : Nat) (fits : inputBits ≤ maxBits)
    (values : Fin (n + 1) → Nat)
    (bounded : ∀ i, values i < 2 ^ rowWidth inputBits maxBits i) :
    ∃ asg : Index n maxBits → F,
      (∀ i, asg (.inl i) = (values i : F)) ∧
      systemAccepts asg (ranges inputBits maxBits fits) := by
  classical
  choose digits boolean decomposition using
    (fun i => exists_boolDecomp (F := F) (values i) (bounded i))
  let asg : Index n maxBits → F := fun index => match index with
    | .inl i => (values i : F)
    | .inr (i, j) => if h : j.val < rowWidth inputBits maxBits i then
        digits i ⟨j.val, h⟩ else 0
  refine ⟨asg, fun _ => rfl, (ranges_correct _ _ fits asg).mpr ?_⟩
  intro i
  apply (rangeGadget_correct asg (.inl i) (rangeBits fits i)).mpr
  exact ⟨by intro j; simpa [asg, rangeBits] using boolean i j,
    by simpa [asg, rangeBits] using decomposition i⟩

/-- Every admitted input has an emitted witness for its exact source result.
No cipher, prover or native decoder is assumed by this completeness theorem. -/
theorem descriptor_complete {n p : Nat} [Fact p.Prime]
    (inputBits maxBits : Nat) (fits : inputBits ≤ maxBits) (expr : Expr n)
    (outputFits : expr.upper (fun _ => 2 ^ inputBits - 1) < 2 ^ maxBits)
    (inputs : Fin n → Nat) (bounded : ∀ i, inputs i < 2 ^ inputBits) :
    ∃ wv : Nat → ZMod p,
      (∀ i, wv (wire (k := maxBits) (Sum.inl i)) = (numbers inputs (expr.value inputs) i : ZMod p)) ∧
      descriptorHolds (descriptor inputBits maxBits fits expr) wv := by
  have resultBound := lt_of_le_of_lt
    (value_le expr inputs (fun _ => 2 ^ inputBits - 1) (fun i => by change inputs i ≤ 2 ^ inputBits - 1; have := bounded i; omega)) outputFits
  have allBounded : ∀ i, numbers inputs (expr.value inputs) i <
      2 ^ rowWidth inputBits maxBits i := by
    intro i
    by_cases zero : i.val = 0
    · simpa [numbers, rowWidth, zero] using resultBound
    · simpa [numbers, rowWidth, zero] using bounded ⟨i.val - 1, by omega⟩
  obtain ⟨asg, primary, rangesAccept⟩ := ranges_complete (F := ZMod p)
    inputBits maxBits fits (numbers inputs (expr.value inputs)) allBounded
  have exprCorrect := air_correct expr (fun i => Sum.inl i.succ) asg inputs
    (fun i => by simpa using primary i.succ)
  have allAccept : systemAccepts asg (constraints inputBits maxBits fits expr) := by
    apply (constraints_correct _ _ fits expr asg).mpr
    exact ⟨(ranges_correct _ _ fits asg).mp rangesAccept,
      by simpa [exprCorrect] using primary 0⟩
  obtain ⟨wv, pinned, accepted⟩ := (emit_accepts_iff wire wire_injective 0
    ((n + 1) + (n + 1) * maxBits) (fun i => (packed i).isLt) asg
      (constraints inputBits maxBits fits expr)).mpr allAccept
  exact ⟨wv, fun i => (pinned _).trans (primary i), accepted⟩

#assert_axioms wire_injective
#assert_axioms ranges_correct
#assert_axioms equation_correct
#assert_axioms constraints_correct
#assert_axioms constraints_integer_sound
#assert_axioms ranges_complete
#assert_axioms descriptor_complete
end Minidregg.Compiler.BendNaturalExpression
