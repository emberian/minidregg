/- Width-generic source Nat.add specialization through existing AirBignum/Emit.
No new arithmetic gadget, evaluator or source compiler. Source terms occur only
in propositions. The constructive polynomial is retained for backends; its field
reading is a cast, not an assertion that a whole multi-limb integer fits one felt.
This module is authored WIP until the representation producer and scoped check
qualify. It does not establish encrypted operand validity, canonical cost,
compiler-wide completeness, or source meaning for custom arithmetic methods. -/
import Compiler.AirBignum
import Compiler.BendSourceNatOperation
import Compiler.BendSourceNatTyped

namespace Minidregg.Compiler.BendLogicNatAdd
open Minidregg.Theory
open BendLogicSpecialization (BBook)
set_option autoImplicit false

/-- The exact Nat type, constructor family, source operation, and whole Book. -/
def bookBinding (book : BBook) : Bool :=
  decide (Minidregg.Theory.BendTT.Book.get book "Nat.arms" =
    some BendSourceRepresentation.natArmsDef) &&
  decide (Minidregg.Theory.BendTT.Book.get book "Nat" =
    some BendSourceRepresentation.natDef) &&
  decide (Minidregg.Theory.BendTT.Book.get book "Nat.add" =
    some BendSourceRepresentation.natAddDef) &&
  decide (Minidregg.Theory.BendTT.Book.check book = .ok ())

theorem bookBinding_sound {book : BBook} (bound : bookBinding book = true) :
    BendSourceRepresentation.NatBookBinding book ∧
      Minidregg.Theory.BendTT.Book.get book "Nat.add" =
        some BendSourceRepresentation.natAddDef := by
  simp only [bookBinding, Bool.and_eq_true, decide_eq_true_eq] at bound
  exact ⟨⟨bound.1.1.1, bound.1.1.2, bound.2⟩, bound.1.2⟩

def descriptor {p nVars width limbBits : Nat} [Fact p.Prime]
    (nPublic : Nat) (w : AirBignum.AddWires (Fin nVars) width limbBits) :
    ConstraintDescriptor (ZMod p) :=
  emit Fin.val nPublic nVars (AirBignum.addGadget w)

/-- Public width/limb topology and exact source API are admitted together.
The prime instance is the backend's declared field, not an arbitrary ring. -/
def compile {p nVars width limbBits : Nat} [Fact p.Prime]
    (nPublic : Nat) (book : BBook)
    (w : AirBignum.AddWires (Fin nVars) width limbBits) :
    Option (ConstraintDescriptor (ZMod p)) :=
  if nPublic ≤ nVars ∧ 2 * 2 ^ limbBits ≤ p ∧ bookBinding book = true then
    some (descriptor nPublic w) else none

theorem compile_exact {p nVars width limbBits : Nat} [Fact p.Prime]
    {nPublic : Nat} {book : BBook}
    {w : AirBignum.AddWires (Fin nVars) width limbBits}
    {d : ConstraintDescriptor (ZMod p)} (accepted : compile nPublic book w = some d) :
    nPublic ≤ nVars ∧ 2 * 2 ^ limbBits ≤ p ∧ bookBinding book = true ∧
      d = descriptor nPublic w := by
  unfold compile at accepted
  split at accepted
  · rename_i h
    exact ⟨h.1, h.2.1, h.2.2, (Option.some.inj accepted).symm⟩
  · contradiction

/-- One retained constructive little-endian polynomial, using the same Air DSL. -/
def wordExpr {F Idx : Type} [Field F] (base : Nat) : List Idx → Term (AirSig F Idx)
  | [] => cst 0
  | i :: tail => add' (vr i) (mul' (cst (base : F)) (wordExpr base tail))

def outputExpr {F : Type} [Field F] {nVars width limbBits : Nat}
    (w : AirBignum.AddWires (Fin nVars) width limbBits) : Term (AirSig F (Fin nVars)) :=
  add' (wordExpr (2 ^ limbBits) (List.ofFn w.x))
    (wordExpr (2 ^ limbBits) (List.ofFn w.y))

theorem wordExpr_cast {p : Nat} [Fact p.Prime] {Idx : Type}
    (base : Nat) (asg : Idx → ZMod p) (indices : List Idx) :
    eval asg (wordExpr base indices) =
      (Bignum.denoteNat base (indices.map (fun i => (asg i).val)) : ZMod p) := by
  induction indices with
  | nil => simp [wordExpr, eval_cst]
  | cons i tail ih =>
    simp only [wordExpr, eval_add', eval_vr, eval_mul', eval_cst, ih,
      List.map_cons, Bignum.denoteNat_cons, Nat.cast_add, Nat.cast_mul,
      ZMod.natCast_zmod_val]

/-- Arbitrary accepting auxiliary wires imply exact mathematical addition,
then the actual captured Nat.add reduction and actual Nat typing. No runtime
unary AST is constructed by this theorem or the emitted arithmetic descriptor. -/
theorem compiled_source_sound {p nVars width limbBits : Nat} [Fact p.Prime]
    {nPublic : Nat} {book : BBook}
    {w : AirBignum.AddWires (Fin nVars) width limbBits}
    {d : ConstraintDescriptor (ZMod p)} (accepted : compile nPublic book w = some d)
    (asg : Fin nVars → ZMod p) (wv : Nat → ZMod p)
    (pinned : ∀ i, wv i.val = asg i) (holds : descriptorHolds d wv) :
    let a := Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.x)
    let b := Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.y)
    let z := Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.z)
    z = a + b ∧
      BendSourceRepresentation.Normalizes book
        (BendSourceRepresentation.natAddCall a b) (BendSourceRepresentation.natTerm z) ∧
      Minidregg.Theory.BendTT.Typed book [] (BendSourceRepresentation.natTerm a) (.Ref "Nat") ∧
      Minidregg.Theory.BendTT.Typed book [] (BendSourceRepresentation.natTerm b) (.Ref "Nat") ∧
      Minidregg.Theory.BendTT.Typed book [] (BendSourceRepresentation.natTerm z) (.Ref "Nat") := by
  obtain ⟨_, noWrap, binding, exactDescriptor⟩ := compile_exact accepted
  obtain ⟨typedBinding, addBinding⟩ := bookBinding_sound binding
  have emittedHolds : descriptorHolds (descriptor nPublic w) wv := exactDescriptor ▸ holds
  have relation := (AirBignum.emit_addGadget_iff Fin.val Fin.val_injective
    nPublic nVars (fun i => i.isLt) asg w).mp
      ⟨wv, pinned, by simpa only [descriptor] using emittedHolds⟩
  obtain ⟨_, _, _, correct⟩ := AirBignum.addGadget_sound noWrap asg w relation
  dsimp only
  refine ⟨correct, ?_, BendSourceRepresentation.natTerm_typed book typedBinding _,
    BendSourceRepresentation.natTerm_typed book typedBinding _,
    BendSourceRepresentation.natTerm_typed book typedBinding _⟩
  rw [correct]
  exact BendSourceRepresentation.source_natAdd_normalizes book addBinding _ _

/-- The constructive output and emitted relation share the integer result.
If a backend wants one exact plaintext integer, it must additionally establish
that this whole value lies below its plaintext modulus. Per-limb no-wrap alone
allows multi-limb values larger than a field and does not imply that condition. -/
theorem compiled_output_cast {p nVars width limbBits : Nat} [Fact p.Prime]
    {nPublic : Nat} {book : BBook}
    {w : AirBignum.AddWires (Fin nVars) width limbBits}
    {d : ConstraintDescriptor (ZMod p)} (accepted : compile nPublic book w = some d)
    (asg : Fin nVars → ZMod p) (wv : Nat → ZMod p)
    (pinned : ∀ i, wv i.val = asg i) (holds : descriptorHolds d wv) :
    eval asg (outputExpr w) =
      (Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.z) : ZMod p) := by
  have correct := (compiled_source_sound accepted asg wv pinned holds).1
  rw [outputExpr, eval_add', wordExpr_cast, wordExpr_cast]
  simpa [AirBignum.limbVals, List.map_ofFn, Nat.cast_add] using
    congrArg (fun n : Nat => (n : ZMod p)) correct.symm

/-- Range checks bound the exact integer result by the declared limb capacity. -/
theorem compiled_result_bound {p nVars width limbBits : Nat} [Fact p.Prime]
    {nPublic : Nat} {book : BBook}
    {w : AirBignum.AddWires (Fin nVars) width limbBits}
    {d : ConstraintDescriptor (ZMod p)} (accepted : compile nPublic book w = some d)
    (asg : Fin nVars → ZMod p) (wv : Nat → ZMod p)
    (pinned : ∀ i, wv i.val = asg i) (holds : descriptorHolds d wv) :
    Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.z) <
      (2 ^ limbBits) ^ width := by
  obtain ⟨_, noWrap, _, exactDescriptor⟩ := compile_exact accepted
  have emittedHolds : descriptorHolds (descriptor nPublic w) wv := exactDescriptor ▸ holds
  have relation := (AirBignum.emit_addGadget_iff Fin.val Fin.val_injective
    nPublic nVars (fun i => i.isLt) asg w).mp
      ⟨wv, pinned, by simpa only [descriptor] using emittedHolds⟩
  obtain ⟨_, _, canonical, _⟩ := AirBignum.addGadget_sound noWrap asg w relation
  have bound := Bignum.denoteNat_lt_pow (by positivity : 0 < 2 ^ limbBits)
    (AirBignum.limbVals asg w.z) canonical.1
  simpa [canonical.2] using bound

/-- Explicit whole-value bound permits a scalar field decoder to recover the
integer result. This is separate from the per-limb soundness condition. -/
theorem compiled_output_exact_val {p nVars width limbBits : Nat} [Fact p.Prime]
    {nPublic : Nat} {book : BBook}
    {w : AirBignum.AddWires (Fin nVars) width limbBits}
    {d : ConstraintDescriptor (ZMod p)} (accepted : compile nPublic book w = some d)
    (asg : Fin nVars → ZMod p) (wv : Nat → ZMod p)
    (pinned : ∀ i, wv i.val = asg i) (holds : descriptorHolds d wv)
    (wholeBound : Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.z) < p) :
    (eval asg (outputExpr w)).val =
      Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.z) := by
  rw [compiled_output_cast accepted asg wv pinned holds]
  exact ZMod.val_cast_of_lt wholeBound

#assert_axioms bookBinding_sound
#assert_axioms compile_exact
#assert_axioms wordExpr_cast
#assert_axioms compiled_source_sound
#assert_axioms compiled_output_cast
#assert_axioms compiled_result_bound
#assert_axioms compiled_output_exact_val
end Minidregg.Compiler.BendLogicNatAdd
