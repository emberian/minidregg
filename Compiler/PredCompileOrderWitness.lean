/-
Focused witnesses for the sole profile-aware predicate lowering. The small fields
and widths are proof fixtures. An enabled receiving profile must separately pin
its field, arithmetic width and compiler version in the committed semantics.
-/
import Compiler.PredCompile

namespace Minidregg.Compiler.OrderFoldWitness

open Minidregg.Pred (Pred State)

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def profile : CompilerProfile := .scalar 2

theorem profile_admissible : profile.Admissible (ZMod 17) :=
  PredOrder.noWrap_zmod (by decide)

def old : State := ⟨[("x", 0), ("owner", 7)]⟩
def next : State := ⟨[("x", 1), ("owner", 7)]⟩
def later : State := ⟨[("x", 2), ("owner", 7)]⟩

/-- False order atoms occur under both negation and disjunction. -/
def policy : Pred := Pred.all
  [.monotone "x", .le "x" 2, .eq "owner" 7, .not (.le "x" 0),
   Pred.any [.le "x" 0, .le "x" 2]]

theorem compound_support : supported profile policy = true := by decide

theorem compound_inputs_in_range : inputsInRange profile policy old next = true := by decide

theorem compound_cast_injective : castInjOn (ZMod 17) (intsOf policy old next) := by decide

theorem compound_source_true : Minidregg.Pred.eval policy old next = true := by decide

/-- The general compiler theorem, not an atom-specific proof, produces acceptance. -/
theorem compound_accepts :
    systemAccepts (stepAsg old next (wit profile (F := ZMod 17) policy old next))
      (lower profile policy) :=
  lower_complete profile profile_admissible compound_cast_injective compound_support
    compound_inputs_in_range compound_source_true

/-- The actual emitted constraints and executable witness also compute to acceptance. -/
theorem compound_accepts_computed :
    systemAccepts (stepAsg old next (wit profile (F := ZMod 17) policy old next))
      (lower profile policy) := by decide

theorem compound_later_accepts :
    systemAccepts (stepAsg old later (wit profile (F := ZMod 17) policy old later))
      (lower profile policy) := by decide

/-- Both steps satisfy the same policy, but a witness for one cannot be substituted for the other. -/
theorem different_step_witness_refused :
    ¬ systemAccepts (stepAsg old later (wit profile (F := ZMod 17) policy old next))
      (lower profile policy) := by decide

def flippedTop (path : List Nat) (index : Nat) : ZMod 17 :=
  if path = [0] ∧ index = 3 then 0 else wit profile policy old next path index

/-- The first child's forged false indicator cannot survive its forcing constraints. -/
theorem top_bit_flip_refused :
    ¬ systemAccepts (stepAsg old next flippedTop) (lower profile policy) := by decide

def decreasing : State := ⟨[("x", -1), ("owner", 7)]⟩

/-- A bounded decrease is rejected for every auxiliary assignment. -/
theorem decreasing_refused (A : List Nat → Nat → ZMod 17) :
    ¬ systemAccepts (stepAsg old decreasing A) (lower profile (.monotone "x")) := by
  intro accepted
  have wrong := lower_sound profile profile_admissible
    (by decide : castInjOn (ZMod 17) (intsOf (.monotone "x") old decreasing))
    (by decide) (by decide) accepted
  have falseSource : Minidregg.Pred.eval (.monotone "x") old decreasing = false := by decide
  rw [falseSource] at wrong
  contradiction

/-- Negating the same bounded false comparison is accepted through the same fold. -/
theorem decreasing_under_not_accepts :
    systemAccepts
      (stepAsg old decreasing (wit profile (F := ZMod 17) (.not (.monotone "x")) old decreasing))
      (lower profile (.not (.monotone "x"))) := by decide

def empty : State := ⟨[]⟩
def zero : State := ⟨[("x", 0)]⟩

def large : State := ⟨[("x", 18)]⟩

/-- Missing old state does not become a present zero operand. -/
theorem absent_to_zero_refused (A : List Nat → Nat → ZMod 17) :
    ¬ systemAccepts (stepAsg empty zero A) (lower profile (.monotone "x")) := by
  intro accepted
  have wrong := lower_sound profile profile_admissible
    (by decide : castInjOn (ZMod 17) (intsOf (.monotone "x") empty zero))
    (by decide) (by decide) accepted
  have falseSource : Minidregg.Pred.eval (.monotone "x") empty zero = false := by decide
  rw [falseSource] at wrong
  contradiction

/-- An unused large operand is allowed when presence masks the comparison. -/
theorem absent_large_under_not_accepts :
    inputsInRange profile (.not (.monotone "x")) empty large = true ∧
    systemAccepts
      (stepAsg empty large (wit profile (F := ZMod 17) (.not (.monotone "x")) empty large))
      (lower profile (.not (.monotone "x"))) := by decide

def upperEndpoint : State := ⟨[("x", 4)]⟩

theorem upper_endpoint_range_refused :
    inputsInRange profile (.monotone "x") zero upperEndpoint = false := by decide

/-- A true disjunct does not hide another branch's source-range violation. -/
theorem any_true_cannot_skip_source_range :
    Minidregg.Pred.eval (Pred.any [.eq "x" 18, .monotone "x"]) zero large = true ∧
    inputsInRange profile (Pred.any [.eq "x" 18, .monotone "x"]) zero large = false := by decide

/-- Negation does not suppress range validation on its child. -/
theorem not_true_cannot_skip_source_range :
    Minidregg.Pred.eval (.not (.le "x" 0)) zero large = true ∧
    inputsInRange profile (.not (.le "x" 0)) zero large = false := by decide

/-- The old finite equality cast label alone does not establish integer order. -/
def wrappedOld : State := ⟨[("x", 18)]⟩
def wrappedNew : State := ⟨[("x", 2)]⟩

def wrappedAux (_ : List Nat) (index : Nat) : ZMod 17 :=
  match index with
  | 0 => 5
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | _ => 0

/-- Teeth for the receiving range check: without it, even equality cast injectivity is insufficient. -/
theorem actual_source_range_is_necessary :
    castInjOn (ZMod 17) (intsOf (.monotone "x") wrappedOld wrappedNew) ∧
    systemAccepts (stepAsg wrappedOld wrappedNew wrappedAux) (lower profile (.monotone "x")) ∧
    Minidregg.Pred.eval (.monotone "x") wrappedOld wrappedNew = false ∧
    inputsInRange profile (.monotone "x") wrappedOld wrappedNew = false := by decide

def smallFieldOld : State := ⟨[("x", 4)]⟩

def smallFieldAux (_ : List Nat) (index : Nat) : ZMod 7 :=
  match index with
  | 0 => 0
  | 1 | 2 | 3 => 1
  | _ => 0

/-- A source-bounded comparison still fails without the whole-interval field condition. -/
theorem profile_no_wrap_is_necessary :
    castInjOn (ZMod 7) (intsOf (.monotone "x") smallFieldOld zero) ∧
    inputsInRange profile (.monotone "x") smallFieldOld zero = true ∧
    systemAccepts (stepAsg smallFieldOld zero smallFieldAux) (lower profile (.monotone "x")) ∧
    Minidregg.Pred.eval (.monotone "x") smallFieldOld zero = false := by decide

theorem small_field_profile_inadmissible : ¬ profile.Admissible (ZMod 7) := by
  intro h
  have impossible := h 0 7 (by decide) (by decide) (by decide)
  omega

/-- The explicit disabled research profile continues to refuse order. -/
theorem disabled_refuses_order (A : List Nat → Nat → ZMod 17) :
    ¬ systemAccepts (stepAsg old next A) (lower CompilerProfile.disabled (.monotone "x")) :=
  lower_monotone_disabled_refuses _ _

/-- info: 'Minidregg.Compiler.OrderFoldWitness.compound_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compound_accepts
/-- info: 'Minidregg.Compiler.OrderFoldWitness.decreasing_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decreasing_refused
/-- info: 'Minidregg.Compiler.OrderFoldWitness.actual_source_range_is_necessary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_source_range_is_necessary
/-- info: 'Minidregg.Compiler.OrderFoldWitness.profile_no_wrap_is_necessary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms profile_no_wrap_is_necessary

end Minidregg.Compiler.OrderFoldWitness
