/- The actual publication decoder is complete for every finitely represented
source term. CodeDenotes uniqueness follows through this deterministic decoder,
not an assumed source oracle or a finite suite of representative programs.
-/
import Theory.BendClosureDecode

namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false

/-- Required recursive decoder fuel. Every source constructor, including dead
annotations/types and live rewrite evidence, contributes to this bound. -/
def codeDepth : Term → Nat
  | .Var _ | .Ref _ | .Typ _ | .Enu _ | .Lab _ | .Efq | .Rfl => 1
  | .Ann value type | .Let _ value type | .All _ value type
  | .App _ value type | .Sig _ value type | .Tup _ value type
  | .Mat _ value type => max (codeDepth value) (codeDepth type) + 1
  | .Lam _ body | .Prj body => codeDepth body + 1
  | .Eql left right type | .Rwt left right type =>
      max (max (codeDepth left) (codeDepth right)) (codeDepth type) + 1

/-- Every finite denotation is recovered by the executable decoder with any
adequate depth bound, retaining the exact source term and its certificate. -/
theorem decodeCode_complete {program : Program} {pointer : Nat} {term : Term}
    (denotation : CodeDenotes program pointer term) (ticks : Nat)
    (adequate : codeDepth term ≤ ticks) :
    decodeCode program ticks pointer = some ⟨term, denotation⟩ := by
  induction denotation generalizing ticks <;> cases ticks with
  | zero => simp_all [codeDepth]
  | succ ticks =>
    simp_all [codeDepth, Nat.max_le, decodeCode]
    all_goals split
    all_goals try simp_all
    all_goals try split
    all_goals try simp_all
    all_goals repeat (cases ‹_ ∧ _›)
    all_goals subst_vars
    all_goals try simp_all
    all_goals try split
    all_goals try simp_all
    all_goals subst_vars
    all_goals try simp_all

/-- A fixed published table entry cannot denote two different source terms.
The shared decoder fuel need not be executable or public; it witnesses the
mathematical uniqueness fact independently of any chosen runtime capacity. -/
theorem CodeDenotes.functional {program : Program} {pointer : Nat}
    {left right : Term} (leftExact : CodeDenotes program pointer left)
    (rightExact : CodeDenotes program pointer right) : left = right := by
  let ticks := max (codeDepth left) (codeDepth right)
  have leftDecoded := decodeCode_complete leftExact ticks (Nat.le_max_left _ _)
  have rightDecoded := decodeCode_complete rightExact ticks (Nat.le_max_right _ _)
  have same : (some (⟨left, leftExact⟩ : DecodedCode program pointer)) =
      some ⟨right, rightExact⟩ := leftDecoded.symm.trans rightDecoded
  exact congrArg DecodedCode.term (Option.some.inj same)

/-- Any successful decode, even with another fuel choice, recovers the same
source term as the publication certificate. This is the consumer-facing join. -/
theorem decodeCode_exact_source {program : Program} {pointer ticks : Nat}
    {source : Term} (sourceExact : CodeDenotes program pointer source)
    {decoded : DecodedCode program pointer}
    (_success : decodeCode program ticks pointer = some decoded) :
    decoded.term = source :=
  decoded.exact.functional sourceExact

#assert_axioms decodeCode_complete
#assert_axioms CodeDenotes.functional
#assert_axioms decodeCode_exact_source
end Minidregg.Theory.BendClosureArena
