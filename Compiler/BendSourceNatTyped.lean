import Compiler.BendSourceTypedRepresentation
namespace Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false
open Minidregg.Theory.BendTT

def natArmsDef : Def := ⟨"Nat.arms", .All .Q1 (.Enu ["Zero", "Succ"]) (.Typ .Q2),
  .Mat "Zero" (.Enu ["()"]) (.Mat "Succ" (.Sig .Q1 (.Ref "Nat") (.Enu ["()"])) .Efq), false⟩
def natDef : Def := ⟨"Nat", .Typ .Q2, .Sig .Q1 (.Enu ["Zero", "Succ"])
  (.App .Q1 (.Ref "Nat.arms") (.Var 0)), false⟩
structure NatBookBinding (bk : Book) : Prop where
  arms : Book.get bk "Nat.arms" = some natArmsDef
  typeDef : Book.get bk "Nat" = some natDef
  checked : Book.check bk = .ok ()

private theorem natArms_closed : Minidregg.Theory.BendTT.Term.Closed natArmsDef.v := by
  intro σ; rfl
private theorem nat_closed : Minidregg.Theory.BendTT.Term.Closed natDef.v := by
  intro σ; rfl

theorem natTerm_typed (bk : Book) (binding : NatBookBinding bk) (n : Nat) :
    Typed bk [] (natTerm n) (.Ref "Nat") := by
  induction n with
  | zero =>
    apply Typed.conv (U := natDef.v)
    · apply Typed.tup
      · exact Typed.lab (by simp)
      · apply Typed.conv (U := .Enu ["()"])
        · exact Typed.lab (by simp)
        · exact Or.inl ⟨.Enu ["()"], .refl,
            .step (.app (.delta binding.arms natArms_closed) .lab)
              (.step (.hit .enu) .refl)⟩
    · exact Or.inl ⟨natDef.v, .refl, .step (.delta binding.typeDef nat_closed) .refl⟩
  | succ n ih =>
    apply Typed.conv (U := natDef.v)
    · apply Typed.tup
      · exact Typed.lab (by simp)
      · apply Typed.conv (U := .Sig .Q1 (.Ref "Nat") (.Enu ["()"]))
        · exact Typed.tup ih (Typed.lab (by simp))
        · exact Or.inl ⟨.Sig .Q1 (.Ref "Nat") (.Enu ["()"]), .refl,
            .step (.app (.delta binding.arms natArms_closed) .lab)
              (.step (.miss (by decide) (.mat (.sig (.ref) .enu) .efq))
                (.step (.hit (.sig (.ref) .enu)) .refl))⟩
    · exact Or.inl ⟨natDef.v, .refl, .step (.delta binding.typeDef nat_closed) .refl⟩

#assert_axioms natTerm_typed
end Minidregg.Compiler.BendSourceRepresentation
