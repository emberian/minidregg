import Compiler.BendSourceNatTyped
namespace Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false
open Minidregg.Theory.BendTT

/-- Actual safe_emit specialization for source List<&2,Nat>. The element
parameter is Q0; the constructor's head and tail remain Q1 fields. -/
def listArmsBody : BTerm := .Lam .Q0 (.Mat "Nil" (.Enu ["()"])
  (.Mat "Con" (.Sig .Q1 (.Var 0) (.Sig .Q1
    (.App .Q0 (.Ref "List.q2") (.Var 1)) (.Enu ["()"]))) .Efq))
def listBody : BTerm := .Lam .Q0 (.Sig .Q1 (.Enu ["Nil", "Con"])
  (.App .Q1 (.App .Q0 (.Ref "List.q2.arms") (.Var 1)) (.Var 0)))
def listArmsDef : Def := ⟨"List.q2.arms", .All .Q0 (.Typ .Q2)
  (.All .Q1 (.Enu ["Nil", "Con"]) (.Typ .Q2)), listArmsBody, false⟩
def listDef : Def := ⟨"List.q2", .All .Q0 (.Typ .Q2) (.Typ .Q2), listBody, false⟩
structure ListBookBinding (bk : Book) : Prop where
  arms : Book.get bk "List.q2.arms" = some listArmsDef
  typeDef : Book.get bk "List.q2" = some listDef
  checked : Book.check bk = .ok ()

def listNatType : BTerm := .App .Q0 (.Ref "List.q2") (.Ref "Nat")
def listNatShape : BTerm := .Sig .Q1 (.Enu ["Nil", "Con"])
  (.App .Q1 (.App .Q0 (.Ref "List.q2.arms") (.Ref "Nat")) (.Var 0))
def listNatFields : BTerm := .Sig .Q1 (.Ref "Nat") (.Sig .Q1 listNatType (.Enu ["()"] ))

private theorem list_closed : Minidregg.Theory.BendTT.Term.Closed listDef.v := by intro σ; rfl
private theorem listArms_closed : Minidregg.Theory.BendTT.Term.Closed listArmsDef.v := by intro σ; rfl

private theorem listType_unfold (bk : Book) (binding : ListBookBinding bk) :
    Pars bk listNatType listNatShape := by
  exact .step (.app (.delta binding.typeDef list_closed) .ref)
    (.step (.beta (par_refl _) .ref) .refl)

private theorem listNil_unfold (bk : Book) (binding : ListBookBinding bk) :
    Pars bk (.App .Q1 (.App .Q0 (.Ref "List.q2.arms") (.Ref "Nat")) (.Lab "Nil"))
      (.Enu ["()"]) := by
  exact .step (.app (.app (.delta binding.arms listArms_closed) .ref) .lab)
    (.step (.app (.beta (par_refl _) .ref) .lab) (.step (.hit .enu) .refl))

private theorem listCon_unfold (bk : Book) (binding : ListBookBinding bk) :
    Pars bk (.App .Q1 (.App .Q0 (.Ref "List.q2.arms") (.Ref "Nat")) (.Lab "Con"))
      listNatFields := by
  exact .step (.app (.app (.delta binding.arms listArms_closed) .ref) .lab)
    (.step (.app (.beta (par_refl _) .ref) .lab)
      (.step (.miss (by decide) (par_refl _)) (.step (.hit (par_refl _)) .refl)))

theorem natListTerm_typed (bk : Book) (natBinding : NatBookBinding bk)
    (listBinding : ListBookBinding bk) (ns : List Nat) :
    Typed bk [] (natListTerm ns) listNatType := by
  induction ns with
  | nil =>
    apply Typed.conv (U := listNatShape)
    · apply Typed.tup
      · exact Typed.lab (by simp)
      · apply Typed.conv (U := .Enu ["()"])
        · exact Typed.lab (by simp)
        · exact Or.inl ⟨.Enu ["()"], .refl, listNil_unfold bk listBinding⟩
    · exact Or.inl ⟨listNatShape, .refl, listType_unfold bk listBinding⟩
  | cons n ns ih =>
    apply Typed.conv (U := listNatShape)
    · apply Typed.tup
      · exact Typed.lab (by simp)
      · apply Typed.conv (U := listNatFields)
        · exact Typed.tup (natTerm_typed bk natBinding n)
            (Typed.tup ih (Typed.lab (by simp)))
        · exact Or.inl ⟨listNatFields, .refl, listCon_unfold bk listBinding⟩
    · exact Or.inl ⟨listNatShape, .refl, listType_unfold bk listBinding⟩

#assert_axioms natListTerm_typed
end Minidregg.Compiler.BendSourceRepresentation
