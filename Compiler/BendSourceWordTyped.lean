import Compiler.BendSourceNatTyped
import Compiler.BendSourceNatOperation
namespace Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false
open Minidregg.Theory.BendTT

def wordNilArmsDef : Def := ⟨"Word.Nil.arms", .All .Q1 (.Enu ["WNil"]) (.Typ .Q2),
  .Mat "WNil" (.Enu ["()"]) .Efq, false⟩
def wordNilDef : Def := ⟨"Word.Nil", .Typ .Q2, .Sig .Q1 (.Enu ["WNil"])
  (.App .Q1 (.Ref "Word.Nil.arms") (.Var 0)), false⟩
def wordConArmsBody : BTerm := .Lam .Q0 (.Mat "WCon"
  (.Sig .Q1 (.Ref "Bool") (.Sig .Q1 (.App .Q1 (.Ref "Word") (.Var 1)) (.Enu ["()"]))) .Efq)
def wordConArmsDef : Def := ⟨"Word.Con.arms", .All .Q0 (.Ref "Nat")
  (.All .Q1 (.Enu ["WCon"]) (.Typ .Q2)), wordConArmsBody, false⟩
def wordConBody : BTerm := .Lam .Q0 (.Sig .Q1 (.Enu ["WCon"])
  (.App .Q1 (.App .Q0 (.Ref "Word.Con.arms") (.Var 1)) (.Var 0)))
def wordConDef : Def := ⟨"Word.Con", .All .Q0 (.Ref "Nat") (.Typ .Q2), wordConBody, false⟩
def wordBody : BTerm := .Prj (.Mat "Zero" (unitArm (.Ref "Word.Nil"))
  (.Mat "Succ" (.Prj (.Lam .Q1 (unitArm (.App .Q0 (.Ref "Word.Con") (.Var 0))))) .Efq))
def wordDef : Def := ⟨"Word", .All .Q1 (.Ref "Nat") (.Typ .Q2), wordBody, false⟩
structure WordBookBinding (bk : Book) : Prop where
  nilArms : Book.get bk "Word.Nil.arms" = some wordNilArmsDef
  nilType : Book.get bk "Word.Nil" = some wordNilDef
  conArms : Book.get bk "Word.Con.arms" = some wordConArmsDef
  conType : Book.get bk "Word.Con" = some wordConDef
  word : Book.get bk "Word" = some wordDef
  checked : Book.check bk = .ok ()

def wordType (width : Nat) : BTerm := .App .Q1 (.Ref "Word") (natTerm width)
def wordConType (width : Nat) : BTerm := .App .Q0 (.Ref "Word.Con") (natTerm width)
def wordConShape (width : Nat) : BTerm := .Sig .Q1 (.Enu ["WCon"])
  (.App .Q1 (.App .Q0 (.Ref "Word.Con.arms") (natTerm width)) (.Var 0))
def wordConFields (width : Nat) : BTerm := .Sig .Q1 (.Ref "Bool")
  (.Sig .Q1 (wordType width) (.Enu ["()"] ))

private theorem natTerm_closed (n : Nat) : Minidregg.Theory.BendTT.Term.Closed (natTerm n) := by
  induction n with
  | zero => intro σ; rfl
  | succ n ih => intro σ; simp only [natTerm, Term.sub]; rw [ih σ]

@[simp] private theorem natTerm_sub (σ : Subst) (n : Nat) : Term.sub σ (natTerm n) = natTerm n := natTerm_closed n σ
@[simp] private theorem natTerm_ren (r : Nat → Nat) (n : Nat) : Term.ren r (natTerm n) = natTerm n := closed_ren (natTerm_closed n)

private theorem wordNil_closed : Minidregg.Theory.BendTT.Term.Closed wordNilDef.v := by intro σ; rfl
private theorem wordNilArms_closed : Minidregg.Theory.BendTT.Term.Closed wordNilArmsDef.v := by intro σ; rfl
private theorem wordCon_closed : Minidregg.Theory.BendTT.Term.Closed wordConDef.v := by intro σ; rfl
private theorem wordConArms_closed : Minidregg.Theory.BendTT.Term.Closed wordConArmsDef.v := by intro σ; rfl

private theorem wordType_zero (bk : Book) (binding : WordBookBinding bk) :
    Pars bk (wordType 0) (.Ref "Word.Nil") := by
  apply eval_pars (book_check bk binding.checked).2.1
  exact .call binding.word (.cons (fun _ => natTerm_value bk 0) .nil)
    (.prj rfl (.hit rfl (.hit rfl (.done rfl))))

private theorem wordType_succ (bk : Book) (binding : WordBookBinding bk) (width : Nat) :
    Pars bk (wordType (width + 1)) (wordConType width) := by
  apply eval_pars (book_check bk binding.checked).2.1
  exact .call binding.word (.cons (fun _ => natTerm_value bk (width + 1)) .nil)
    (.prj rfl (.miss rfl (by decide) (.hit rfl
      (.prj rfl (.lam rfl (by intro h; cases h) (.hit rfl (.done rfl)))))))

private theorem wordCon_unfold (bk : Book) (binding : WordBookBinding bk) (width : Nat) :
    Pars bk (wordConType width) (wordConShape width) := by
  simpa [wordConType, wordConShape, Term.inst, Term.sub, Subst.one, Subst.up, Subst.lift, natTerm_sub, natTerm_ren, closed_ren (natTerm_closed width)] using
    Pars.step (.app (.delta binding.conType wordCon_closed) (par_refl (natTerm width)))
    (.step (.beta (par_refl _) (par_refl (natTerm width))) .refl)
private theorem wordConFields_unfold (bk : Book) (binding : WordBookBinding bk) (width : Nat) :
    Pars bk (.App .Q1 (.App .Q0 (.Ref "Word.Con.arms") (natTerm width)) (.Lab "WCon"))
      (wordConFields width) := by
  simpa [wordConFields, wordType, Term.inst, Term.sub, Subst.one, Subst.up, Subst.lift, natTerm_sub, natTerm_ren, closed_ren (natTerm_closed width)] using
    Pars.step (.app (.app (.delta binding.conArms wordConArms_closed) (par_refl (natTerm width))) .lab)
    (.step (.app (.beta (par_refl _) (par_refl (natTerm width))) .lab)
      (.step (.hit (par_refl _)) .refl))

/-- General source Word(n) constructor typing, with actual source Nat index and
all five emitted family definitions bound structurally. Q0 p stays in the type;
no runtime p field is invented. -/
theorem wordTerm_typed (bk : Book) (boolBinding : BoolBookBinding bk)
    (_natBinding : NatBookBinding bk) (binding : WordBookBinding bk) (bits : List Bool) :
    Typed bk [] (wordTerm bits) (wordType bits.length) := by
  induction bits with
  | nil =>
    apply Typed.conv (U := .Ref "Word.Nil")
    · apply Typed.conv (U := wordNilDef.v)
      · apply Typed.tup
        · exact Typed.lab (by simp)
        · apply Typed.conv (U := .Enu ["()"])
          · exact Typed.lab (by simp)
          · exact Or.inl ⟨.Enu ["()"], .refl,
              .step (.app (.delta binding.nilArms wordNilArms_closed) .lab)
                (.step (.hit .enu) .refl)⟩
      · exact Or.inl ⟨wordNilDef.v, .refl,
          .step (.delta binding.nilType wordNil_closed) .refl⟩
    · exact Or.inl ⟨.Ref "Word.Nil", .refl, wordType_zero bk binding⟩
  | cons b bits ih =>
    apply Typed.conv (U := wordConType bits.length)
    · apply Typed.conv (U := wordConShape bits.length)
      · apply Typed.tup
        · exact Typed.lab (by simp)
        · apply Typed.conv (U := wordConFields bits.length)
          · exact Typed.tup (boolTerm_typed bk boolBinding b)
              (Typed.tup (by simpa [wordType, Term.inst, Term.sub, Subst.one, natTerm_sub] using ih) (Typed.lab (by simp)))
          · exact Or.inl ⟨wordConFields bits.length, .refl,
              by simpa [Term.inst, Term.sub, Subst.one, natTerm_sub] using wordConFields_unfold bk binding bits.length⟩
      · exact Or.inl ⟨wordConShape bits.length, .refl, wordCon_unfold bk binding bits.length⟩
    · exact Or.inl ⟨wordConType bits.length, .refl, wordType_succ bk binding bits.length⟩

#assert_axioms wordTerm_typed
end Minidregg.Compiler.BendSourceRepresentation
