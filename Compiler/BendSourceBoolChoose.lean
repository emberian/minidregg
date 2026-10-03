import Compiler.BendSourceTypedRepresentation
import Compiler.BendLogicMux
namespace Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false
open Minidregg.Theory.BendTT

/-- Exact captured safe_emit source of SourceBool.choose(c,a,b). The selector
is split before the remaining two Q1 arms are bound; this is not the previous
bare enum core lambda tree or a guess about elaboration. -/
def chooseTerm : BTerm := .Prj (.Mat "False"
  (unitArm (.Lam .Q1 (.Lam .Q1 (.Var 0))))
  (.Mat "True" (unitArm (.Lam .Q1 (.Lam .Q1 (.Var 1)))) .Efq))
theorem choose_closed : Minidregg.Theory.BendTT.Term.Closed chooseTerm := by
  intro σ; rfl
theorem choose_live (bk : Book) : Minidregg.Theory.BendTT.Term.Live bk chooseTerm := by rfl

def chooseType : BTerm := .All .Q1 (.Ref "Bool")
  (.All .Q1 (.Ref "Bool") (.All .Q1 (.Ref "Bool") (.Ref "Bool")))
def chooseDef : Def := ⟨"SourceBool.choose", chooseType, chooseTerm, false⟩
def emittedChooseBook : Book := [chooseDef, armsDef, boolDef]
def chooseCall (selector onTrue onFalse : Bool) : BTerm :=
  .App .Q1 (.App .Q1 (.App .Q1 (.Ref "SourceBool.choose") (boolTerm selector))
    (boolTerm onTrue)) (boolTerm onFalse)

theorem source_choose_walk (bk : Book) (selector onTrue onFalse : Bool) :
    Walk bk chooseTerm [] [(.Q1, boolTerm selector), (.Q1, boolTerm onTrue),
      (.Q1, boolTerm onFalse)] (some (boolTerm (BendLogicMux.result selector onTrue onFalse))) := by
  cases selector with
  | false => exact .prj rfl (.hit rfl (.hit rfl
      (.lam rfl (by intro h; cases h) (.lam rfl (by intro h; cases h) (.done rfl)))))
  | true => exact .prj rfl (.miss rfl (by decide) (.hit rfl (.hit rfl
      (.lam rfl (by intro h; cases h) (.lam rfl (by intro h; cases h) (.done rfl))))))

theorem source_choose_call (bk : Book)
    (binding : Book.get bk "SourceBool.choose" = some chooseDef)
    (selector onTrue onFalse : Bool) :
    Eval bk (chooseCall selector onTrue onFalse)
      (boolTerm (BendLogicMux.result selector onTrue onFalse)) := by
  exact .call binding (.cons (fun _ => boolTerm_value bk selector)
    (.cons (fun _ => boolTerm_value bk onTrue) (.cons (fun _ => boolTerm_value bk onFalse) .nil)))
    (source_choose_walk bk selector onTrue onFalse)

/-- Same dynamic mux AIR and original wire ABI, arbitrary auxiliary witness,
actual authored Base Bool method call. Cipher/key/domain admission is separate. -/
theorem descriptor_choose_source_sound {F : Type} [Field F] (bk : Book)
    (binding : Book.get bk "SourceBool.choose" = some chooseDef) (nPublic : Nat)
    (selector onTrue onFalse output : Bool) (wv : Nat → F)
    (pinned : ∀ i : Fin 4, wv i.val = BendLogicMux.assignment selector onTrue onFalse output i)
    (holds : descriptorHolds (BendLogicMux.descriptor nPublic) wv) :
    Eval bk (chooseCall selector onTrue onFalse) (boolTerm output) := by
  have correct := (BendLogicMux.descriptor_correct nPublic selector onTrue onFalse output).mp
    ⟨wv, pinned, holds⟩
  rw [correct]
  exact source_choose_call bk binding selector onTrue onFalse

#assert_axioms choose_closed
#assert_axioms choose_live
#assert_axioms source_choose_walk
#assert_axioms source_choose_call
#assert_axioms descriptor_choose_source_sound
end Minidregg.Compiler.BendSourceRepresentation
