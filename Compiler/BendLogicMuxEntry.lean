/- Objective Bend specialization joins an ACTUAL resolved Book definition.
Pure blocks have no object/world effects. The installed Book's typing, source
attribution, method resolution, current authority and ciphertext validity stay
with their existing producers/receivers. Ref invocation uses source Walk, not
an invented inline evaluator, and has one source Eval.call step. -/
import Compiler.BendLogicMux

namespace Minidregg.Compiler.BendLogicMuxEntry

open BendLogicSpecialization
open Minidregg.Theory.BendTT
open Minidregg.Theory.BendLiveMachine
set_option autoImplicit false

def arguments (selector onTrue onFalse : Bool) : List Arg :=
  [(.Q1, label selector), (.Q1, label onTrue), (.Q1, label onFalse)]

def invocation (entry : String) (selector onTrue onFalse : Bool) : BTerm :=
  Minidregg.Theory.BendTT.Term.spine (.Ref entry) (arguments selector onTrue onFalse)

theorem label_value (book : Book) (b : Bool) : Value book (label b) := by
  cases b <;> exact .lab

theorem arguments_values (book : Book) (selector onTrue onFalse : Bool) :
    Values book (arguments selector onTrue onFalse) :=
  .cons (fun _ => label_value book selector)
    (.cons (fun _ => label_value book onTrue)
      (.cons (fun _ => label_value book onFalse) .nil))

/-- Walk follows exact source lambdas, environment lookup and case dispatch.
There is no constraint/proof oracle hidden in the source execution claim. -/
theorem source_walk (book : Book) (selector onTrue onFalse : Bool) :
    Walk book BendLogicMux.sourceTerm [] (arguments selector onTrue onFalse)
      (some (label (BendLogicMux.result selector onTrue onFalse))) := by
  cases selector with
  | false =>
      exact .lam rfl (by intro h; cases h)
        (.lam rfl (by intro h; cases h)
          (.lam rfl (by intro h; cases h)
            (.app rfl (.hit rfl (.done rfl)))))
  | true =>
      exact .lam rfl (by intro h; cases h)
        (.lam rfl (by intro h; cases h)
          (.lam rfl (by intro h; cases h)
            (.app rfl (.miss rfl (by decide) (.hit rfl (.done rfl))))))

/-- This checks the actual selected definition, including transparent entry
and complete source-body equality; attributed source metadata is insufficient. -/
def compile {F : Type} [Field F] (nPublic : Nat) (book : Book) (entry : String) :
    Option (ConstraintDescriptor F) := do
  let definition ← Book.get book entry
  if definition.o then none else
    if definition.T = BendLogicMux.sourceType then
      BendLogicMux.compile nPublic definition.v else none

theorem compile_exact {F : Type} [Field F] {nPublic : Nat} {book : Book}
    {entry : String} {d : ConstraintDescriptor F}
    (accepted : compile nPublic book entry = some d) :
    ∃ definition, Book.get book entry = some definition ∧ definition.o = false ∧
      definition.T = BendLogicMux.sourceType ∧ definition.v = BendLogicMux.sourceTerm ∧ nPublic ≤ 4 ∧
      d = BendLogicMux.descriptor nPublic := by
  unfold compile at accepted
  cases found : Book.get book entry with
  | none => simp [found] at accepted
  | some definition =>
      cases isOpaque : definition.o with
      | true => simp [found, isOpaque] at accepted
      | false =>
          have selected : (if definition.T = BendLogicMux.sourceType then
              BendLogicMux.compile nPublic definition.v else none) = some d := by
            simpa [found, isOpaque] using accepted
          split at selected
          · rename_i exactType
            have body : BendLogicMux.compile nPublic definition.v = some d := selected
            obtain ⟨bounded, exactBody, exactDescriptor⟩ := BendLogicMux.compile_exact body
            exact ⟨definition, rfl, isOpaque, exactType, exactBody, bounded, exactDescriptor⟩
          · contradiction

/-- General specialization theorem for a resolved authored method: every
satisfying auxiliary witness yields the real Ref-entry Eval/Walk outcome.
The inline source count4/5 is deliberately not assigned to this one-step call. -/
theorem compiled_entry_trace_sound {F : Type} [Field F] {nPublic : Nat}
    {book : Book} {entry : String} {d : ConstraintDescriptor F}
    (accepted : compile nPublic book entry = some d)
    (selector onTrue onFalse output : Bool) (wv : Nat → F)
    (pinned : ∀ i : Fin 4,
      wv i.val = BendLogicMux.assignment selector onTrue onFalse output i)
    (holds : descriptorHolds d wv) :
    Trace book 1 (invocation entry selector onTrue onFalse) (label output) := by
  obtain ⟨definition, found, _, _, body, _, exactDescriptor⟩ := compile_exact accepted
  have correct : output = BendLogicMux.result selector onTrue onFalse :=
    (BendLogicMux.descriptor_correct nPublic selector onTrue onFalse output).mp
      ⟨wv, pinned, exactDescriptor ▸ holds⟩
  rw [correct]
  apply Trace.step
  · apply Eval.call found (arguments_values book selector onTrue onFalse)
    rw [body]
    exact source_walk book selector onTrue onFalse
  · exact .refl _

#assert_axioms label_value
#assert_axioms arguments_values
#assert_axioms source_walk
#assert_axioms compile_exact
#assert_axioms compiled_entry_trace_sound

end Minidregg.Compiler.BendLogicMuxEntry
