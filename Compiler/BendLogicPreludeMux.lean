/- Specialize actual pinned safe.ts Prelude Bool (tag,unit) source layout.
This consumes the captured selector producer and SAME dynamic Air/DAG, not another
compiler or interpreter. Book binding checks actual Bool/Bool.arms definitions;
method compilation also pins selected interface/body and refuses opaque code.
Current authority, source package attribution and ciphertext validity remain
with their producers/receivers. Public source specialization only. -/
import Compiler.BendSourceBoolChoose
import Compiler.BendLogicPreludeCase
import Theory.BendLiveMachine

namespace Minidregg.Compiler.BendLogicPreludeMux

open BendLogicMux
open BendLogicSpecialization (BTerm BBook)
open Minidregg.Theory.BendLiveMachine
set_option autoImplicit false

def compile {F : Type} [Field F] (nPublic : Nat) (source : BTerm) :
    Option (ConstraintDescriptor F) :=
  if nPublic ≤ 4 ∧ source = BendSourceRepresentation.chooseTerm then
    some (descriptor nPublic) else none

theorem compile_exact {F : Type} [Field F] {nPublic : Nat} {source : BTerm}
    {d : ConstraintDescriptor F} (accepted : compile nPublic source = some d) :
    nPublic ≤ 4 ∧ source = BendSourceRepresentation.chooseTerm ∧
      d = descriptor nPublic := by
  unfold compile at accepted
  split at accepted
  · rename_i h
    exact ⟨h.1, h.2, (Option.some.inj accepted).symm⟩
  · contradiction

/-- Reuse the same exact dependent Bool Book admission. -/
def bookBinding := BendLogicPreludeCase.bookBinding

theorem bookBinding_sound {book : BBook} (bound : bookBinding book = true) :
    BendSourceRepresentation.BoolBookBinding book :=
  BendLogicPreludeCase.bookBinding_sound bound

def sourceType : BTerm := BendSourceRepresentation.chooseType

def compileEntry {F : Type} [Field F] (nPublic : Nat) (book : BBook)
    (entry : String) : Option (ConstraintDescriptor F) := do
  let definition ← Minidregg.Theory.BendTT.Book.get book entry
  if definition.o then none else
    if definition.T = sourceType ∧ bookBinding book = true then
      compile nPublic definition.v else none

theorem compileEntry_exact {F : Type} [Field F] {nPublic : Nat} {book : BBook}
    {entry : String} {d : ConstraintDescriptor F}
    (accepted : compileEntry nPublic book entry = some d) :
    ∃ definition, Minidregg.Theory.BendTT.Book.get book entry = some definition ∧
      definition.o = false ∧ definition.T = sourceType ∧
      BendSourceRepresentation.BoolBookBinding book ∧
      definition.v = BendSourceRepresentation.chooseTerm ∧
      nPublic ≤ 4 ∧ d = descriptor nPublic := by
  unfold compileEntry at accepted
  cases found : Minidregg.Theory.BendTT.Book.get book entry with
  | none => simp [found] at accepted
  | some definition =>
      cases isOpaque : definition.o with
      | true => simp [found, isOpaque] at accepted
      | false =>
          have selected : (if definition.T = sourceType ∧ bookBinding book = true then
              compile nPublic definition.v else none) = some d := by
            simpa [found, isOpaque] using accepted
          split at selected
          · rename_i admitted
            obtain ⟨bounded, exactBody, exactDescriptor⟩ := compile_exact selected
            exact ⟨definition, rfl, isOpaque, admitted.1, bookBinding_sound admitted.2,
              exactBody, bounded, exactDescriptor⟩
          · contradiction

def invocation (entry : String) (selector onTrue onFalse : Bool) : BTerm :=
  .App .Q1 (.App .Q1 (.App .Q1 (.Ref entry)
    (BendSourceRepresentation.boolTerm selector))
    (BendSourceRepresentation.boolTerm onTrue)) (BendSourceRepresentation.boolTerm onFalse)

/-- Arbitrary satisfying AIR witnesses refine the selected actual source call.
The public source specializes; ciphertext validity and world authority are not
inferred from a descriptor, a body match or the Book checker. -/
theorem compiled_entry_trace_sound {F : Type} [Field F] {nPublic : Nat}
    {book : BBook} {entry : String} {d : ConstraintDescriptor F}
    (accepted : compileEntry nPublic book entry = some d)
    (selector onTrue onFalse output : Bool) (wv : Nat → F)
    (pinned : ∀ i : Fin 4, wv i.val = assignment selector onTrue onFalse output i)
    (holds : descriptorHolds d wv) :
    Trace book 1 (invocation entry selector onTrue onFalse)
      (BendSourceRepresentation.boolTerm output) := by
  obtain ⟨definition, found, _, _, _, exactBody, _, exactDescriptor⟩ :=
    compileEntry_exact accepted
  have correct : output = result selector onTrue onFalse :=
    (descriptor_correct nPublic selector onTrue onFalse output).mp
      ⟨wv, pinned, exactDescriptor ▸ holds⟩
  rw [correct]
  apply Trace.step
  · apply Minidregg.Theory.BendTT.Eval.call found
      (.cons (fun _ => BendSourceRepresentation.boolTerm_value book selector)
        (.cons (fun _ => BendSourceRepresentation.boolTerm_value book onTrue)
          (.cons (fun _ => BendSourceRepresentation.boolTerm_value book onFalse) .nil)))
    rw [exactBody]
    exact BendSourceRepresentation.source_choose_walk book selector onTrue onFalse
  · exact .refl _

#assert_axioms compile_exact
#assert_axioms bookBinding_sound
#assert_axioms compileEntry_exact
#assert_axioms compiled_entry_trace_sound

end Minidregg.Compiler.BendLogicPreludeMux
