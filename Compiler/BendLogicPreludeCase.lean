/- Specialize actual pinned safe.ts Prelude Bool (tag,unit) source layout.
This consumes the representation producer and SAME Plan/Air/DAG, not another
compiler or interpreter. Book binding checks actual Bool/Bool.arms definitions;
method compilation also pins selected interface/body and refuses opaque code.
Current authority, source package attribution and ciphertext validity remain
with their producers/receivers. Public source specialization only. -/
import Compiler.BendSourceTypedRepresentation
import Theory.BendLiveMachine

namespace Minidregg.Compiler.BendLogicPreludeCase

open BendLogicCase
open BendLogicSpecialization (BTerm BBook)
open Minidregg.Theory.BendLiveMachine
set_option autoImplicit false

def compile {F : Type} [Field F] (nPublic : Nat) (source : BTerm) (plan : Plan) :
    Option (ConstraintDescriptor F) :=
  if nPublic ≤ 2 ∧ source = BendSourceRepresentation.sourceTerm plan then
    some (descriptor nPublic plan) else none

theorem compile_exact {F : Type} [Field F] {nPublic : Nat} {source : BTerm}
    {plan : Plan} {d : ConstraintDescriptor F}
    (accepted : compile nPublic source plan = some d) :
    nPublic ≤ 2 ∧ source = BendSourceRepresentation.sourceTerm plan ∧
      d = descriptor nPublic plan := by
  unfold compile at accepted
  split at accepted
  · rename_i h
    exact ⟨h.1, h.2, (Option.some.inj accepted).symm⟩
  · contradiction

theorem compiled_descriptor_source_sound {F : Type} [Field F] (book : BBook)
    {nPublic : Nat} {source : BTerm} {plan : Plan} {d : ConstraintDescriptor F}
    (accepted : compile nPublic source plan = some d)
    (input output : Bool) (wv : Nat → F)
    (pinned : ∀ i : Fin 2, wv i.val = assignment input output i)
    (holds : descriptorHolds d wv) :
    BendLogicSpecialization.Normalizes book
      (.App .Q1 source (BendSourceRepresentation.boolTerm input))
      (BendSourceRepresentation.boolTerm output) := by
  obtain ⟨_, sourceExact, descriptorExact⟩ := compile_exact accepted
  rw [sourceExact]
  exact BendSourceRepresentation.descriptor_source_sound book nPublic plan input output
    wv pinned (descriptorExact ▸ holds)

/-- Actual dependent type definitions and whole Book check, not caller tags. -/
def bookBinding (book : BBook) : Bool :=
  decide (Minidregg.Theory.BendTT.Book.get book "Bool.arms" =
    some BendSourceRepresentation.armsDef) &&
  decide (Minidregg.Theory.BendTT.Book.get book "Bool" =
    some BendSourceRepresentation.boolDef) &&
  decide (Minidregg.Theory.BendTT.Book.check book = .ok ())

theorem bookBinding_sound {book : BBook} (bound : bookBinding book = true) :
    BendSourceRepresentation.BoolBookBinding book := by
  simp only [bookBinding, Bool.and_eq_true, decide_eq_true_eq] at bound
  exact ⟨bound.1.1, bound.1.2, bound.2⟩

def sourceType : BTerm := .All .Q1 (.Ref "Bool") (.Ref "Bool")

def compileEntry {F : Type} [Field F] (nPublic : Nat) (book : BBook)
    (entry : String) (plan : Plan) : Option (ConstraintDescriptor F) := do
  let definition ← Minidregg.Theory.BendTT.Book.get book entry
  if definition.o then none else
    if definition.T = sourceType ∧ bookBinding book = true then
      compile nPublic definition.v plan else none

theorem compileEntry_exact {F : Type} [Field F] {nPublic : Nat} {book : BBook}
    {entry : String} {plan : Plan} {d : ConstraintDescriptor F}
    (accepted : compileEntry nPublic book entry plan = some d) :
    ∃ definition, Minidregg.Theory.BendTT.Book.get book entry = some definition ∧
      definition.o = false ∧ definition.T = sourceType ∧
      BendSourceRepresentation.BoolBookBinding book ∧
      definition.v = BendSourceRepresentation.sourceTerm plan ∧
      nPublic ≤ 2 ∧ d = descriptor nPublic plan := by
  unfold compileEntry at accepted
  cases found : Minidregg.Theory.BendTT.Book.get book entry with
  | none => simp [found] at accepted
  | some definition =>
      cases isOpaque : definition.o with
      | true => simp [found, isOpaque] at accepted
      | false =>
          have selected : (if definition.T = sourceType ∧ bookBinding book = true then
              compile nPublic definition.v plan else none) = some d := by
            simpa [found, isOpaque] using accepted
          split at selected
          · rename_i admitted
            obtain ⟨bounded, exactBody, exactDescriptor⟩ := compile_exact selected
            exact ⟨definition, rfl, isOpaque, admitted.1, bookBinding_sound admitted.2,
              exactBody, bounded, exactDescriptor⟩
          · contradiction

def invocation (entry : String) (input : Bool) : BTerm :=
  .App .Q1 (.Ref entry) (BendSourceRepresentation.boolTerm input)

/-- Walk splits the live constructor pair and consumes its exact unit tail. -/
theorem source_walk (book : BBook) (plan : Plan) (input : Bool) :
    Minidregg.Theory.BendTT.Walk book (BendSourceRepresentation.sourceTerm plan) []
      [(.Q1, BendSourceRepresentation.boolTerm input)]
      (some (BendSourceRepresentation.boolTerm (plan.output input))) := by
  cases input with
  | false => exact .prj rfl (.hit rfl (.hit rfl (.done rfl)))
  | true => exact .prj rfl (.miss rfl (by decide) (.hit rfl (.hit rfl (.done rfl))))

theorem compiled_entry_trace_sound {F : Type} [Field F] {nPublic : Nat}
    {book : BBook} {entry : String} {plan : Plan} {d : ConstraintDescriptor F}
    (accepted : compileEntry nPublic book entry plan = some d)
    (input output : Bool) (wv : Nat → F)
    (pinned : ∀ i : Fin 2, wv i.val = assignment input output i)
    (holds : descriptorHolds d wv) :
    Trace book 1 (invocation entry input) (BendSourceRepresentation.boolTerm output) := by
  obtain ⟨definition, found, _, _, _, exactBody, _, exactDescriptor⟩ :=
    compileEntry_exact accepted
  have correct : output = plan.output input :=
    (descriptor_correct nPublic plan input output).mp ⟨wv, pinned, exactDescriptor ▸ holds⟩
  rw [correct]
  apply Trace.step
  · apply Minidregg.Theory.BendTT.Eval.call found
      (.cons (fun _ => BendSourceRepresentation.boolTerm_value book input) .nil)
    rw [exactBody]
    exact source_walk book plan input
  · exact .refl _

#assert_axioms compile_exact
#assert_axioms compiled_descriptor_source_sound
#assert_axioms bookBinding_sound
#assert_axioms compileEntry_exact
#assert_axioms source_walk
#assert_axioms compiled_entry_trace_sound

end Minidregg.Compiler.BendLogicPreludeCase
