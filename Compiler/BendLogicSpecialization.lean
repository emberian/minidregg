/-
Source adapter for the exact BendTT kernel at 947db722640c86247849343657bf2f7ef01cb7f1.
The source module is namespace-wrapped upstream code, not a substitute semantics.
This first block accepts a complete literal Boolean enum case tree and compiles
it through BendLogicCase -> Air -> AirFlatten -> Emit. It rejects other syntax.
A reusable fixed-program descriptor has two original variables and a selected
public prefix. The relation computes private input -> private/public output;
it does not verify the upstream checker, establish a zk proof, or bind a world
root. Those outer bindings and the proof consumer have separate obligations.
-/
import Theory.BendTTSource
import Compiler.BendLogicCase
import Mathlib.Logic.Relation

namespace Minidregg.Compiler.BendLogicSpecialization

set_option autoImplicit false
open BendLogicCase

abbrev BTerm := Minidregg.Theory.BendTT.Term
abbrev BBook := Minidregg.Theory.BendTT.Book
abbrev BQuan := Minidregg.Theory.BendTT.Quan

/-- Exact label syntax, not a native integer representation. -/
def label (b : Bool) : BTerm := .Lab (if b then "true" else "false")

def sourceTerm (p : Plan) : BTerm :=
  .Mat "false" (label p.onFalse) (.Mat "true" (label p.onTrue) .Efq)

def inputTerm (p : Plan) (input : Bool) : BTerm :=
  .App .Q1 (sourceTerm p) (label input)

abbrev Normalizes (bk : BBook) :=
  Relation.ReflTransGen (Minidregg.Theory.BendTT.Eval bk)

theorem label_injective : Function.Injective label := by
  intro a b h
  cases a <;> cases b <;> simp_all [label]

def booleanType : BTerm := .Enu ["false", "true"]

theorem label_typed (bk : BBook) (b : Bool) :
    Minidregg.Theory.BendTT.Typed bk [] (label b) booleanType := by
  cases b <;> exact Minidregg.Theory.BendTT.Typed.lab (by simp [booleanType])

theorem source_closed (p : Plan) :
    Minidregg.Theory.BendTT.Term.Closed (sourceTerm p) := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> intro substitution <;> rfl

theorem source_live (bk : BBook) (p : Plan) :
    Minidregg.Theory.BendTT.Term.Live bk (sourceTerm p) := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- Complete source case coverage is typed over the two labels, including the
empty fallback. Compilation itself still requires the receiving Book admission. -/
theorem source_typed (bk : BBook) (p : Plan) :
    Minidregg.Theory.BendTT.Typed bk [] (sourceTerm p)
      (.All .Q1 booleanType booleanType) := by
  apply Minidregg.Theory.BendTT.Typed.mat rfl (by simp [booleanType])
  · exact label_typed bk p.onFalse
  · apply Minidregg.Theory.BendTT.Typed.mat rfl (by simp [booleanType])
    · exact label_typed bk p.onTrue
    · exact Minidregg.Theory.BendTT.Typed.efq rfl

/-- This is actual upstream live CBV Eval, not checker WNF. The case tree
requires one hit for false, a miss and hit for true. -/
theorem source_normalizes (bk : BBook) (p : Plan) (input : Bool) :
    Normalizes bk (inputTerm p input) (label (p.output input)) := by
  cases input with
  | false =>
      exact Relation.ReflTransGen.single
        (Minidregg.Theory.BendTT.Eval.hit rfl)
  | true =>
      exact (Relation.ReflTransGen.single
        (Minidregg.Theory.BendTT.Eval.miss rfl (by decide))).trans
        (Relation.ReflTransGen.single
          (Minidregg.Theory.BendTT.Eval.hit rfl))

/-- A caller may propose a specialization, but equality to the full source
case tree is checked. Missing branches, Q0 calls, altered labels and fallback
code cannot acquire this artifact. The public split must fit its two inputs. -/
def compile {F : Type} [Field F] (nPublic : Nat) (source : BTerm)
    (candidate : Plan) : Option (ConstraintDescriptor F) :=
  if nPublic ≤ 2 ∧ source = sourceTerm candidate then
    some (descriptor nPublic candidate)
  else none

theorem compile_exact {F : Type} [Field F] {nPublic : Nat} {source : BTerm}
    {candidate : Plan} {d : ConstraintDescriptor F}
    (accepted : compile nPublic source candidate = some d) :
    nPublic ≤ 2 ∧ source = sourceTerm candidate ∧ d = descriptor nPublic candidate := by
  unfold compile at accepted
  split at accepted
  · rename_i h
    cases accepted
    exact ⟨h.1, h.2, rfl⟩
  · cases accepted

/-- Full source -> serialized descriptor -> arbitrary satisfying witness ->
upstream normalized result. Original input/output tags are externally pinned;
there is no trusted canonical-witness premise. -/
theorem compiled_descriptor_source_sound {F : Type} [Field F] (bk : BBook)
    {nPublic : Nat} {source : BTerm} {candidate : Plan} {d : ConstraintDescriptor F}
    (accepted : compile nPublic source candidate = some d)
    (input output : Bool) (wv : Nat → F)
    (pinned : ∀ i : Fin 2, wv i.val = assignment input output i)
    (holds : descriptorHolds d wv) :
    Normalizes bk (.App .Q1 source (label input)) (label output) := by
  obtain ⟨_, hs, hd⟩ := compile_exact accepted
  rw [hs]
  have correct : output = candidate.output input :=
    (descriptor_correct nPublic candidate input output).mp ⟨wv, pinned, hd ▸ holds⟩
  rw [correct]
  exact source_normalizes bk candidate input

/-- The same fixed artifact has a satisfying descriptor vector for every
Boolean input, and its source normalizes to precisely the selected output. -/
theorem compiled_descriptor_complete {F : Type} [Field F] (nPublic : Nat)
    (candidate : Plan) (input : Bool) :
    ∃ wv : Nat → F,
      (∀ i : Fin 2, wv i.val = assignment input (candidate.output input) i) ∧
      descriptorHolds (descriptor nPublic candidate) wv :=
  (descriptor_correct nPublic candidate input (candidate.output input)).mpr rfl

def negation : Plan := ⟨true, false⟩

theorem negation_source_normalizes (bk : BBook) (input : Bool) :
    Normalizes bk (inputTerm negation input) (label (!input)) := by
  cases input <;> exact source_normalizes bk negation _

#assert_axioms label_typed
#assert_axioms source_live
#assert_axioms source_closed
#assert_axioms source_typed
#assert_axioms label_injective
#assert_axioms source_normalizes
#assert_axioms compile_exact
#assert_axioms compiled_descriptor_source_sound
#assert_axioms compiled_descriptor_complete
#assert_axioms negation_source_normalizes

end Minidregg.Compiler.BendLogicSpecialization
