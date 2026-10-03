/- Executable source construction discharges lawful ancestry, completion and
captured Data rather than asking a host caller to assert those predicates. -/
import Compiler.ObjectiveBendLinker
import Compiler.ObjectiveBendOrder
import Theory.BendLiveMachine
import Theory.AssertAxioms
namespace Minidregg.Compiler.ObjectiveBendConstruction
open Minidregg.Theory.BendTT
open ObjectiveBendComposition ObjectiveBendElaboration ObjectiveBendLinker
set_option autoImplicit false

structure Certified (claim : Prop) : Type where
  valid : claim

def checkAll {α : Type} {P : α → Prop} (check : (a : α) → Option (Certified (P a))) :
    (values : List α) → Option (Certified (∀ a ∈ values, P a))
  | [] => some ⟨by simp⟩
  | head :: tail => do
    let first ← check head
    let rest ← checkAll check tail
    pure ⟨by
      intro a present
      rcases List.mem_cons.mp present with same | later
      · subst a; exact first.valid
      · exact rest.valid a later⟩

def captures (layers : List Spec) : Option (Certified
    (∀ spec ∈ layers, ∀ provision ∈ spec.provisions, capturedData provision)) :=
  checkAll (fun spec => checkAll (fun provision =>
    checkAll (fun term => (Minidregg.Theory.BendLiveMachine.checkData term).map
      (fun qualified => ⟨qualified.valid⟩)) provision.captured) spec.provisions) layers

inductive Refusal where
  | unlawfulOrder
  | incomplete
  | notCapturedData
  | link (diagnostic : Diagnostic)
  deriving Repr

/-- Every returned Construction owns exact resolved entry definitions in the
actual checked core, plus finite checked ancestry and real Data witnesses. -/
def construct (helpers : Book) (root : Spec) (layers : List Spec) : Except Refusal Construction := do
  let some lawful := ObjectiveBendOrder.check root layers | throw .unlawfulOrder
  let linked ← (link helpers layers).mapError Refusal.link
  if complete : closed layers = true then
    let some qualified := captures layers | throw .notCapturedData
    pure (construction linked root lawful complete qualified.valid)
  else throw .incomplete

#assert_axioms checkAll
#assert_axioms captures
#assert_axioms construct
end Minidregg.Compiler.ObjectiveBendConstruction
