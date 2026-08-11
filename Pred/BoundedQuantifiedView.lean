/-
# Pred.BoundedQuantifiedView -- finite quantifiers as views of the one Pred AST

Bounded quantification does not add a second policy language.  A finite
universal is the existing `Pred.all` over the instantiated bodies, and a
finite existential is the existing `Pred.any`.  The body function is used
only while constructing that first-order `Pred`; it is not retained in the
policy record or evaluator.

The equal-denotation theorems below are the complete semantic boundary of the
view.  Compiler specializations live downstream in
`Compiler.BoundedQuantifiedPolicyAdmission`, preserving the dependency from
Compiler to Pred.
-/
import Pred.Core

namespace Minidregg.Pred.BoundedQuantifiedView

open Minidregg.Pred

set_option autoImplicit false

/-- Finite universal view.  The result is ordinary, serializable `Pred`
syntax; the meta-level body function is eliminated by `List.map`. -/
def forallView {Index : Type} (range : List Index) (body : Index -> Pred) : Pred :=
  Pred.all (range.map body)

/-- Finite existential view, likewise eliminated to ordinary `Pred` syntax. -/
def existsView {Index : Type} (range : List Index) (body : Index -> Pred) : Pred :=
  Pred.any (range.map body)

/-- The universal view has exactly the bounded universal denotation. -/
theorem eval_forallView {Index : Type} (range : List Index)
    (body : Index -> Pred) (old new : State) :
    Minidregg.Pred.eval (forallView range body) old new =
      range.all (fun index => Minidregg.Pred.eval (body index) old new) := by
  simp [forallView, Minidregg.Pred.eval_all, Function.comp_def]

/-- The existential view has exactly the bounded existential denotation. -/
theorem eval_existsView {Index : Type} (range : List Index)
    (body : Index -> Pred) (old new : State) :
    Minidregg.Pred.eval (existsView range body) old new =
      range.any (fun index => Minidregg.Pred.eval (body index) old new) := by
  simp [existsView, Minidregg.Pred.eval_any, Function.comp_def]

/-! ## Concrete discrimination witnesses -/

def witnessRange : List Bool := [false, true]

def witnessBody : Bool -> Pred
  | false => .eq "left" 1
  | true => .eq "right" 2

def witnessOld : State := { slots := [] }
def witnessGood : State := { slots := [("left", 1), ("right", 2)] }
def witnessBad : State := { slots := [("left", 1), ("right", 3)] }

/-- Both instantiated bodies hold on the good state. -/
theorem witness_forall_accepts :
    Minidregg.Pred.eval (forallView witnessRange witnessBody)
      witnessOld witnessGood = true := by
  decide

/-- The same universal rejects when one instantiated body is changed. -/
theorem witness_forall_rejects :
    Minidregg.Pred.eval (forallView witnessRange witnessBody)
      witnessOld witnessBad = false := by
  decide

/-- The existential still accepts the bad state through its unchanged left arm. -/
theorem witness_exists_accepts :
    Minidregg.Pred.eval (existsView witnessRange witnessBody)
      witnessOld witnessBad = true := by
  decide

end Minidregg.Pred.BoundedQuantifiedView
