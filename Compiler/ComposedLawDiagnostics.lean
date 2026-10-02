/- Admission uses the complete closure. Public explanations require authority
for both their source origin and their disclosed target slots. -/
import Compiler.ComposedPolicyAdmission
import Compiler.PredRangeLeaf

namespace Minidregg.Compiler.ComposedLawDiagnostics

open Minidregg.Pred
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.LawComposition
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.ComposedPolicyAdmission

set_option autoImplicit false

structure OriginFailure where
  origin : Key
  leaf : Option LawLeaf

/-- Internal provenance only. A child read grant is not authorization to render
this origin, its identifier, or any ancestor clause or operand. -/
def internalFailure (nodes : List Node) (old new : State) : Option OriginFailure := do
  let node ← (canonicalOrder nodes).find? fun node =>
    !Minidregg.Pred.eval node.component.guarded old new
  pure ⟨node.key, LawLeaf.of node.component.guarded old new⟩

/-- This function receives only the exact target-local source, whose observation
has already been authorized, and the fields that same capability discloses.
Inherited policies and their identities cannot influence the detail returned.
A separately authenticated origin-inspection path may expose internalFailure. -/
def localRefusal {F : Type} [Field F] [DecidableEq F]
    (profile : CompilerProfile) (fields : Option (Finset CellField))
    (predicate : Pred) (old new : State) : Refusal :=
  match LawLeaf.ofRange profile predicate old new with
  | some leaf => Refusal.lawInputRangeFor fields leaf
  | none =>
      match castAlias F (intsOf predicate old new) with
      | some (x, y) => Refusal.castAliasFor fields x y
      | none => Refusal.lawDeniedFor fields predicate old new

def publicRefusal {F : Type} [Field F] [DecidableEq F] {config : Config F}
    (fields : Option (Finset CellField)) (law : PreparedLaw config) : Refusal :=
  localRefusal (F := F) config.profile.compiler fields
    law.head.committed.record.localComponent.guarded config.step.oldState config.step.newState

/-- Changing hidden ancestors cannot change public failure details when the
selected target-local source and authorized projection stay identical. The
full admission verdict still depends on every authenticated restriction. -/
theorem hidden_origins_do_not_change_details {F : Type} [Field F] [DecidableEq F]
    {left right : Config F} (a : PreparedLaw left) (b : PreparedLaw right)
    (fields : Option (Finset CellField))
    (sameProfile : left.profile.compiler = right.profile.compiler)
    (sameLocal : a.head.committed.record.localComponent = b.head.committed.record.localComponent)
    (sameOld : left.step.oldState = right.step.oldState)
    (sameNew : left.step.newState = right.step.newState) :
    publicRefusal fields a = publicRefusal fields b := by
  simp only [publicRefusal, sameProfile, sameLocal, sameOld, sameNew]

end Minidregg.Compiler.ComposedLawDiagnostics
