/- Actual independently authored workshop helper consumption. Raw source/helper
provenance is retained by the sealed package publisher; these wrappers refer to
exact admitted helper entries. -/
import Compiler.ObjectiveBendLinker
import Compiler.ObjectiveBendOrder
namespace Minidregg.Compiler.ObjectiveBendWorkshop
open Minidregg.Theory.BendTT
open ObjectiveBendComposition ObjectiveBendLinker
set_option autoImplicit false
private abbrev CoreTerm := Minidregg.Theory.BendTT.Term

def pair (a b : CoreTerm) : CoreTerm := .Tup .Q1 a b
def unit : CoreTerm := .Lab "()"
def nat : Nat → CoreTerm
  | 0 => pair (.Lab "Zero") unit
  | n+1 => pair (.Lab "Succ") (pair (nat n) unit)
def bytes : List Nat → CoreTerm
  | [] => pair (.Lab "Nil") unit
  | n::ns => pair (.Lab "Con") (pair (nat n) (pair (bytes ns) unit))
def candidate (revision : Nat) : CoreTerm :=
  pair (.Lab "CatalogReview.Candidate")
    (pair (bytes [1]) (pair (bytes [2]) (pair (nat revision) unit)))
def catalog : CoreTerm := pair (.Lab "ReusableWorkshop.CatalogRow")
  (pair (candidate 1) (pair (bytes [3])
    (pair (pair (.Lab "ReusableWorkshop.EmptyCatalog") unit) unit)))
def interface (selector result : String) : Interface :=
  ⟨selector, .All .Q2 (.Ref "CatalogReview.Candidate") (.Ref result)⟩
def catalogI : Interface := interface "catalog" "ReusableWorkshop.Lookup"
def reviewI : Interface := interface "review" "CatalogReview.Recommendation"
def auditI : Interface := interface "audit" "Bool"
def presentationI : Interface := interface "presentation" "ReusableWorkshop.Card"

/-- Callbacks are exact symbolic self/super demands, elaborated by the common
resolver. Immutable catalog/policy/label are Data expressions at this seam. -/
def specs (source : BendCoreAdmission.Checked) : Except String (List Spec) := do
  let catalogE ← BendCoreAdmission.entry source "ReusableWorkshop.catalog"
  let reviewE ← BendCoreAdmission.entry source "ReusableWorkshop.review_with_policy"
  let focusedE ← BendCoreAdmission.entry source "MemberExtension.focused_review"
  let presentationE ← BendCoreAdmission.entry source "ReusableWorkshop.presentation_with_label"
  let auditE ← BendCoreAdmission.entry source "MemberExtension.audit"
  let alternateE ← BendCoreAdmission.entry source "MemberExtension.alternate_presentation"
  pure [
    ⟨1, [], [1], [], [fromEntry catalogE 2 catalogI [(.Q1, catalog)]]⟩,
    ⟨2, [1], [1,2], [⟨.finalSelf, catalogI⟩],
      [fromEntry reviewE 2 reviewI [(.Q1, bytes [4]), (.Q1, .Ref "self.catalog")]]⟩,
    ⟨3, [2], [1,2,3], [⟨.priorSuper, reviewI⟩, ⟨.finalSelf, auditI⟩],
      [fromEntry focusedE 3 reviewI [(.Q1, .Ref "super.review"), (.Q1, .Ref "self.audit")]]⟩,
    ⟨4, [3], [1,2,3,4], [⟨.finalSelf, reviewI⟩],
      [fromEntry presentationE 2 presentationI [(.Q1, bytes [5]), (.Q1, .Ref "self.review")]]⟩,
    ⟨5, [4], [1,2,3,4,5], [], [fromEntry auditE 3 auditI []]⟩,
    ⟨6, [5], [1,2,3,4,5,6], [⟨.finalSelf, reviewI⟩],
      [fromEntry alternateE 3 presentationI [(.Q1, .Ref "self.review")]]⟩]

def checkCase (source : BendCoreAdmission.Checked) (label : String) (layers : List Spec) (expectedIncomplete : Bool) : IO Unit := do
  match layers.getLast? with
  | none => throw (IO.userError "empty composition")
  | some root =>
    if (ObjectiveBendOrder.check root layers).isNone then
      throw (IO.userError (label ++ ": unlawful behavior order"))
  match linkSource source layers with
  | .error (.incompleteMethod owner required) =>
    if expectedIncomplete && owner == 3 && required.interface.selector == "audit" then
      IO.println (label ++ ": EXPECTED missing finalSelf.audit at owner 3")
    else throw (IO.userError (label ++ ": unexpected incomplete method"))
  | .error diagnostic => throw (IO.userError (label ++ ": " ++ reprStr diagnostic))
  | .ok linked =>
    if expectedIncomplete then throw (IO.userError "incomplete audit incorrectly linked")
    IO.println (label ++ ": LINKED exact methods/helpers, definitions=" ++ toString linked.core.book.length)

def run (path : String) : IO Unit := do
  let raw ← IO.FS.readBinFile path
  let source ← match BendCoreAdmission.canonicalize raw.toList with
    | .error e => throw (IO.userError e)
    | .ok source => pure source
  let layers ← match specs source with
    | .error e => throw (IO.userError e)
    | .ok layers => pure layers
  checkCase source "incomplete audit" (layers.take 4) true
  checkCase source "third member completion" (layers.take 5) false
  checkCase source "alternate presentation" layers false

end Minidregg.Compiler.ObjectiveBendWorkshop
