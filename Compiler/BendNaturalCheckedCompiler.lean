/- Receipt-backed source compilation. Reuses actual immutable core admission;
the saved Book.check proof is consumed, not an unproved Boolean/cache flag.
Compilation still checks exact selected definition/type/body and Nat family. -/
import Compiler.BendNaturalCompiler
import Compiler.BendCoreAdmission
import Compiler.BendLogicPreludeMux

namespace Minidregg.Compiler.BendNaturalExpression
open Minidregg.Theory.BendTT
open BendSourceRepresentation
set_option autoImplicit false

def checkedFamily (core : BendCoreAdmission.Checked) : Bool :=
  decide (Book.get core.book "Nat.arms" = some natArmsDef) &&
  decide (Book.get core.book "Nat" = some natDef) &&
  decide (Book.get core.book "Nat.add" = some natAddDef)

def checkedMethod {n : Nat} (core : BendCoreAdmission.Checked) (entry : String)
    (expr : Expr n) : Bool :=
  decide (Book.get core.book entry = some (definition entry expr)) && checkedFamily core

theorem checkedFamily_eq (core : BendCoreAdmission.Checked) :
    checkedFamily core = BendLogicNatAdd.bookBinding core.book := by
  simp only [checkedFamily, BendLogicNatAdd.bookBinding, core.checked, decide_true, Bool.and_true]

theorem checkedMethod_eq {n : Nat} (core : BendCoreAdmission.Checked) (entry : String)
    (expr : Expr n) : checkedMethod core entry expr = admitMethod core.book entry expr := by
  simp only [checkedMethod, admitMethod, checkedFamily_eq]

def compileChecked {n p : Nat} (core : BendCoreAdmission.Checked) (entry : String) (fuel : Nat)
    (inputBits outputBits sourceBudget plaintextModulus : Nat) : Option (Plan n) := do
  let found ← Book.get core.book entry
  let body ← unwrap n found.v
  let expression ← recover fuel body
  let plan := Plan.mk expression inputBits outputBits sourceBudget plaintextModulus
  if checkedMethod core entry expression && profileAccepted (p := p) plan then some plan else none

/-- Runtime work changes; the source compiler result is exactly the existing
proved compiler for every actual admitted core, entry and public profile. -/
theorem compileChecked_eq {n p : Nat} (core : BendCoreAdmission.Checked) (entry : String)
    (fuel inputBits outputBits sourceBudget plaintextModulus : Nat) :
    compileChecked (n := n) (p := p) core entry fuel inputBits outputBits sourceBudget plaintextModulus =
      compile (n := n) (p := p) core.book entry fuel inputBits outputBits sourceBudget plaintextModulus := by
  simp only [compileChecked, compile, checkedMethod_eq]

theorem compiled_checked_source_complete {n p : Nat} (core : BendCoreAdmission.Checked)
    (entry : String) (fuel inputBits outputBits sourceBudget plaintextModulus : Nat) (plan : Plan n)
    (accepted : compileChecked (p := p) core entry fuel inputBits outputBits sourceBudget plaintextModulus =
      some plan) (inputs : Fin n → Nat) (bounded : ∀ i, inputs i < plan.inputCap) :
    Minidregg.Theory.BendLiveMachine.Trace core.book (1 + plan.expression.sourceCount inputs)
      (invocation entry inputs) (natTerm (plan.expression.value inputs)) ∧
    Typed core.book [] (natTerm (plan.expression.value inputs)) (.Ref "Nat") ∧
    outcome plan.expression inputs plan.sourceBudget = .complete (plan.expression.value inputs) ∧
    plan.expression.value inputs ≤ plan.outputMax ∧
    plan.expression.value inputs < plan.plaintextModulus := by
  exact compiled_source_complete (p := p)
    (by simpa only [compileChecked_eq] using accepted) inputs bounded

#assert_axioms checkedFamily_eq
#assert_axioms checkedMethod_eq
#assert_axioms compileChecked_eq
#assert_axioms compiled_checked_source_complete
end Minidregg.Compiler.BendNaturalExpression

namespace Minidregg.Compiler.BendCheckedPrelude
open Minidregg.Theory.BendTT
set_option autoImplicit false

def family (core : BendCoreAdmission.Checked) : Bool :=
  decide (Book.get core.book "Bool.arms" = some BendSourceRepresentation.armsDef) &&
  decide (Book.get core.book "Bool" = some BendSourceRepresentation.boolDef)

theorem family_eq (core : BendCoreAdmission.Checked) :
    family core = BendLogicPreludeCase.bookBinding core.book := by
  simp only [family, BendLogicPreludeCase.bookBinding, core.checked, decide_true, Bool.and_true]

def unary {F : Type} [Field F] (core : BendCoreAdmission.Checked) (entry : String)
    (nPublic : Nat) (plan : BendLogicCase.Plan) : Option (ConstraintDescriptor F) := do
  let definition ← Book.get core.book entry
  if definition.o then none else
    if definition.T = BendLogicPreludeCase.sourceType ∧ family core = true then
      BendLogicPreludeCase.compile nPublic definition.v plan else none

theorem unary_eq {F : Type} [Field F] (core : BendCoreAdmission.Checked)
    (entry : String) (nPublic : Nat) (plan : BendLogicCase.Plan) :
    unary (F := F) core entry nPublic plan =
      BendLogicPreludeCase.compileEntry nPublic core.book entry plan := by
  simp only [unary, BendLogicPreludeCase.compileEntry, family_eq]

def mux {F : Type} [Field F] (core : BendCoreAdmission.Checked) (entry : String)
    (nPublic : Nat) : Option (ConstraintDescriptor F) := do
  let definition ← Book.get core.book entry
  if definition.o then none else
    if definition.T = BendLogicPreludeMux.sourceType ∧ family core = true then
      BendLogicPreludeMux.compile nPublic definition.v else none

theorem mux_eq {F : Type} [Field F] (core : BendCoreAdmission.Checked)
    (entry : String) (nPublic : Nat) : mux (F := F) core entry nPublic =
      BendLogicPreludeMux.compileEntry nPublic core.book entry := by
  simp only [mux, BendLogicPreludeMux.compileEntry, BendLogicPreludeMux.bookBinding, family_eq]
  rfl

#assert_axioms family_eq
#assert_axioms unary_eq
#assert_axioms mux_eq
end Minidregg.Compiler.BendCheckedPrelude
