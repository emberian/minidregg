/- Reusable public Bend mux program with three varying private Boolean tags.
The compiled expression and relation use the existing Air/flatten/Emit fold;
source evaluation uses the same exact BendTT kernel and shared Trace.
This is a pure block, not object dispatch, world effects or encrypted admission. -/
import Compiler.BendLogicTrace

namespace Minidregg.Compiler.BendLogicMux

open BendLogicSpecialization
open Minidregg.Theory.BendLiveMachine
set_option autoImplicit false

/-- Ordered ABI: output0, selector1, true arm2, false arm3. -/
def assignment {F : Type} [Field F] (selector onTrue onFalse output : Bool) : Fin 4 → F :=
  fun i => BendLogicCase.bit <| if i.val = 0 then output else
    if i.val = 1 then selector else if i.val = 2 then onTrue else onFalse

def result (selector onTrue onFalse : Bool) : Bool :=
  if selector then onTrue else onFalse

/-- Constructive mux: y + b*(x-y). This computes without a supplied output. -/
def outputExpr {F : Type} [Field F] : Term (AirSig F (Fin 4)) :=
  add' (vr 3) (mul' (vr 1) (add' (vr 2) (mul' (cst (-1)) (vr 3))))

def constraints {F : Type} [Field F] : ConstraintSystem F (Fin 4) :=
  [boolGadget 0, boolGadget 1, boolGadget 2, boolGadget 3,
    add' (vr 0) (mul' (cst (-1)) outputExpr)]

def descriptor {F : Type} [Field F] (nPublic : Nat) : ConstraintDescriptor F :=
  emit Fin.val nPublic 4 constraints

theorem outputExpr_correct {F : Type} [Field F]
    (selector onTrue onFalse output : Bool) :
    eval (assignment (F := F) selector onTrue onFalse output) outputExpr =
      BendLogicCase.bit (result selector onTrue onFalse) := by
  rw [← eval_agrees_exec]
  change BendLogicCase.bit (F := F) onFalse +
    BendLogicCase.bit selector * (BendLogicCase.bit onTrue + (-1) * BendLogicCase.bit onFalse) = _
  cases selector <;> cases onTrue <;> cases onFalse <;>
    simp [BendLogicCase.bit, result]

theorem constraints_correct {F : Type} [Field F]
    (selector onTrue onFalse output : Bool) :
    systemAccepts (assignment (F := F) selector onTrue onFalse output) constraints ↔
      output = result selector onTrue onFalse := by
  simp only [systemAccepts, constraints, List.forall_mem_cons]
  simp only [List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [boolGadget_correct]
  simp only [accepts_iff_semHolds, semHolds]
  change ((assignment (F := F) selector onTrue onFalse output 0 = 0 ∨
      assignment (F := F) selector onTrue onFalse output 0 = 1) ∧
    (assignment (F := F) selector onTrue onFalse output 1 = 0 ∨
      assignment (F := F) selector onTrue onFalse output 1 = 1) ∧
    (assignment (F := F) selector onTrue onFalse output 2 = 0 ∨
      assignment (F := F) selector onTrue onFalse output 2 = 1) ∧
    (assignment (F := F) selector onTrue onFalse output 3 = 0 ∨
      assignment (F := F) selector onTrue onFalse output 3 = 1) ∧
    assignment (F := F) selector onTrue onFalse output 0 + (-1) *
      evalExec (assignment (F := F) selector onTrue onFalse output) outputExpr = 0) ↔ _
  rw [eval_agrees_exec, outputExpr_correct]
  cases selector <;> cases onTrue <;> cases onFalse <;> cases output <;>
    simp [assignment, BendLogicCase.bit, result]

/-- Soundness/completeness quantify arbitrary satisfying auxiliary vectors. -/
theorem descriptor_correct {F : Type} [Field F] (nPublic : Nat)
    (selector onTrue onFalse output : Bool) :
    (∃ wv : Nat → F,
      (∀ i : Fin 4, wv i.val = assignment selector onTrue onFalse output i) ∧
      descriptorHolds (descriptor nPublic) wv) ↔
      output = result selector onTrue onFalse := by
  rw [descriptor, emit_accepts_iff_fin, constraints_correct]

/-- Selector, true arm, false arm are affine source binders in that order.
At the body: Var2=selector, Var1=true arm, Var0=false arm. -/
def sourceTerm : BTerm :=
  .Lam .Q1 (.Lam .Q1 (.Lam .Q1
    (.App .Q1 (.Mat "false" (.Var 0) (.Mat "true" (.Var 1) .Efq)) (.Var 2))))

def inputTerm (selector onTrue onFalse : Bool) : BTerm :=
  .App .Q1 (.App .Q1 (.App .Q1 sourceTerm (label selector))
    (label onTrue)) (label onFalse)

def sourceType : BTerm :=
  .All .Q1 booleanType (.All .Q1 booleanType (.All .Q1 booleanType booleanType))

theorem source_closed : Minidregg.Theory.BendTT.Term.Closed sourceTerm := by
  intro substitution
  rfl

theorem source_live (book : BBook) :
    Minidregg.Theory.BendTT.Term.Live book sourceTerm := by rfl

theorem source_typed (book : BBook) :
    Minidregg.Theory.BendTT.Typed book [] sourceTerm sourceType := by
  apply Minidregg.Theory.BendTT.Typed.lam rfl (by intro h; cases h)
  apply Minidregg.Theory.BendTT.Typed.lam rfl (by intro h; cases h)
  apply Minidregg.Theory.BendTT.Typed.lam rfl (by intro h; cases h)
  apply Minidregg.Theory.BendTT.Typed.app (A := booleanType) (B := booleanType)
  · apply Minidregg.Theory.BendTT.Typed.mat rfl (by simp [booleanType])
    · exact Minidregg.Theory.BendTT.Typed.var (Γ := [booleanType, booleanType, booleanType]) (i := 0) (A := booleanType) rfl
    · apply Minidregg.Theory.BendTT.Typed.mat rfl (by simp [booleanType])
      · exact Minidregg.Theory.BendTT.Typed.var (Γ := [booleanType, booleanType, booleanType]) (i := 1) (A := booleanType) rfl
      · exact Minidregg.Theory.BendTT.Typed.efq rfl
  · exact Minidregg.Theory.BendTT.Typed.var (Γ := [booleanType, booleanType, booleanType]) (i := 2) (A := booleanType) rfl

/-- Three beta steps plus the exact shared hit/miss source trace. -/
theorem source_trace (book : BBook) (selector onTrue onFalse : Bool) :
    Trace book (BendLogicTrace.sourceCount selector + 3)
      (inputTerm selector onTrue onFalse) (label (result selector onTrue onFalse)) := by
  have tail := BendLogicTrace.source_trace book (⟨onFalse, onTrue⟩ : BendLogicCase.Plan) selector
  cases selector <;> cases onTrue <;> cases onFalse <;>
    exact .step (.app_f (.app_f (.beta rfl (fun _ => .lab) (by intro h; cases h))))
      (.step (.app_f (.beta rfl (fun _ => .lab) (by intro h; cases h)))
        (.step (.beta rfl (fun _ => .lab) (by intro h; cases h))
          tail))

/-- Only the complete public source and valid public prefix acquire this block. -/
def compile {F : Type} [Field F] (nPublic : Nat) (source : BTerm) :
    Option (ConstraintDescriptor F) :=
  if nPublic ≤ 4 ∧ source = sourceTerm then some (descriptor nPublic) else none

theorem compile_exact {F : Type} [Field F] {nPublic : Nat} {source : BTerm}
    {d : ConstraintDescriptor F} (accepted : compile nPublic source = some d) :
    nPublic ≤ 4 ∧ source = sourceTerm ∧ d = descriptor nPublic := by
  unfold compile at accepted
  split at accepted
  · rename_i h
    exact ⟨h.1, h.2, (Option.some.inj accepted).symm⟩
  · contradiction

theorem compiled_descriptor_trace_sound {F : Type} [Field F] (book : BBook)
    {nPublic : Nat} {source : BTerm} {d : ConstraintDescriptor F}
    (accepted : compile nPublic source = some d)
    (selector onTrue onFalse output : Bool) (wv : Nat → F)
    (pinned : ∀ i : Fin 4, wv i.val = assignment selector onTrue onFalse output i)
    (holds : descriptorHolds d wv) :
    Trace book (BendLogicTrace.sourceCount selector + 3)
      (.App .Q1 (.App .Q1 (.App .Q1 source (label selector))
        (label onTrue)) (label onFalse)) (label output) := by
  obtain ⟨_, hs, hd⟩ := compile_exact accepted
  rw [hs]
  have correct : output = result selector onTrue onFalse :=
    (descriptor_correct nPublic selector onTrue onFalse output).mp ⟨wv, pinned, hd ▸ holds⟩
  rw [correct]
  exact source_trace book selector onTrue onFalse

#assert_axioms outputExpr_correct
#assert_axioms constraints_correct
#assert_axioms descriptor_correct
#assert_axioms source_closed
#assert_axioms source_live
#assert_axioms source_typed
#assert_axioms source_trace
#assert_axioms compile_exact
#assert_axioms compiled_descriptor_trace_sound

end Minidregg.Compiler.BendLogicMux
