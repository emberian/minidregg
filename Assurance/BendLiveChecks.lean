/- Named adversarial checks accompany proof-carrying source execution.
These cases do not prove the closure/circuit/backend refinements. -/
import Theory.BendLiveMachine

namespace Minidregg.Assurance.BendLiveChecks
open Minidregg.Theory.BendTT
open Minidregg.Theory.BendTT.Term Minidregg.Theory.BendTT.Quan
open Minidregg.Theory.BendLiveMachine
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

def run (book : Book) (term : Term) (steps := 20) : Outcome :=
  (executeChecked book 64 steps term).outcome

theorem beta_live : run [] (App Q1 (Lam Q1 (Var 0)) (Lab "yes")) =
    .complete (Lab "yes") 1 := by decide

theorem erased_argument_never_runs :
    run [] (App Q0 (Lam Q0 (Lab "yes")) (Ref "absent")) =
      .complete (Lab "yes") 1 := by decide

/-- Source proof evidence is live even when a native compiler erases it. -/
theorem rewrite_evidence_is_live :
    run [] (Rwt (Ann Rfl (Typ Q2)) (Typ Q1) (Lab "yes")) =
      .complete (Lab "yes") 2 := by decide

/-- Source CBV evaluates unused LIVE bindings. Canonical charging may not use
an optimized C/JS instruction count as if it counted these same reductions. -/
theorem unused_live_let_still_evaluates :
    run [] (Let Q1 (Ann (Lab "unused") (Enu ["unused"])) (Lab "yes")) =
      .complete (Lab "yes") 2 := by decide

theorem copyable_function_refused :
    run [] (App Q2 (Lam Q2 (Lab "yes")) (Lam Q1 (Var 0))) =
      .refused 0 .notData := by decide

def opaqueIdentity : Def := ⟨"identity", All Q1 (Enu ["yes"]) (Enu ["yes"]),
  Lam Q1 (Var 0), true⟩

theorem opaque_model_executes :
    run [opaqueIdentity] (App Q1 (Ref "identity") (Lab "yes")) =
      .complete (Lab "yes") 1 := by decide

theorem underapplication_preserves_call :
    run [opaqueIdentity] (Ref "identity") = .complete (Ref "identity") 0 := by decide

theorem quantity_mismatch_refuses :
    run [] (App Q1 (Lam Q0 (Lab "yes")) (Lab "yes")) =
      .refused 0 .quantity := by decide

theorem zero_budget_accepts_value : run [] (Lab "yes") 0 =
    .complete (Lab "yes") 0 := by decide

theorem zero_budget_refuses_redex : run [] (Ann (Lab "yes") (Enu ["yes"])) 0 =
    .refused 0 .ticks := by decide

def constantCase : Term := Mat "left" (Lab "same")
  (Mat "right" (Lab "same") Efq)

/-- Equal permitted outputs do not authorize publishing exact trace count. -/
theorem same_output_different_private_count :
    run [] (App Q1 constantCase (Lab "left")) = .complete (Lab "same") 1 ∧
    run [] (App Q1 constantCase (Lab "right")) = .complete (Lab "same") 2 := by decide

#assert_axioms same_output_different_private_count

#assert_axioms beta_live
#assert_axioms erased_argument_never_runs
#assert_axioms rewrite_evidence_is_live
#assert_axioms unused_live_let_still_evaluates
#assert_axioms copyable_function_refused
#assert_axioms opaque_model_executes
#assert_axioms underapplication_preserves_call
#assert_axioms quantity_mismatch_refuses
#assert_axioms zero_budget_accepts_value
#assert_axioms zero_budget_refuses_redex
end Minidregg.Assurance.BendLiveChecks
