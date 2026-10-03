import Theory.BendClosureVariableSteps
import Theory.BendClosureDenotation

namespace Minidregg.Assurance.BendClosureVariableWitness
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine BendClosureSimulation
set_option autoImplicit false

def limits : Limits := ⟨⟨4,3,by decide⟩,2,2⟩
def library : Library := ⟨⟨#[.lab 0],#["ok"],#[]⟩,#[]⟩
def state : State :=
  ⟨⟨#[.nil,.closure 0 0,.environment 1 0,.vacant],3⟩,
    #[false,true,false,false],[],.lookup 0 2 .evaluateValue,0⟩

theorem head_denotes : Denotes library.program state.heap 1 (.Lab "ok") :=
  .closure rfl (.lab rfl rfl) (.nil rfl)

theorem head_ready : ReadyPointer [] library.program state.heap 1 (.Lab "ok") :=
  ⟨head_denotes, Or.inl ⟨0,0,rfl⟩⟩

/-- The generic source-preservation theorem has inhabited heap/readiness and
stack premises, and is consumed on the actual machine transition. -/
theorem actual_lookup_has_source :
    StateDenotes [] library.program (step limits library state) (.Lab "ok") ∧
      (step limits library state).sourceSteps = 0 := by
  have result := lookup_zero_source limits library state 2 1 0 (.Lab "ok") [] []
    rfl rfl head_ready (.nil rfl) .nil
  exact ⟨result.2.1,result.2.2⟩

/-- A forged source interpretation cannot turn the retained closure into a
different label. This uses general denotation uniqueness, not a second decoder. -/
theorem other_label_not_denoted : ¬ Denotes library.program state.heap 1 (.Lab "other") := by
  intro forged
  have impossible := Denotes.functional head_denotes forged
  exact (by decide : ("ok" : String) ≠ "other") (Term.Lab.inj impossible)

#assert_axioms head_denotes
#assert_axioms head_ready
#assert_axioms actual_lookup_has_source
#assert_axioms other_label_not_denoted
end Minidregg.Assurance.BendClosureVariableWitness
