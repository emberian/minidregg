/- Adversarial correspondence regressions for the real bounded machine.
These checks do not replace the pending all-program simulation theorem. -/
import Compiler.BoundedNockCircuit

namespace Minidregg.Assurance.BoundedNockChecks
open Minidregg.Theory
open Noun
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

def bounds : BoundedNockMachine.Limits := ⟨64, 32, 32, 16⟩
def quote (noun : Noun) : Noun := Nock.op 1 noun
def slot (axis : Nat) : Noun := Nock.op 0 (.atom axis)

def expected (fuel : Nat) (subject formula : Noun) : BoundedNockMachine.Result :=
  match Nock.run fuel subject formula with
  | .ok value => .value value (Nock.steps fuel subject formula)
  | .error .crash => .crash (Nock.steps fuel subject formula)
  | .error .exhausted => .exhausted fuel

abbrev agrees (subject formula : Noun) (fuel := 12) (ticks := 48) : Prop :=
  BoundedNockMachine.run bounds ticks fuel subject formula = expected fuel subject formula

theorem quote_exact : agrees (.atom 9) (quote (.cell (.atom 3) (.atom 4))) := by decide

theorem nested_slot_exact :
    agrees (.cell (.atom 3) (.cell (.atom 4) (.atom 5))) (slot 7) := by decide

theorem autocons_exact :
    agrees (.atom 0) (.cell (quote (.atom 3)) (quote (.atom 4))) := by decide

theorem eval_exact :
    agrees (.atom 0) (Nock.op 2 (.cell (quote (.atom 41)) (quote (Nock.op 4 (slot 1))))) := by decide

theorem cell_test_exact : agrees (.atom 0) (Nock.op 3 (quote (.cell (.atom 0) (.atom 0)))) := by decide

theorem increment_exact : agrees (.atom 41) (Nock.op 4 (slot 1)) := by decide

theorem equality_exact :
    agrees (.atom 0) (Nock.op 5 (.cell (quote (.cell (.atom 8) (.atom 9)))
      (quote (.cell (.atom 8) (.atom 9))))) := by decide

theorem equality_unequal_exact :
    agrees (.atom 0) (Nock.op 5 (.cell (quote (.cell (.atom 8) (.atom 9)))
      (quote (.cell (.atom 8) (.atom 10))))) := by decide

theorem conditional_exact :
    agrees (.atom 0) (Nock.op 6 (.cell (quote (.atom 1))
      (.cell (.atom 99) (quote (.atom 6))))) := by decide

theorem compose_exact :
    agrees (.atom 0) (Nock.op 7 (.cell (quote (.atom 7)) (Nock.op 4 (slot 1)))) := by decide

theorem push_subject_exact :
    agrees (.atom 12) (Nock.op 8 (.cell (quote (.atom 7)) (slot 3))) := by decide

theorem arm_exact :
    agrees (.atom 0) (Nock.op 9 (.cell (.atom 2)
      (quote (.cell (quote (.atom 33)) (.atom 0))))) := by decide

theorem edit_exact :
    agrees (.atom 0) (Nock.op 10 (.cell (.cell (.atom 7) (quote (.atom 88)))
      (quote (.cell (.atom 1) (.cell (.atom 2) (.atom 3)))))) := by decide

theorem hint_static_exact :
    agrees (.atom 0) (Nock.op 11 (.cell (.atom 123) (quote (.atom 7)))) := by decide

theorem hint_dynamic_exact :
    agrees (.atom 0) (Nock.op 11 (.cell (.cell (.atom 123) (quote (.atom 9)))
      (quote (.atom 7)))) := by decide

/-- Tree is evaluated before patch: at fuel2 a malformed tree crashes even
though the patch has a deeper evaluation. Reversing native opcode10 order
would exhaust instead and change both observable status and charge. -/
theorem edit_tree_before_patch :
    agrees (.atom 0) (Nock.op 10 (.cell (.cell (.atom 2) (Nock.op 4 (slot 1)))
      (.atom 0))) 2 := by decide

theorem dynamic_hint_clue_crash_exact :
    agrees (.atom 0) (Nock.op 11 (.cell (.cell (.atom 123) (.atom 0))
      (quote (.atom 7)))) := by decide

theorem native_exhaustion_exact : agrees (.atom 41) (Nock.op 4 (slot 1)) 1 := by decide

theorem scry_is_native_crash : agrees (.atom 41) (Nock.op 12 (.atom 0)) := by decide

theorem atom_capacity_refuses :
    BoundedNockMachine.run { bounds with atomBits := 2 } 48 12 (.atom 4) (quote (.atom 0)) =
      .overflow .atom := by decide

theorem heap_capacity_refuses :
    BoundedNockMachine.run { bounds with heapSlots := 1 } 48 12 (.atom 0) (quote (.atom 0)) =
      .overflow .heap := by decide

theorem public_ticks_do_not_claim_crash :
    BoundedNockMachine.run bounds 0 12 (.atom 0) (quote (.atom 7)) = .overflow .ticks := by decide

#assert_axioms quote_exact
#assert_axioms nested_slot_exact
#assert_axioms autocons_exact
#assert_axioms eval_exact
#assert_axioms cell_test_exact
#assert_axioms increment_exact
#assert_axioms equality_exact
#assert_axioms equality_unequal_exact
#assert_axioms conditional_exact
#assert_axioms compose_exact
#assert_axioms push_subject_exact
#assert_axioms arm_exact
#assert_axioms edit_exact
#assert_axioms hint_static_exact
#assert_axioms hint_dynamic_exact
#assert_axioms edit_tree_before_patch
#assert_axioms dynamic_hint_clue_crash_exact
#assert_axioms native_exhaustion_exact
#assert_axioms scry_is_native_crash
#assert_axioms atom_capacity_refuses
#assert_axioms heap_capacity_refuses
#assert_axioms public_ticks_do_not_claim_crash
end Minidregg.Assurance.BoundedNockChecks
