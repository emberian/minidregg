/- Narrow adversarial teeth for bounded native input and custody identity.
General laws live in the imported modules; these are kernel-decided regressions. -/
import Assurance.PrivateEvaluatorCustodyJoin

namespace Minidregg.Assurance.PrivateEvaluatorCustodyChecks
open Minidregg.Theory
open Minidregg.Compiler
open Minidregg.Compiler.ObliviousEvaluator
open Minidregg.Compiler.NockProgramCodec
open Minidregg.Kernel.PrivateSuccessorCustody
open Minidregg.Kernel.NockProgramCell
set_option autoImplicit false

def capacity : Capacity := ⟨2, 8, 8, 8⟩
def balance : Key := ⟨0, "balance"⟩
def absent : Key := ⟨1, "missing"⟩
def read (target : Nat) (field : String) : Option Int :=
  if target = 0 ∧ field = "balance" then some 7 else none

theorem exact_cached_absence : scan absent (gather read [balance, absent]) = none := by decide

theorem no_truncation : gatherBounded capacity read [balance, absent, balance] = none := by decide

theorem value_overflow_distinct :
    gatherBounded capacity (fun _ _ => some 256) [balance] = none := by decide

def abi : Abi where
  version := 4
  sample := [⟨0, "balance", "b", .nat, some 255⟩]
  outputs := []
  libraries := []
  fuel := 10

theorem incomplete_footprint : coversCheck [absent] abi = false := by decide

theorem complete_footprint : coversCheck [balance, absent] abi = true := by decide

/-- Actual registered evaluator term and metering, not a toy arithmetic machine. -/
theorem registered_nock_increment :
    Machine.nock.oracle 10 (.atom 42, Nock.op 4 (Nock.op 0 (.atom 1))) =
      Eval.Ran.ok (.atom 43) 2 := by decide

theorem registered_nock_exhaustion :
    Machine.nock.oracle 0 (.atom 42, Nock.op 4 (Nock.op 0 (.atom 1))) =
      Eval.Ran.exhausted 0 := by decide

def digest : TypedAuthorization.Digest := ⟨0⟩
def generation : GenerationKey := ⟨digest, [1, 2, 3], 7, 11, digest⟩
def row : CorrelationId := ⟨digest, 9⟩
def first : Journal := (reserve Journal.empty row generation .holderOutputPad).getD Journal.empty

theorem changed_attempt_does_not_refresh_pad :
    reserve first row { generation with attempt := 8, generation := 12 } .holderOutputPad = none := by decide

theorem uncertain_crash_does_not_refresh_pad :
    reserve (burn first row) row generation .holderOutputPad = none := by decide

theorem purpose_relabel_cannot_reuse_pad :
    reserve first row generation .audienceReleasePad = none := by decide

theorem late_abort_cannot_undo_commit : advance .committed .abort = none := rfl

theorem application_is_idempotent : advance .applied .apply = some .applied := rfl

#assert_axioms exact_cached_absence
#assert_axioms no_truncation
#assert_axioms value_overflow_distinct
#assert_axioms registered_nock_increment
#assert_axioms registered_nock_exhaustion
#assert_axioms changed_attempt_does_not_refresh_pad
#assert_axioms uncertain_crash_does_not_refresh_pad
#assert_axioms purpose_relabel_cannot_reuse_pad

end Minidregg.Assurance.PrivateEvaluatorCustodyChecks
