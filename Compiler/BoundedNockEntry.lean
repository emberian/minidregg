/- Native ABI/entry integration for the independent bounded Nock machine.
Uses the registered source sample and entry constructors; never calls its
reference oracle. This is a clear executable path pending controller/MPC and
all-program machine simulation proofs, not a private execution certificate. -/
import Compiler.ObliviousEvaluator
import Theory.BoundedNockMachine

namespace Minidregg.Compiler.BoundedNockEntry
open Minidregg.Theory
open Minidregg.Compiler.NockProgramCodec
open Minidregg.Kernel.NockProgramCell
open ObliviousEvaluator
set_option autoImplicit false

inductive Result
  | workingSetOverflow
  | sampleRefused
  | evaluated (result : BoundedNockMachine.Result)
  deriving DecidableEq, Repr

/-- The same native subject/formula entry as Machine.nock, evaluated by the
new continuation machine. Capacity/tick overflow remains a separate result. -/
def run (limits : BoundedNockMachine.Limits) (ticks fuel : Nat)
    (params : Machine.nock.Params) (code : Machine.nock.Code)
    (libs : List Machine.nock.Code) (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) : Result :=
  match Machine.nock.sampleOf abi ctx targets read with
  | none => .sampleRefused
  | some sample =>
      let term := Machine.nock.entry params code libs sample
      .evaluated (BoundedNockMachine.run limits ticks fuel term.1 term.2)

def runGathered (working : Capacity) (keys : List Key)
    (limits : BoundedNockMachine.Limits) (ticks fuel : Nat)
    (params : Machine.nock.Params) (code : Machine.nock.Code)
    (libs : List Machine.nock.Code) (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) : Result :=
  if coversCheck keys abi then
    match gatherBounded working read keys with
    | none => .workingSetOverflow
    | some rows => run limits ticks fuel params code libs abi ctx targets
        (fun target field => scan ⟨target, field⟩ rows)
  else .workingSetOverflow

/-- Completeness here is solely the finite input boundary: the bounded machine
receives exactly the native term. It is not an all-opcode simulation theorem. -/
theorem gathered_entry_exact (working : Capacity) (keys : List Key)
    (limits : BoundedNockMachine.Limits) (ticks fuel : Nat)
    (params : Machine.nock.Params) (code : Machine.nock.Code)
    (libs : List Machine.nock.Code) (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int)
    (covered : Covers keys abi) (count : keys.length ≤ working.rows)
    (width : (gather read keys).all (entryFits working) = true) :
    runGathered working keys limits ticks fuel params code libs abi ctx targets read =
      run limits ticks fuel params code libs abi ctx targets read := by
  have check := (coversCheck_iff keys abi).2 covered
  simp only [runGathered, check, ↓reduceIte,
    gatherBounded_complete working read keys count width, run]
  rw [gathered_sample_exact Machine.nock read keys abi ctx targets covered]

/-- Member-authored OO supplies the real WorldMethodTrace/nativeRead projection
at this seam. This function itself grants no source authority or custody. -/
def runWorld (working : Capacity) (keys : List Key)
    (limits : BoundedNockMachine.Limits) (ticks fuel : Nat)
    (params : Machine.nock.Params) (code : Machine.nock.Code)
    (libs : List Machine.nock.Code) (abi : Abi) (ctx : Context) (targets : List Nat)
    (world : List Entry) : Result :=
  runGathered working keys limits ticks fuel params code libs abi ctx targets
    (fun target field => scan ⟨target, field⟩ world)

#assert_axioms gathered_entry_exact
end Minidregg.Compiler.BoundedNockEntry
