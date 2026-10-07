/- Private input lowering joined to the same native world method semantics.
This module does not define another object evaluator. It retains typed effects
and non-ABI authority dependencies in WorldMethodTrace; the finite memory scan
supplies the actual registered evaluator's sample with exact native outcomes.
Secret-PC evaluation and malicious MPC remain separate backend refinements. -/
import Compiler.ObliviousEvaluator
import Kernel.WorldMethodTrace

namespace Minidregg.Compiler.PrivateWorldIR

open Minidregg.Theory
open Minidregg.Theory.Eval
open Minidregg.Compiler.NockProgramCodec
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler.ObliviousEvaluator

set_option autoImplicit false

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {ground : Ground deployment} {command : Command}

/-- The physical/native snapshot supplies every preimage, target ID, absent
slot, funding exclusion and context. A client-provided sample is never used. -/
def nativeRead (prepared : PreparedInvocation deployment profile ambient ground command) :
    Nat → String → Option Int :=
  programSampleRead command (fun i => (prepared.targets i).pre.logical)
    (computeFundingIndex prepared.compute)

def lower (M : Machine) (prepared : PreparedInvocation deployment profile ambient ground command)
    (working : Capacity) (keys : List Key) (fuel : Nat) (params : M.Params)
    (code : M.Code) (libraries : List M.Code) (abi : Abi) (world : List Entry) :
    Result M.Output :=
  runWorld M working keys fuel params code libraries abi (runContext ambient command)
    (programTargets command (computeFundingIndex prepared.compute)) world

/-- Complete finite native projection + bounds entails the exact registered
oracle result, including sample refusal, native crash/exhaustion, output and
metered count. Overflow never substitutes a partial result. -/
theorem lower_native_exact (M : Machine)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (worldCapacity working : Capacity) (keys : List Key) (fuel : Nat)
    (params : M.Params) (code : M.Code) (libraries : List M.Code) (abi : Abi)
    (world : WorldProjection worldCapacity abi (nativeRead prepared))
    (covered : Covers keys abi) (count : keys.length ≤ working.rows)
    (width : (gather (fun target field => scan ⟨target, field⟩ world.rows) keys).all
      (entryFits working) = true) :
    lower M prepared working keys fuel params code libraries abi world.rows =
      nativeRun M fuel params code libraries abi (runContext ambient command)
        (programTargets command (computeFundingIndex prepared.compute)) (nativeRead prepared) :=
  runWorld_native_exact M worldCapacity working keys fuel params code libraries abi
    (runContext ambient command) (programTargets command (computeFundingIndex prepared.compute))
    (nativeRead prepared) world covered count width

/-- Admission produces the source-owned typed effects and complete dependency
trace consumed by agreement/custody. Input lowering never invents an effect,
releases private data, or manufactures a second charge. -/
def retained (prepared : PreparedInvocation deployment profile ambient ground command)
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed) :
    WorldMethodTrace.Trace := WorldMethodTrace.ofAccepted prepared accepted

#assert_axioms lower_native_exact

end Minidregg.Compiler.PrivateWorldIR
