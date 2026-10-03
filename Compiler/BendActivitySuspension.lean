/- Executable persistent-yield preparation from the retained Activity record.
The exact source origin is rechecked and executed, then compared to the actual
completed heap pair. This is pure preparation, not current native authority.
Native receiving must derive the application intent from the selected Plan,
validate every target/current grant, add its exact generated control target,
and consume the predecessor before exposing a post-durability dispatch permit.
-/
import Kernel.BendActivity
import Compiler.BendActivityResponseBinding

namespace Minidregg.Compiler.BendActivitySuspension
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler.BendClosureContinuationCodec
set_option autoImplicit false

structure Prepared {source : BendActivityProgram.Source}
    (program : BendActivityProgram.Prepared source) (before : Minidregg.Kernel.BendActivity.Record)
    (sourceLimits : BendRunCore.Limits) (abi : BendClosureResponse.ABI)
    (pin : BendActivitySegment.TypePin) where
  private mk ::
  idle : before.pending = none
  contextExact : before.checkpoint.contextBytes =
    encodeContext (executionContext (BendActivityProgram.binding source) program.limits program.compiled.library)
  segment : BendActivitySegment.Checked program before.checkpoint.state.heap before.origin
  sourceRun : BendRunCore.Checked program.core segment.initial segment.outputType sourceLimits
  bound : BendActivityYieldSource.Bound sourceRun program.compiled.library.program before.checkpoint.state
  responses : BendActivityResponseBinding.Prepared bound program.limits abi pin

/-- Readiness is computed over the actual retained complete state and exact
source segment. No caller-selected post-state/result/typing flag is accepted. -/
def prepare {source : BendActivityProgram.Source}
    (program : BendActivityProgram.Prepared source) (before : Minidregg.Kernel.BendActivity.Record)
    (sourceLimits : BendRunCore.Limits) (abi : BendClosureResponse.ABI)
    (pin : BendActivitySegment.TypePin) (decodeTicks : Nat) :
    Option (Prepared program before sourceLimits abi pin) := do
  if idle : before.pending = none then
    if contextExact : before.checkpoint.contextBytes =
        encodeContext (executionContext (BendActivityProgram.binding source) program.limits program.compiled.library) then
      let segment ← BendActivitySegment.check program before.checkpoint.state.heap before.origin
        decodeTicks sourceLimits.checkerTicks
      let .ok sourceRun := BendActivitySegment.runChecked segment sourceLimits | none
      let bound ← BendActivityYieldSource.bind sourceRun program.compiled.library.program
        before.checkpoint.state decodeTicks
      let responses ← BendActivityResponseBinding.prepare bound program.limits abi pin sourceLimits.checkerTicks
      some ⟨idle,contextExact,segment,sourceRun,bound,responses⟩
    else none
  else none

/-- Source-returned effects/returns/reads remain intact for current native Plan
admission. This is not a replacement Plan with arbitrary extra writes. -/
def Prepared.plan {source : BendActivityProgram.Source}
    {program : BendActivityProgram.Prepared source} {before : Minidregg.Kernel.BendActivity.Record}
    {sourceLimits : BendRunCore.Limits} {abi : BendClosureResponse.ABI}
    {pin : BendActivitySegment.TypePin} (prepared : Prepared program before sourceLimits abi pin) :
    BendWorldPlan.Plan := prepared.bound.yielded.plan

/-- A retained separately signed application command is inert until actual
ordinary current native admission. It excludes this Activity target entirely.
The final Activity command/intent cannot be embedded in its own pending post. -/
structure PendingCandidate {source : BendActivityProgram.Source}
    {program : BendActivityProgram.Prepared source} {before : Minidregg.Kernel.BendActivity.Record}
    {sourceLimits : BendRunCore.Limits} {abi : BendClosureResponse.ABI}
    {pin : BendActivitySegment.TypePin}
    (prepared : Prepared program before sourceLimits abi pin)
    (cell : Minidregg.Kernel.DurableDataIntent.CellId)
    (identity applicationBytes : List UInt8) where
  private mk ::
  domain : Minidregg.Theory.TypedAuthorization.Digest
  semantics : Minidregg.Theory.TypedAuthorization.Digest
  signed : SignedCommand
  command : Command
  scopeExact : decodeSignedBytes applicationBytes = some (domain,semantics,signed)
  commandExact : commandCodec.decode signed.commandBytes = some command
  effectsExact : BendWorldPlan.matchesCommand prepared.plan command = true
  noControlTarget : ∀ target ∈ command.targets, target.target ≠ cell.value
  record : Minidregg.Kernel.BendActivity.Record
  retained : record.checkpoint = before.checkpoint
  ordinalExact : record.ordinal = before.ordinal + 1
  pendingExact : record.pending = some ⟨identity,applicationBytes,abi,pin⟩
  originExact : record.origin = before.origin

/-- This is the explicit retained-publication route: prepare this pending phase,
commit it under current source authority, then admit/reconcile the exact original
application operation. It does not claim atomic Activity/request co-commit.
Parsing signed bytes here is not verification of a signature or current grants. -/
def pendingCandidate {source : BendActivityProgram.Source}
    {program : BendActivityProgram.Prepared source} {before : Minidregg.Kernel.BendActivity.Record}
    {sourceLimits : BendRunCore.Limits} {abi : BendClosureResponse.ABI}
    {pin : BendActivitySegment.TypePin}
    (prepared : Prepared program before sourceLimits abi pin)
    (cell : Minidregg.Kernel.DurableDataIntent.CellId)
    (identity applicationBytes : List UInt8) :
    Option (PendingCandidate prepared cell identity applicationBytes) :=
  match scopeExact : decodeSignedBytes applicationBytes with
  | none => none
  | some (domain,semantics,signed) =>
    match commandExact : commandCodec.decode signed.commandBytes with
    | none => none
    | some command =>
      if effectsExact : BendWorldPlan.matchesCommand prepared.plan command = true then
       if disjoint : ∀ target ∈ command.targets, target.target ≠ cell.value then
         let record : Minidregg.Kernel.BendActivity.Record :=
           {before with ordinal := before.ordinal + 1, pending := some ⟨identity,applicationBytes,abi,pin⟩}
         some ⟨domain,semantics,signed,command,scopeExact,commandExact,effectsExact,disjoint,
           record,rfl,rfl,rfl,rfl⟩
       else none
      else none

#assert_axioms prepare
#assert_axioms Prepared.plan
#assert_axioms pendingCandidate
end Minidregg.Compiler.BendActivitySuspension
