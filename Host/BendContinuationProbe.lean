/- Two-process checkpoint/restart consumer of the actual controller codec.
This is local restart conformance, not an admitted world effect or fsync proof.
The program author supplies no per-application journal or restoration routine.
-/
import Compiler.BendClosureContinuationCodec
import Theory.BendClosureDecode

namespace Minidregg.Host.BendContinuationProbe
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler.BendClosureContinuationCodec
set_option autoImplicit false

private def bounds : Limits :=
  {heap := {slots := 32, wordBits := 8, fits := by decide}, frames := 16, arguments := 16}

private def library : Library :=
  {program := {code := #[.lab 0, .var 0, .lam .Q1 1, .app .Q1 2 0],
    names := #["continued"], enumerations := #[]}, definitions := #[]}

private def context : List UInt8 :=
  encodeContext (executionContext "continuation-probe/source-v1/activity-0".toUTF8.toList
    bounds library)

private def initial : IO State :=
  match start bounds library 3 with
  | .ok state => pure state
  | .error failure => throw (IO.userError (reprStr failure))

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Save and resume run as separate OS processes in the narrow harness. -/
def execute (args : List String) : IO Unit := do
  match args with
  | ["save", file, cutText] =>
    let some cut := cutText.toNat? | throw (IO.userError "invalid cut")
    check (cut ≤ 24) "cut exceeds fixture budget"
    let paused := run bounds library cut (← initial)
    let bytes := encode ⟨context, 0, paused⟩
    IO.FS.writeBinFile file bytes.toByteArray
    IO.println s!"CONTINUATION SAVED cut={cut} bytes={bytes.length} control={reprStr paused.control}"
  | ["resume", file, cutText] =>
    let some cut := cutText.toNat? | throw (IO.userError "invalid cut")
    check (cut ≤ 24) "cut exceeds fixture budget"
    let bytes := (← IO.FS.readBinFile file).toList
    let some restored := restore 1048576 context 0 bytes |
      throw (IO.userError "checkpoint refused")
    let starting ← initial
    check (restored == run bounds library cut starting) "restore changed actual machine state"
    let resumed := run bounds library (24 - cut) restored
    check (resumed == run bounds library 24 starting) "split execution differs"
    let .complete pointer := resumed.control | throw (IO.userError "did not complete")
    let some result := BendClosureArena.decode library.program resumed.heap 64 pointer |
      throw (IO.userError "cannot reify result")
    check (result.term == .Lab "continued") "wrong source result"
    check (resumed.sourceSteps == 1) "wrong source count"
    check ((restore 1048576 (context ++ [0]) 0 bytes).isNone) "foreign context accepted"
    check ((restore 1048576 context 1 bytes).isNone) "stale generation accepted"
    check ((restore 1048576 context 0 (bytes ++ [0])).isNone) "trailing bytes accepted"
    check ((restore 0 context 0 bytes).isNone) "byte capacity ignored"
    IO.println s!"CONTINUATION PASS cut={cut} exact-state/exact-result/context/generation/canonical/capacity"
  | _ => throw (IO.userError "usage: save|resume PATH CUT")
end Minidregg.Host.BendContinuationProbe

def main (args : List String) : IO Unit :=
  Minidregg.Host.BendContinuationProbe.execute args
