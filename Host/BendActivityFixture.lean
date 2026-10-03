/- Native Activity fixture producer. It consumes actual source-selected pin and
current cell bytes, emits the normal native command for existing prepare/sign,
and seals that original signed command into event62. No test signature bypass. -/
import Kernel.BendActivityProposal

namespace Minidregg.Host.BendActivityFixture
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

private def book : BendTT.Book :=
  [⟨"Activity.main", .Enu ["continued"], .Lab "continued", false⟩]

private def program : BendActivityProgram.Source :=
  ⟨BendCoreAdmission.encode book, "Activity.main", 64, 8, 32, 32, 1000⟩

private def read (path : String) : IO (List UInt8) :=
  return (← IO.FS.readBinFile path).toList

private def write (path : String) (bytes : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path bytes.toByteArray

/-- The pin is exported by the actual native source configuration. Capability
and current image are supplied by the real authorized receiving fixture. -/
def execute (args : List String) : IO Unit := do
  match args with
  | ["propose", mode, pinPath, capText, preimagePath, ticksText, sourcePath, commandPath] =>
    let some pin := ContentControlFrame.pinStream.toLawful.decode (← read pinPath)
      | throw (IO.userError "invalid source-selected activity pin")
    let some cap := capText.toNat? | throw (IO.userError "invalid capability")
    let some ticks := ticksText.toNat? | throw (IO.userError "invalid ticks")
    let preimage ← read preimagePath
    let source ← if mode = "initialize" then
        pure ({program := program, initialize := true, generation := 0, ordinal := 0, ticks := 0, signedBytes := []} : BendActivityIngress.Source)
      else if mode = "advance" then do
        let some before := BendActivityControl.readRecord pin preimage
          | throw (IO.userError "no current admitted activity record")
        pure ({program := program, initialize := false, generation := before.checkpoint.generation, ordinal := before.ordinal, ticks := ticks, signedBytes := []} : BendActivityIngress.Source)
      else throw (IO.userError "expected initialize or advance")
    let some proposal := BendActivityProposal.propose pin ⟨cap⟩ source preimage
      | throw (IO.userError "actual source proposal refused")
    write sourcePath (BendActivityIngress.sourceStream.encode source)
    write commandPath (commandCodec.encode proposal.command)
    IO.println s!"ACTIVITY PROPOSAL mode={mode} ordinal={proposal.after.ordinal} sourceSteps={proposal.after.checkpoint.state.sourceSteps}"
  | ["seal", sourcePath, signedPath, outputPath] =>
    let some source := BendActivityIngress.sourceStream.toLawful.decode (← read sourcePath)
      | throw (IO.userError "invalid activity source proposal")
    let some (domain,semantics,signed) := decodeSignedBytes (← read signedPath)
      | throw (IO.userError "invalid original native signed operation")
    let some sealed := BendActivityProposal.seal source domain semantics signed
      | throw (IO.userError "signature does not bind activity action nonce")
    write outputPath (BendActivityIngress.encode sealed)
    IO.println "ACTIVITY SEALED original native signature retained"
  | _ => throw (IO.userError "usage: propose initialize|advance PIN CAP PREIMAGE TICKS SOURCE COMMAND | seal SOURCE SIGNED OUT")
end Minidregg.Host.BendActivityFixture

def main (args : List String) : IO Unit := Minidregg.Host.BendActivityFixture.execute args
