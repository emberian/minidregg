/- Native fixture/operator authoring consumer. Input files are actual source
and current control data. Output is an unsigned native content proposal plus its
source action; signing, current admission, CAS and readback remain native work.
-/
import Compiler.BendActivityAuthor

namespace Minidregg.Host.BendActivityAuthor
open Minidregg.Compiler
open Minidregg.Kernel
set_option autoImplicit false

private def readBytes (path : String) : IO (List UInt8) := do
  return (← IO.FS.readBinFile path).toList

private def writeBytes (path : String) (bytes : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path bytes.toByteArray

def execute (args : List String) : IO Unit := do
  match args with
  | [mode,programPath,pinPath,currentPath,output,generationText,ticksText] =>
    unless mode == "initialize" || mode == "advance" do
      throw (IO.userError "mode must be initialize or advance")
    let some generation := generationText.toNat? | throw (IO.userError "bad generation")
    let some ticks := ticksText.toNat? | throw (IO.userError "bad ticks")
    let programBytes ← readBytes programPath
    let pinBytes ← readBytes pinPath
    let currentBytes ← readBytes currentPath
    let some program := BendActivityProgram.sourceStream.toLawful.decode programBytes
      | throw (IO.userError "source program malformed")
    unless BendActivityProgram.sourceStream.encode program = programBytes do
      throw (IO.userError "source program noncanonical")
    let some pin := ContentControlFrame.pinStream.toLawful.decode pinBytes
      | throw (IO.userError "source pin malformed")
    unless ContentControlFrame.pinStream.encode pin = pinBytes do
      throw (IO.userError "source pin noncanonical")
    let some proposal := Minidregg.Compiler.BendActivityAuthor.prepare program pin currentBytes
        (mode == "initialize") generation ticks
      | throw (IO.userError "actual source/current phase preparation refused")
    writeBytes (output ++ ".activity") (BendActivity.encode proposal.record)
    writeBytes (output ++ ".content") (ContentResource.commandCodec.encode proposal.content)
    writeBytes (output ++ ".source") (BendActivityIngress.encode proposal.action)
    IO.FS.writeFile (output ++ ".nonce") (toString proposal.nonce ++ "\n")
    IO.println s!"ACTIVITY PROPOSAL mode={mode} nonce={proposal.nonce} ordinal={proposal.record.ordinal} sourceSteps={proposal.record.checkpoint.state.sourceSteps}"
  | _ => throw (IO.userError "usage: initialize|advance PROGRAM_SOURCE PIN CURRENT_CONTROL OUTPUT_PREFIX GENERATION TICKS")
end Minidregg.Host.BendActivityAuthor

def main (args : List String) : IO Unit := Minidregg.Host.BendActivityAuthor.execute args
