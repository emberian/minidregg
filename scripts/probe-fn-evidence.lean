/- Produce canonical negative P0 packages for the public CLI regression. -/
import Compiler.FnEvidenceCodec

open Minidregg.Compiler.FnEvidenceCodec

def flipLast (bytes : List UInt8) : List UInt8 :=
  match bytes.reverse with
  | [] => []
  | byte :: rest => (UInt8.ofNat (byte.toNat + 1) :: rest).reverse

def writePackage (directory name : String) (package : Package) : IO Unit := do
  let bytes ← IO.ofExcept (encodeChecked package)
  IO.FS.writeBinFile (directory ++ "/" ++ name ++ ".bin") bytes.toByteArray

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [source, directory] =>
      let package ← IO.ofExcept (decodeChecked (← IO.FS.readBinFile source).toList)
      writePackage directory "changed-call" { package with signedCall := flipLast package.signedCall }
      writePackage directory "changed-receipt" { package with originalReceipt :=
        { package.originalReceipt with eventId := ⟨package.originalReceipt.eventId.value + 1⟩ } }
      writePackage directory "changed-prefix" { package with acceptedPrefix := flipLast package.acceptedPrefix }
      writePackage directory "changed-profile" { package with semantics := ⟨package.semantics.value + 1⟩ }
      writePackage directory "changed-genesis" { package with genesisPin := ⟨package.genesisPin.value + 1⟩ }
      return 0
  | _ =>
      (← IO.getStderr).putStrLn "usage: lean --run scripts/probe-fn-evidence.lean PACKAGE.bin DIRECTORY"
      return 2
