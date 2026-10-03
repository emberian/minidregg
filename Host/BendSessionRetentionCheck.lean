/- Local recovery capacity regression: no native authority or receipt fixture. -/
import Host.BendSessionDriverJson

open Minidregg.Host.BendSessionDriverJson

def main (args : List String) : IO UInt32 := do
  let [directory] := args | throw (IO.userError "expected fresh private capacity directory")
  let root : System.FilePath := directory
  if ← root.pathExists then throw (IO.userError "capacity directory already exists")
  IO.FS.createDir root
  let path := (root / "original-attempt.bin").toString
  let bytes : List UInt8 := List.replicate 2100000 7
  writeRetained path bytes
  unless (← readRetained path) == bytes do
    throw (IO.userError "exact larger retained attempt changed")
  let ingressRefused ← try
      let _ ← read path
      pure false
    catch _ => pure true
  unless ingressRefused do throw (IO.userError "public ingress cap accidentally grew")
  let output := (root / "oversized.bin").toString
  let oversizedRefused ← try
      writeRetained output (List.replicate (retainedCapacity + 1) 0)
      pure false
    catch _ => pure true
  unless oversizedRefused do throw (IO.userError "unbounded retained write admitted")
  if ← (System.FilePath.mk output).pathExists then
    throw (IO.userError "oversized retained write emitted bytes")
  if ← (System.FilePath.mk (output ++ ".pending")).pathExists then
    throw (IO.userError "oversized retained write emitted pending bytes")
  IO.println "BEND SESSION RETENTION PASS: exact 2.1MB retained; 2MB public ingress refused; oversized recovery refused before writes"
  pure 0
