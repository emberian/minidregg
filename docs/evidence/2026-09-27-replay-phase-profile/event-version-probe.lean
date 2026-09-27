import Compiler.DurableReceiverCodec

def main : IO Unit := do
  let bytes ← IO.FS.readBinFile
    "/home/ember/build/minidregg-f461-replay-profile-v2-20260927/image.bin"
  match Minidregg.Compiler.DurableReceiverCodec.decode bytes.toList with
  | none => throw (IO.userError "retained image did not decode canonically")
  | some image =>
      let versions := image.accepted.map (fun record => record.event.codecVersion)
      IO.println s!"{versions}"
