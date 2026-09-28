import Host.Json

def main (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, canonicalPath, inspectionPath] =>
      let text ← IO.FS.readFile sourcePath
      let source ← IO.ofExcept (Minidregg.Host.Json.parse text)
      let bytes ← IO.ofExcept (Minidregg.Host.Json.author
        "application-spk-launch-descriptor" source)
      let inspected ← IO.ofExcept (Minidregg.Host.Json.inspect
        "application-spk-launch-descriptor" bytes)
      IO.FS.writeBinFile canonicalPath bytes.toByteArray
      IO.FS.writeFile inspectionPath inspected.pretty
      pure 0
  | _ =>
      IO.eprintln "usage: ProbeLaunch.lean SOURCE.json CANONICAL.bin INSPECTION.json"
      pure 2
