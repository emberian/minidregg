import Host.Json

open Lean

private def fail (reason : String) : IO α := throw (IO.userError reason)

def main : IO Unit := do
  let evidence := "docs/evidence/2026-09-27-spk-launch-lean-v2/"
  let sourceBytes ← IO.FS.readFile (evidence ++ "source.json")
  let source ← match Minidregg.Host.Json.parse sourceBytes with
    | .ok value => pure value
    | .error error => fail s!"strict source parse: {error}"
  let authored ← match Minidregg.Host.Json.author "application-spk-launch-descriptor" source with
    | .ok value => pure value
    | .error error => fail s!"route author: {error}"
  let retained ← IO.FS.readBinFile (evidence ++ "descriptor.bin")
  unless authored == retained.data.toList do fail "route author differs from retained canonical bytes"
  let projection ← match Minidregg.Host.Json.inspect "application-spk-launch-descriptor" authored with
    | .ok value => pure value
    | .error error => fail s!"route inspect: {error}"
  let expected ← IO.FS.readFile (evidence ++ "inspect.json")
  unless projection.compress == expected do fail "route inspect differs from retained projection"
  if (Minidregg.Host.Json.parse "{\"x\":1,\"x\":2}").isOk then
    fail "duplicate JSON key accepted"
  if (Minidregg.Host.Json.inspect "application-spk-launch-descriptor"
      (authored.drop 1)).isOk then fail "wrong-frame descriptor accepted"
  IO.println s!"PASS route author/inspect exact {authored.length} bytes; duplicate-key and wrong-frame refused"
