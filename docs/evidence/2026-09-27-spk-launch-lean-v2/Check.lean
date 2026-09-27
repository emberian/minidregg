import Host.ApplicationSpkLaunchDescriptorAuthoring

open Lean
open Minidregg.Host.ApplicationSpkLaunchDescriptorAuthoring

private def fail (reason : String) : IO α := throw (IO.userError reason)

def main : IO Unit := do
  let sourceBytes ← IO.FS.readFile "launch-source.json"
  let source ← match Json.parse sourceBytes with
    | .ok value => pure value
    | .error error => fail s!"source JSON parse: {error}"
  let (bytes, root) ← match author source with
    | .ok value => pure value
    | .error error => fail s!"author: {error}"
  let projection ← match inspect bytes with
    | .ok value => pure value
    | .error error => fail s!"inspect: {error}"
  let rootText ← match projection.getObjValAs? String "root" with
    | .ok value => pure value
    | .error error => fail s!"inspect root: {error}"
  unless rootText == toString root.value do fail "root mismatch"
  let kind ← match projection.getObjValAs? String "type" with
    | .ok value => pure value
    | .error error => fail s!"inspect type: {error}"
  unless kind == "application-spk-launch-descriptor-v2" do fail "type mismatch"
  if (author (Json.mkObj [])).isOk then fail "empty source accepted"
  if (inspect (bytes.take (bytes.length - 1))).isOk then fail "truncated descriptor accepted"
  IO.FS.writeFile "launch-inspect.json" projection.compress
  IO.FS.writeBinFile "launch-descriptor.bin" (ByteArray.mk bytes.toArray)
  IO.println s!"PASS root={root.value} bytes={bytes.length} type={kind} empty/truncated rejected"
