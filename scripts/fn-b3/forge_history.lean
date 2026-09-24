/- Scratch-only negative tooth for native historical admission. The changed
ingress remains physically restorable, but cannot be source-admitted. -/
import Host.Main

open Minidregg.Host
open Minidregg.Kernel
open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec

def forgeHistory : IO Unit := do
  let some configPath ← IO.getEnv "MINI_B3_FORGE_CONFIG"
    | throw (IO.userError "MINI_B3_FORGE_CONFIG must select the existing pinned config")
  let some outputPath ← IO.getEnv "MINI_B3_FORGE_OUTPUT"
    | throw (IO.userError "MINI_B3_FORGE_OUTPUT must select a fresh scratch output")
  let settings ← loadSettings configPath
  let config := settings.config
  let durable ← IO.ofExcept (← DurableReceiverIO.load config.storage.transport ResourceBirthCodec.rootBytes)
  let first :: rest := durable.image.accepted
    | throw (IO.userError "expected accepted history")
  let forged := { durable.image with accepted :=
    { first with event := { first.event with canonicalBytes := [255] } } :: rest }
  unless forged.restore ResourceBirthCodec.rootBytes |>.isSome do
    throw (IO.userError "forged image is not physically replayable")
  IO.FS.writeBinFile outputPath (DurableReceiverCodec.encode forged).toByteArray
  IO.println s!"forged physically replayable history with {forged.accepted.length} accepted entries"

#eval forgeHistory
