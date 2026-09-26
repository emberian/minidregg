import Host.Json

open Minidregg.Host
open Minidregg.Compiler.NativeObservationCodec
open Minidregg.Kernel

def main : IO Unit := do
  let source := String.join [
    "{\"grain\":{\"task\":\"1\",\"subject\":\"2\",\"capability\":\"3\",",
    "\"expectedAuthorityRoot\":\"4\",\"schemaVersion\":\"1\",\"expectedTargetRoot\":\"5\",",
    "\"context\":{\"operationId\":\"6\",\"payload\":\"observed\"},",
    "\"before\":{\"generation\":\"0\",\"status\":\"0\",\"remaining\":\"10\",\"reserved\":\"0\"},",
    "\"operation\":{\"type\":\"input\"},",
    "\"publications\":[{\"kind\":\"object\",\"target\":\"7\",\"capability\":\"8\",",
    "\"observeCapability\":null,\"schemaVersion\":\"1\",\"expectedTargetRoot\":\"9\",",
    "\"payload\":{\"type\":\"scalar\",\"actions\":[]}}]},",
    "\"grants\":[{\"kind\":\"object\",\"target\":\"1\",\"capability\":\"3\"},",
    "{\"kind\":\"object\",\"target\":\"7\",\"capability\":\"8\"}],",
    "\"intentNonce\":\"10\"}"]
  let json ← IO.ofExcept (Json.parse source)
  let bytes ← IO.ofExcept (Json.author "grain-intent" json)
  let some intent := intentCodec.decode bytes
    | throw (IO.userError "grain intent codec failed")
  unless intent.subject.value == 2 && intent.nonce == 10 && intent.grants.length == 2 do
    throw (IO.userError "grain intent lost source selection")
  let .prepare (.invoke commandBytes) := intent.purpose
    | throw (IO.userError "grain intent did not prepare an invocation")
  let some command := DeclaredResourceController.commandCodec.decode commandBytes
    | throw (IO.userError "grain command codec failed")
  let some publication := command.targets[1]?
    | throw (IO.userError "grain publication missing")
  unless command.targets.length == 2 && publication.target == 7 do
    throw (IO.userError "grain publication was not atomic in command")
  IO.println "PASS source-authored grain intent with publication"
