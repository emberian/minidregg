import Host.Main

open Lean

set_option autoImplicit false

def probeFnPinJson : IO Unit := do
  let json ← IO.ofExcept <| Minidregg.Host.Json.parse
    "{\"fnBinary\":\"/logical/fn\",\"mlPublicKey\":\"/logical/ml.pem\",\"principal\":\"aa\",\"edPublicKey\":\"bb\",\"mlPublicKeyHex\":\"cc\"}"
  let parsed : Minidregg.Host.FnPortablePin ← IO.ofExcept (fromJson? json)
  unless parsed.fnExecution.isNone && parsed.mlPublicKeyExecution.isNone &&
      parsed.executable == "/logical/fn" &&
      parsed.publicKeyFile == "/logical/ml.pem" do
    throw (IO.userError "external fn pin lost logical pathname semantics")
  let pinned := parsed.withExecution "/private/fn" "/private/ml.pem"
  unless pinned.fnBinary == "/logical/fn" && pinned.executable == "/private/fn" &&
      pinned.mlPublicKey == "/logical/ml.pem" &&
      pinned.publicKeyFile == "/private/ml.pem" do
    throw (IO.userError "private fn execution overwrote durable logical pin")
  IO.println "PASS external fn pin JSON preserves logical path; private execution is separate"

#eval probeFnPinJson
