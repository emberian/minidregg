import Host.Json

def main : IO Unit := do
  let sample := "{\"issueIndex\":\"22\",\"ticketResource\":\"8500\",\"packageManifest\":\"8402\",\"role\":{\"basis\":{\"type\":\"none\"},\"added\":[],\"removed\":[],\"roleSchemaRoot\":\"123\",\"roleVersion\":\"1\"},\"descriptorCapability\":\"149\",\"sessionObserveCapability\":\"148\",\"descriptorObserveCapability\":\"150\",\"manifestObserveCapability\":\"143\",\"nonce\":\"1\"}"
  let .ok json := Lean.Json.parse sample | throw (IO.userError "sample JSON parse failed")
  let .ok bytes := Minidregg.Host.Json.author "application-session-enrollment-request" json
    | throw (IO.userError "source author refused valid request")
  let .ok inspected := Minidregg.Host.Json.inspect "application-session-enrollment-request" bytes
    | throw (IO.userError "source inspector refused authored bytes")
  unless inspected.compress.contains "application-session-enrollment-request-v1" do
    throw (IO.userError "wrong source inspection type")
  let malformed := (sample.dropEnd 1).toString ++ ",\"extra\":\"1\"}"
  let .ok malformedJson := Lean.Json.parse malformed
    | throw (IO.userError "malformed probe JSON parse failed")
  match Minidregg.Host.Json.author "application-session-enrollment-request" malformedJson with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unknown request field was accepted")
  IO.println s!"PASS request bytes={bytes.length}, strict unknown field refused"
