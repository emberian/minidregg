/-
# Kernel.Contracts.IntentVectors — the emitter of the SDK's golden intent vectors

    lean --run Kernel/Contracts/IntentVectors.lean native/mini-sdk/golden/intents.json \
      > native/mini-sdk/golden/lean-intents.json

Reads the hand-written input rows (`[{"name", "text"}]`: `text` is the intent in the SDK's JSON
spelling, as a string, so the exact SOURCE TEXT reaches the codec: `100.0` and `1e2` are not
re-printed on the way in) and runs EACH ROW THROUGH THE EXPORTED ENTRY POINTS (`minidregg_intent_encode`,
`minidregg_intent_id_preimage`: `Intents.intentEncodeBytes` / `intentIdPreimageBytes`), so the
vectors are the bytes a native caller of the export would get. A row prints either
`{"name", "text" (echo), "result": "ok", "bytes", "idPreimage"}` or
`{"name", "text", "result": "refused", "reason"}`. The SDK's Rust and TS suites require their
encoder to match every `ok` row byte for byte and to refuse every `refused` row, and require
the echoed `text` to equal its input byte for byte (a stale vector file fails).
-/
import Kernel.Contracts.Intents

namespace Minidregg.Kernel.Contracts.IntentVectors

open Lean (Json)
open Minidregg.Kernel.Contracts.Intents

/-- A status-tagged reply → the bytes or the refusal. -/
def untag (reply : ByteArray) : Except String (List UInt8) :=
  match reply.toList with
  | 1 :: bytes => .ok bytes
  | 0 :: msg => .error ((String.fromUTF8? ⟨msg.toArray⟩).getD "<non-UTF-8 refusal>")
  | _ => .error "malformed reply"

def row (r : Json) : Except String Json := do
  let name ← (← r.getObjVal? "name").getStr?
  let text ← (← r.getObjVal? "text").getStr?
  let spelling := text.toUTF8
  let echo := Json.mkObj [("name", name), ("text", text)]
  match untag (intentEncodeBytes spelling), untag (intentIdPreimageBytes spelling) with
  | .ok bytes, .ok pre =>
      pure (echo.setObjVal! "result" "ok" |>.setObjVal! "bytes" (hexOf bytes) |>.setObjVal! "idPreimage" (hexOf pre))
  | .error e, .error _ => pure (echo.setObjVal! "result" "refused" |>.setObjVal! "reason" e)
  | _, _ => throw s!"{name}: the two exports disagree about whether the intent is admitted"

end Minidregg.Kernel.Contracts.IntentVectors

open Lean (Json)
open Minidregg.Kernel.Contracts.IntentVectors

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: IntentVectors INPUTS.json"; return 2
  let rows ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let out ← IO.ofExcept ((← IO.ofExcept rows.getArr?).toList.mapM row)
  IO.println (Json.pretty (Json.mkObj [
    ("generator", "Kernel/Contracts/IntentVectors.lean"),
    ("lean", Lean.versionString),
    ("frame", "DREGG/CONTRACT/INTENT/v1"),
    ("idFrame", "DREGG/CONTRACT/INTENT-ID/v1"),
    ("vectors", Json.arr out.toArray)]))
  return 0
