/- Objective Bend reference example: LazySharedField.

Laziness and sharing. result = fix(Fields, ...).twice with costly = work(8n) = 256 and twice = costly + costly = 512. Call-by-need evaluates the one costly thunk once and the second selection reads the cache; the second theorem pins that count on the checked packet.

Source:   tests/objective-bend-source/ (see the `LazySharedField` row of preview-cohort.json)
Packet:   LazySharedField.typed.json, the typed core packet the current front end produces
          for that row (parser, capture, elaborator, annotation proposal).
          scripts/check-objective-examples.sh fails when it is stale;
          `scripts/check-objective-examples.sh --refresh` rewrites it.
Run:      lake env lean examples/objective-bend-world/reference/LazySharedField.lean

`observation` is the generic typed preview (`Host.ObjectiveBendPreview.preview`):
decode the packet, run `check` (typing and ownership), then `runBounded` on the same
decoded term. The theorem pins the checked type, the observed result and the empty
use set; it rests on the compiled evaluator (`native_decide`), which
`#assert_compiled` re-runs and names. `main` prints the same summary and exits 1
on a mismatch. -/
import Host.ObjectiveBendPreview
import Theory.AssertCompiled

open Lean (Json toJson)

namespace Minidregg.Examples.LazySharedField

def packet : String := include_str "LazySharedField.typed.json"
def limits : String := "{\"ticks\":\"100000\",\"heap\":\"100000\",\"stack\":\"10000\"}"

def observation : Except String Json := do
  Minidregg.Host.ObjectiveBendPreview.preview (← Json.parse packet) (← Json.parse limits)

def summary (json : Json) : Except String Json := do
  pure <| Json.mkObj [("name", toJson "LazySharedField"), ("status", ← json.getObjVal? "status"),
    ("type", ← (← json.getObjVal? "type").getObjVal? "tag"), ("result", ← json.getObjVal? "result"),
    ("uses", ← json.getObjVal? "uses"), ("typing", ← json.getObjVal? "typing")]

def expected : Json := Json.mkObj [("name", toJson "LazySharedField"), ("status", toJson "finished"),
  ("type", toJson "natural"), ("result", Json.mkObj [("tag", toJson "natural"), ("value", toJson "512")]), ("uses", Json.arr #[]),
  ("typing", toJson "accepted by actual annotated checker")]

def holds : Bool := match observation >>= summary with
  | .ok json => json == expected
  | .error _ => false

theorem LazySharedField_observed : holds = true := by native_decide
#assert_compiled LazySharedField_observed

/-! Call-by-need sharing. `Pair.costly` is `work(8n)` and `twice` selects it twice.
`entries` counts, over the whole bounded run of the checked packet's term, how often
the machine enters a still-suspended cell; every record cell on the final heap with a `costly` field has that field entered
exactly once (counts `[1, 1]`: the tied record and the extension's record), so the second
selection of `costly` reads the cached value rather than re-entering it. -/

open Minidregg.Theory.ObjectiveBendDemandMachine in
def entries : Nat → State → List Nat → State × List Nat
  | 0, state, seen => (state, seen)
  | fuel + 1, state, seen =>
    let seen := match state.control with
      | .enter address => match state.heap[address]? with
        | some (.suspended _) => address :: seen
        | _ => seen
      | _ => seen
    match step ⟨100000, 10000⟩ state with
    | .suspended .ticks next => entries fuel next seen
    | .finished _ final | .suspended _ final | .divergent _ final | .refused _ final | .yielded _ final => (final, seen)

open Minidregg.Theory.ObjectiveBendDemandMachine in
def costlyEntries : Except String (List Nat) := do
  let decoded ← Minidregg.Theory.ObjectiveBendTyping.decodePacket (← Json.parse packet)
  let (final, seen) := entries 100000 (initial decoded.source.term) []
  let addresses := final.heap.toList.filterMap fun cell => match cell with
    | .cached _ (.record fields) => (fields.find? (fun field => field.1 == "costly")).map Prod.snd
    | _ => none
  pure <| addresses.map fun address => (seen.filter (· == address)).length

def costlyEnteredOnce : Bool := match costlyEntries with
  | .ok counts => !counts.isEmpty && counts.all (· == 1)
  | .error _ => false

theorem LazySharedField_costly_entered_once : costlyEnteredOnce = true := by native_decide
#assert_compiled LazySharedField_costly_entered_once

#eval costlyEntries

open Minidregg.Examples.LazySharedField in
#eval show IO Unit from do
  match observation >>= summary with
  | .ok json =>
    IO.println json.compress
    unless json == expected do throw (IO.userError "LazySharedField: observation differs from the expected summary")
  | .error message => throw (IO.userError message)

end Minidregg.Examples.LazySharedField
