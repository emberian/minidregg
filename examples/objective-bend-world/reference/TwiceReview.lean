/- Objective Bend reference example: TwiceReview.

Three composed specifications: BaseReview.review v = v+1, AugmentedReview.review v = super.review v + 1, TwiceReview.twice v = self.review (self.review v), so twice(3) = ((3+2)+2) = 7. self-dispatch sees the augmented override; super sees the base.

Source:   tests/objective-bend-source/ (see the `TwiceReview` row of preview-cohort.json)
Packet:   TwiceReview.typed.json, the typed core packet the current front end produces
          for that row (parser, capture, elaborator, annotation proposal).
          scripts/check-objective-examples.sh fails when it is stale;
          `scripts/check-objective-examples.sh --refresh` rewrites it.
Run:      lake env lean examples/objective-bend-world/reference/TwiceReview.lean

`observation` is the generic typed preview (`Host.ObjectiveBendPreview.preview`):
decode the packet, run `check` (typing and ownership), then `runBounded` on the same
decoded term. The theorem pins the checked type, the observed result and the empty
use set; it rests on the compiled evaluator (`native_decide`), which
`#assert_compiled` re-runs and names. `main` prints the same summary and exits 1
on a mismatch. -/
import Host.ObjectiveBendPreview
import Theory.AssertCompiled

open Lean (Json toJson)

namespace Minidregg.Examples.TwiceReview

def packet : String := include_str "TwiceReview.typed.json"
def limits : String := "{\"ticks\":\"100000\",\"heap\":\"100000\",\"stack\":\"10000\"}"

def observation : Except String Json := do
  Minidregg.Host.ObjectiveBendPreview.preview (← Json.parse packet) (← Json.parse limits)

def summary (json : Json) : Except String Json := do
  pure <| Json.mkObj [("name", toJson "TwiceReview"), ("status", ← json.getObjVal? "status"),
    ("type", ← (← json.getObjVal? "type").getObjVal? "tag"), ("result", ← json.getObjVal? "result"),
    ("uses", ← json.getObjVal? "uses"), ("typing", ← json.getObjVal? "typing")]

def expected : Json := Json.mkObj [("name", toJson "TwiceReview"), ("status", toJson "finished"),
  ("type", toJson "natural"), ("result", Json.mkObj [("tag", toJson "natural"), ("value", toJson "7")]), ("uses", Json.arr #[]),
  ("typing", toJson "accepted by actual annotated checker")]

def holds : Bool := match observation >>= summary with
  | .ok json => json == expected
  | .error _ => false

theorem TwiceReview_observed : holds = true := by native_decide
#assert_compiled TwiceReview_observed

open Minidregg.Examples.TwiceReview in
#eval show IO Unit from do
  match observation >>= summary with
  | .ok json =>
    IO.println json.compress
    unless json == expected do throw (IO.userError "TwiceReview: observation differs from the expected summary")
  | .error message => throw (IO.userError message)

end Minidregg.Examples.TwiceReview
