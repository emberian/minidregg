/-
# `law-sat` on the wire (C-SAT-2, session op 150, CLI `law-sat REQUEST.json RESULT.json`)

The request is the law as the client already spells it: the predicate JSON a `law` proposal
carries and the signed `policy` view returns, so a friend can ask about a law before
installing it and about the law a cell holds now. Nothing in it names the Store and the
Host reads none (`lawSat_reads_no_store`): the reply is a function of the request bytes.

```
{"type":"minidregg-law-sat-v1", "predicate": LAW, "extra": CLAUSE?, "fromHere": BOOL?}
```

The reply is `150 ‖ UTF-8 JSON`, one of

* `{"verdict":"outside", "part", "path", "clause"}` — the first `witnessed`/`hashEq`/`ran`
  leaf (`lawSat_outside_is_untranslatable`);
* `{"verdict":"unrealizable", "slot", "name"}` — a `fromHere` query on a law that reads the
  old value of a slot the declared scalar step shape does not model;
* `{"verdict":"witness", "systems", "old", "new"}` — slot lists (`lawSat_witness_admits`,
  `lawSat_witness_admits_from_here`);
* `{"verdict":"unsat", "systems", "certificate"}` — one entry per system: a `clash` or a
  `cycle` of constraints, each with its text and the clauses of the law it came from
  (`lawSat_unsat_admits_nothing`, `lawSat_unsat_from_here`);
* `{"verdict":"unknown", "reason":"cap", "cap":1024}` — the translation passed `dnfCap`.

Every `witness`/`unsat` reply is `Sat.decide` on the decoded query (`lawSat_is_decide`).
-/
import Host.Json
import Host.LawSat

namespace Minidregg.Host.LawSatWire

open Lean
open Minidregg.Pred
open Minidregg.Pred.Sat
open Minidregg.Host.LawSat

set_option autoImplicit false

def renderSlot (s : Slot) : String := Minidregg.Compiler.LawLeaf.renderSlot s
def renderValue (s : Slot) (v : Int) : String := Minidregg.Compiler.LawLeaf.renderValue s v
def renderClause (p : Pred) : String := Minidregg.Compiler.LawLeaf.renderClause p

/-! ## Rendering a certificate as the law's own clauses -/

def nodeText : Node → String
  | .zero => "0"
  | .old s => s!"{renderSlot s} (before the step)"
  | .new s => renderSlot s

def valueText (v : Node) (k : Int) : String :=
  match v with
  | .old s => renderValue s k
  | .new s => renderValue s k
  | .zero => toString k

/-- `val x ≤ val y + k`, in the shell's grammar. -/
def conText (c : Con) : String :=
  match c.x, c.y with
  | .zero, .zero => s!"0 <= {c.k}"
  | .zero, y => s!"{nodeText y} >= {valueText y (-c.k)}"
  | x, .zero => s!"{nodeText x} <= {valueText x c.k}"
  | x, y =>
      if c.k = 0 then s!"{nodeText x} <= {nodeText y}"
      else if 0 < c.k then s!"{nodeText x} <= {nodeText y} + {c.k}"
      else s!"{nodeText x} <= {nodeText y} - {-c.k}"

def nodeJson : Node → Json
  | .zero => Json.mkObj [("view", "zero")]
  | .old s => Json.mkObj [("view", "old"), ("slot", s), ("name", renderSlot s)]
  | .new s => Json.mkObj [("view", "new"), ("slot", s), ("name", renderSlot s)]

mutual
/-- Every leaf of `p` with its path (`Pred.subterm`'s convention) and the polarity at which
it is translated (`dnf` flips it under `not`). -/
def leaves (b : Bool) (path : List Nat) : Pred → List (List Nat × Bool × Pred)
  | .not q => leaves (!b) (path ++ [0]) q
  | .allL ps => leavesList b path 0 ps
  | .anyL ps => leavesList b path 0 ps
  | p => [(path, b, p)]
def leavesList (b : Bool) (path : List Nat) (i : Nat) : PredList → List (List Nat × Bool × Pred)
  | .nil => []
  | .cons q rest => leaves b (path ++ [i]) q ++ leavesList b path (i + 1) rest
end

/-- The leaves of the translated predicate whose own systems contain what `keep` looks for. -/
def sources (t : Pred) (keep : Sys → Bool) : List (List Nat) :=
  ((leaves true [] t).filterMap fun (path, b, atom) =>
    match atomDnf b atom with
    | some ss => if ss.any keep then some path else none
    | none => none).eraseDups

/-- A clause the friend wrote as one: an atom, or the negation of one (a guard
`not (verb == write)` is named whole). -/
def isAtom : Pred → Bool
  | .not (.not _) | .not (.allL _) | .not (.anyL _) => false
  | .not _ => true
  | .allL _ | .anyL _ => false
  | _ => true

/-- The clause of the asked predicate a path of the translated one lies in: realization
replaces an atom by a small tree at the same path, so the atom is at a prefix. -/
def clauseAt (orig : Pred) (path : List Nat) : List Nat × Pred :=
  ((List.range (path.length + 1)).findSome? fun k =>
    match orig.subterm (path.take k) with
    | some c => if isAtom c then some (path.take k, c) else none
    | none => none).getD (path, orig)

def sourceJson (q : Query) (path : List Nat) : Json :=
  let (at_, clause) := clauseAt q.pred path
  match at_ with
  | 0 :: rest =>
      let top := match rest.head?.bind (fun i => q.law.subterm [i]) with
        | some c => ([("top", Json.mkObj [("index", toJson rest.head!),
            ("clause", renderClause c)])] : List (String × Json))
        | none => []
      let base : List (String × Json) :=
        [("part", "law"), ("path", toJson rest), ("clause", renderClause clause)]
      Json.mkObj (base ++ top)
  | _ :: rest =>
      Json.mkObj [("part", "query"), ("path", toJson rest), ("clause", renderClause clause)]
  | [] => Json.mkObj [("part", "query"), ("path", toJson ([] : List Nat)),
      ("clause", renderClause clause)]

def conJson (q : Query) (t : Pred) (c : Con) : Json :=
  Json.mkObj [("text", conText c), ("x", nodeJson c.x), ("y", nodeJson c.y), ("k", toJson c.k),
    ("sources", Json.arr ((sources t (fun s => s.cons.contains c)).map (sourceJson q)).toArray)]

def certJson (q : Query) (t : Pred) : SysCert → Json
  | .clash v => Json.mkObj [("kind", "clash"), ("node", nodeJson v),
      ("text", s!"{nodeText v} must be both present and absent"),
      ("sources", Json.arr ((sources t (fun s => s.present.contains v || s.absent.contains v)).map
        (sourceJson q)).toArray)]
  | .cycle cs => Json.mkObj [("kind", "cycle"), ("sum", toJson (cs.map Con.k).sum),
      -- The exact decimal: subject ids exceed 2^63, and a JSON number past i64
      -- reached the client as 0 ("0 <= 0") (FIX-DISCLOSE).
      ("sumText", Json.str (toString (cs.map Con.k).sum)),
      ("constraints", Json.arr (cs.map (conJson q t)).toArray)]

def stateJson (s : State) : Json :=
  Json.arr (s.slots.map fun (slot, v) => Json.mkObj [("slot", slot), ("name", renderSlot slot),
    ("value", toString v), ("text", renderValue slot v)]).toArray

/-- The reply for one answer. -/
def answerJson (q : Query) : Answer → Json
  | .outside path =>
      let (part, rest) := match path with
        | 0 :: rest => ("law", rest)
        | _ :: rest => ("query", rest)
        | [] => ("query", [])
      Json.mkObj [("verdict", "outside"), ("part", part), ("path", toJson rest),
        ("clause", ((q.pred.subterm path).map renderClause).getD "")]
  | .unrealizable slot => Json.mkObj [("verdict", "unrealizable"), ("slot", slot),
      ("name", renderSlot slot)]
  | .decided d (.witness o n) => Json.mkObj [("verdict", "witness"),
      ("systems", toJson d.systems.length), ("old", stateJson o), ("new", stateJson n)]
  | .decided d (.unsat c) => Json.mkObj [("verdict", "unsat"),
      ("systems", toJson d.systems.length),
      ("certificate", Json.arr (c.map (certJson q d.source)).toArray)]
  | .decided _ .unknown => Json.mkObj [("verdict", "unknown"), ("reason", "decide")]
  | .pastCap => Json.mkObj [("verdict", "unknown"), ("reason", "cap"), ("cap", toJson dnfCap)]

/-! ## Decoding the request -/

def requestType : String := "minidregg-law-sat-v1"

def query (json : Json) : Except String Query := do
  let obj ← json.getObj?.mapError (fun e => s!"law-sat request: {e}")
  let keys := obj.foldl (init := []) (fun names key _ => key :: names)
  for key in keys do
    unless ["type", "predicate", "extra", "fromHere"].contains key do
      throw s!"law-sat request: unknown field {key}"
  match obj.get? "type" with
  | some (.str t) => unless t == requestType do throw s!"law-sat request: type is not {requestType}"
  | _ => throw "law-sat request: missing type"
  let some lawJson := obj.get? "predicate" | throw "law-sat request: missing predicate"
  let law ← Minidregg.Host.Json.predicate "predicate" lawJson
  let extra ← match obj.get? "extra" with
    | none => pure (Pred.all [])
    | some j => Minidregg.Host.Json.predicate "extra" j
  let fromHere ← match obj.get? "fromHere" with
    | none => pure false
    | some (.bool b) => pure b
    | some _ => throw "law-sat request: fromHere is not a boolean"
  pure ⟨law, extra, fromHere⟩

def decode (payload : List UInt8) : Except String Query := do
  let some text := String.fromUTF8? ⟨payload.toArray⟩ | throw "law-sat request is not UTF-8"
  query (← Minidregg.Host.Json.parse text)

/-- The served reply: the decoded query's `answer`, rendered. -/
def lawSatReply (payload : List UInt8) : Except String Json := do
  let q ← decode payload
  pure (answerJson q (answer q))

/-- **`lawSat_reply_is_answer`** — the reply to a request that decodes to `q` is `answer q`,
and nothing else (so, with `LawSat.lawSat_is_decide`, `Sat.decide` on the decoded law). -/
theorem lawSat_reply_is_answer (payload : List UInt8) (q : Query) (h : decode payload = .ok q) :
    lawSatReply payload = .ok (answerJson q (answer q)) := by
  simp [lawSatReply, h, bind, Except.bind, pure, Except.pure]

/-- The FFI symbol: request bytes in, reply JSON bytes out (`{"error": …}` on a malformed
request). -/
@[export minidregg_law_sat]
def lawSatExport (payload : ByteArray) : ByteArray :=
  match lawSatReply payload.toList with
  | .ok value => value.compress.toUTF8
  | .error e => (Json.mkObj [("error", e)]).compress.toUTF8

theorem lawSatExport_answers (payload : ByteArray) (q : Query) (h : decode payload.toList = .ok q) :
    lawSatExport payload = (answerJson q (answer q)).compress.toUTF8 := by
  simp [lawSatExport, lawSat_reply_is_answer _ q h]

/-- Session op 150. It is handed the payload and nothing else: no configuration, no session,
no Store handle. -/
def lawSatSession (payload : List UInt8) : IO (UInt8 × List UInt8) := do
  let value ← IO.ofExcept (lawSatReply payload)
  return (150, value.compress.toUTF8.toList)

/-- **`lawSat_reads_no_store`** — the op's IO is `IO.ofExcept` of a pure function of the request
bytes: whatever Store, configuration or session the Host holds, the reply is the same, and the
op performs no other effect. (Op 130's `submit_storage_irrelevant` needs a theorem because its
program receives the Store; this one never does, and the statement says what it is.) -/
theorem lawSat_reads_no_store (payload : List UInt8) :
    lawSatSession payload =
      (IO.ofExcept (lawSatReply payload) >>= fun value =>
        pure (150, value.compress.toUTF8.toList)) := rfl

#assert_axioms lawSat_reply_is_answer
#assert_axioms lawSatExport_answers
#assert_axioms lawSat_reads_no_store

end Minidregg.Host.LawSatWire
