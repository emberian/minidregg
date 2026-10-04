/-
# Compiler.FnWireJson — fn's `specs/wire-grammar.json`, read and checked

The loader of fn's exported grammar file (language `fn-wire-grammar`, version 1; fn
`planning/design/wire-grammar-2026-10-04.md` §2–§3). Grammars, values and vectors are read
from their JSON forms exactly as §2 writes them; anything else is refused by name:
an unknown node, a wrong arity, a non-canonical hex string (fn writes lower case), a value
outside its grammar's JSON shape, a grammar `Grammar.wf` rejects, an unknown language
version, an unknown refusal word.

`checkDoc` is the contract check: every vector's octets get exactly the decoder answer the
file prints (value, octets consumed and rest; or the refusal word), and an accepted value
re-encodes to exactly the consumed octets. It requires the coverage fn §3 promises per
family and returns the counts, so a file with no vectors cannot read as a pass.
-/
import Lean.Data.Json
import Compiler.FnWireGrammar

namespace Minidregg.Compiler.FnWire

set_option autoImplicit false

open Lean (Json)
open Minidregg.Compiler

/-! ## Hex -/

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Lower-case hex only (fn's value JSON); anything else is refused. -/
def hexBytes? : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
      let x ← hexDigit? a
      let y ← hexDigit? b
      let tail ← hexBytes? rest
      pure (UInt8.ofNat (16 * x + y) :: tail)
  | [_] => none

def ofHex (label : String) (s : String) : Except String (List UInt8) :=
  match hexBytes? s.toList with
  | some b => .ok b
  | none => .error s!"{label}: not lower-case hex: {s}"

/-! ## JSON plumbing -/

def jNat (label : String) (j : Json) : Except String Nat :=
  match j.getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"{label}: not a natural: {j.compress}"

def jStr (label : String) (j : Json) : Except String String :=
  match j with
  | .str s => .ok s
  | _ => .error s!"{label}: not a string: {j.compress}"

def jArr (label : String) (j : Json) : Except String (List Json) :=
  match j with
  | .arr a => .ok a.toList
  | _ => .error s!"{label}: not an array: {j.compress}"

def jField (label key : String) (j : Json) : Except String Json :=
  match j.getObjVal? key with
  | .ok v => .ok v
  | .error _ => .error s!"{label}: missing field {key}"

def octetClass (s : String) : Except String OctetClass :=
  match s with
  | "any" => .ok .any
  | "utf8" => .ok .utf8
  | "header" => .ok .header
  | _ => .error s!"unknown octet class {s}"

def check (j : Json) : Except String Check := do
  match ← jArr "check" j with
  | [.str "le", i, k] => return .le (← jNat "le" i) (← jNat "le" k)
  | [.str "eq", i, k] => return .eq (← jNat "eq" i) (← jNat "eq" k)
  | [.str "diff", k, j', i] => return .diff (← jNat "diff" k) (← jNat "diff" j') (← jNat "diff" i)
  | _ => throw s!"unknown check {j.compress}"

def octet (label : String) (j : Json) : Except String UInt8 := do
  let n ← jNat label j
  unless n < 256 do throw s!"{label}: not an octet: {n}"
  return UInt8.ofNat n

mutual
/-- A grammar node from its JSON form (fn §2's table, column "JSON"). -/
partial def grammarOfJson (j : Json) : Except String Grammar := do
  match ← jArr "grammar" j with
  | [.str "const", h] => return .const (← ofHex "const" (← jStr "const" h))
  | [.str "uint", w, lo, hi] => return .uint (← jNat "uint" w) (← jNat "uint" lo) (← jNat "uint" hi)
  | [.str "bytes", w, lo, hi, c] =>
      return .bytes (← jNat "bytes" w) (← jNat "bytes" lo) (← jNat "bytes" hi)
        (← octetClass (← jStr "bytes" c))
  | [.str "rest", lo, hi, c] =>
      return .rest (← jNat "rest" lo) (← jNat "rest" hi) (← octetClass (← jStr "rest" c))
  | [.str "line", lo, hi, c] =>
      return .line (← jNat "line" lo) (← jNat "line" hi) (← octetClass (← jStr "line" c))
  | [.str "base64-lines", w, lo, hi] =>
      return .base64Lines (← jNat "base64-lines" w) (← jNat "base64-lines" lo)
        (← jNat "base64-lines" hi)
  | [.str "enum", w, base, names] =>
      return .enum (← jNat "enum" w) (← jNat "enum" base)
        (← (← jArr "enum" names).mapM (jStr "enum name"))
  | [.str "seq", elems] => seqOfJson (← jArr "seq" elems)
  | [.str "tag", w, arms] => tagOfJson (← jNat "tag" w) (← jArr "tag" arms)
  | [.str "maybe", g] => return .maybe (← grammarOfJson g)
  | [.str "where", g, checks] =>
      return .where_ (← grammarOfJson g) (← (← jArr "where" checks).mapM check)
  | [.str "frame", magic, version, kind, max, g] =>
      return .frame (← ofHex "frame magic" (← jStr "frame" magic)) (← octet "frame version" version)
        (← octet "frame kind" kind) (← jNat "frame" max) (← grammarOfJson g)
  | _ => throw s!"unknown grammar node {j.compress}"

partial def seqOfJson : List Json → Except String Grammar
  | [] => .ok .seqNil
  | g :: gs => do return .seqCons (← grammarOfJson g) (← seqOfJson gs)

partial def tagOfJson (w : Nat) : List Json → Except String Grammar
  | [] => .ok (.tagNil w)
  | arm :: arms => do
      match ← jArr "tag arm" arm with
      | [code, .str name, g] =>
          return .tagArm w (← jNat "tag code" code) name (← grammarOfJson g) (← tagOfJson w arms)
      | _ => throw s!"bad tag arm {arm.compress}"
end

/-- A grammar from JSON, refused unless well formed. -/
def loadGrammar (j : Json) : Except String Grammar := do
  let g ← grammarOfJson j
  unless g.wf do throw s!"grammar is not well formed: {j.compress}"
  return g

/-! ## Values -/

/-- A value of `g` from its JSON form (fn §2 "Value JSON"). -/
def valueOfJson : Grammar → Json → Except String Value
  | .const _, .null => .ok .null
  | .uint _ _ _, j => do return .nat (← jNat "uint value" j)
  | .bytes _ _ _ _, j | .rest _ _ _, j | .line _ _ _, j | .base64Lines _ _ _, j => do
      return .octets (← ofHex "octets value" (← jStr "octets value" j))
  | .enum _ _ _, j => do return .name (← jStr "enum value" j)
  | .seqNil, .arr a =>
      if a.isEmpty then .ok (.list []) else .error "seq value too long"
  | .seqCons h t, .arr a =>
      match a.toList with
      | [] => .error "seq value too short"
      | x :: xs => do
          let v ← valueOfJson h x
          match ← valueOfJson t (.arr xs.toArray) with
          | .list vs => return .list (v :: vs)
          | _ => throw "seq value"
  | .tagNil _, j => .error s!"no tag arm for {j.compress}"
  | .tagArm _ _ name arm more, .arr a =>
      match a.toList with
      | [.str n, x] =>
          if n = name then do return .tagged n (← valueOfJson arm x)
          else valueOfJson more (.arr a)
      | _ => .error s!"tag value {(Json.arr a).compress}"
  | .maybe g, .arr a =>
      match a.toList with
      | [] => .ok (.list [])
      | [x] => do return .list [← valueOfJson g x]
      | _ => .error "maybe value"
  | .where_ g _, j => valueOfJson g j
  | .frame _ _ _ _ g, j => valueOfJson g j
  | _, j => .error s!"value does not fit its grammar: {j.compress}"

def hexOf (b : List UInt8) : String := Blake3.toHex b

/-- A value's JSON form (fn §2 "Value JSON"). -/
partial def valueToJson : Value → Json
  | .null => .null
  | .nat n => Lean.toJson n
  | .octets b => .str (hexOf b)
  | .name s => .str s
  | .list vs => .arr (vs.map valueToJson).toArray
  | .tagged n v => .arr #[.str n, valueToJson v]

/-! ## The file -/

structure Family where
  name : String
  grammar : Grammar

/-- What a passing check counted. -/
structure Summary where
  families : Nat
  accepted : Nat
  refused : Nat
  deriving DecidableEq, Repr

/-- The vector kinds of fn §3. -/
def vectorKinds : List String := ["accept", "concat", "prefix", "mutation", "length"]

/-- What one vector checked: its kind and, when refused, the word. -/
structure Checked where
  kind : String
  refused : Option String

/-- One vector against the decoder's whole answer (fn §2 "Decoding", §3): every vector names
its family, the language version and its kind; an accepting vector names the value, the
octets consumed and the rest, and the value re-encodes to exactly the consumed octets; a
refusing vector names the refusal word, and the decoder refuses with that word (a refusal
consumes nothing). -/
def vectorCheck (fam : Family) (version : Nat) (v : Json) : Except String Checked := do
  let label := fam.name
  unless (← jStr label (← jField label "family" v)) == fam.name do
    throw s!"{label}: vector names another family"
  unless (← jNat label (← jField label "version" v)) == version do
    throw s!"{label}: vector of another language version"
  let kind ← jStr label (← jField label "kind" v)
  unless vectorKinds.contains kind do throw s!"{label}: unknown vector kind {kind}"
  let octets ← ofHex label (← jStr label (← jField label "octets" v))
  let at_ := s!"{label} {kind} {(hexOf octets).take 80}"
  match v.getObjVal? "refused" with
  | .ok word =>
      let word ← jStr label word
      unless word == "trailer" || word == "malformed" do
        throw s!"{at_}: unknown refusal word {word}"
      match decode fam.grammar octets with
      | .ok (got, _) => throw s!"{at_}: accepted a refusal vector as {(valueToJson got).compress}"
      | .error r =>
          unless r.fnWord == word do
            throw s!"{at_}: refused {r.fnWord} where the file says {word}"
          return { kind, refused := some word }
  | .error _ =>
      let valueJ ← jField label "value" v
      let value ← valueOfJson fam.grammar valueJ
      let consumed ← jNat label (← jField label "consumed" v)
      let rest ← ofHex label (← jStr label (← jField label "rest" v))
      match decode fam.grammar octets with
      | .error r => throw s!"{at_}: refused ({r.fnWord}) a vector the file accepts"
      | .ok (got, gotRest) =>
          unless (valueToJson got).compress == valueJ.compress do
            throw s!"{at_}: decoded {(valueToJson got).compress}, the file says {valueJ.compress}"
          unless gotRest == rest do throw s!"{at_}: rest {hexOf gotRest}, the file says {hexOf rest}"
          unless octets.length - gotRest.length == consumed do
            throw s!"{at_}: consumed {octets.length - gotRest.length}, the file says {consumed}"
          match encode fam.grammar got with
          | .ok b => unless b == octets.take consumed do throw s!"{at_}: re-encoding differs: {hexOf b}"
          | .error r => throw s!"{at_}: re-encoding refused ({r.fnWord})"
          match encode fam.grammar value with
          | .ok b => unless b == octets.take consumed do
              throw s!"{at_}: the file's value encodes to {hexOf b}"
          | .error r => throw s!"{at_}: the file's value is refused by the encoder ({r.fnWord})"
          return { kind, refused := none }

def Grammar.isFrame : Grammar → Bool
  | .frame _ _ _ _ _ => true
  | _ => false

/-- The language version this interpreter speaks; any other is refused by name. -/
def languageVersion : Nat := 1

/-- Parse the file, check its header, load every family (refusing a non-well-formed
grammar or a duplicated name). -/
def loadDoc (text : String) : Except String (Json × List (Family × List Json)) := do
  let doc ← match Json.parse text with
    | .ok d => pure d
    | .error e => throw s!"wire grammar file is not JSON: {e}"
  unless (← jStr "format" (← jField "file" "format" doc)) == "fn-wire-grammar" do
    throw "not an fn-wire-grammar file"
  let version ← jNat "version" (← jField "file" "version" doc)
  unless version == languageVersion do
    throw s!"fn-wire-grammar version {version} is not version {languageVersion}"
  unless (← jStr "trailer" (← jField "file" "trailer" doc)) == "blake3-256" do
    throw "frame trailer is not blake3-256"
  let fams ← (← jArr "families" (← jField "file" "families" doc)).mapM fun f => do
    let name ← jStr "family name" (← jField "family" "name" f)
    let g ← loadGrammar (← jField name "grammar" f)
    let vs ← jArr name (← jField name "vectors" f)
    pure (({ name, grammar := g } : Family), vs)
  let names := fams.map (·.1.name)
  unless distinct names do throw "duplicated family name"
  return (doc, fams)

/-- The contract check over a whole file. -/
def checkDoc (text : String) : Except String Summary := do
  let (doc, fams) ← loadDoc text
  let names := fams.map (·.1.name)
  let mut accepted := 0
  let mut refused := 0
  for (fam, vs) in fams do
    let mut seen : List Checked := []
    for v in vs do
      let c ← vectorCheck fam languageVersion v
      seen := c :: seen
      if c.refused.isSome then refused := refused + 1 else accepted := accepted + 1
    -- Coverage (fn §3): the encodings, every truncation boundary, every one-octet change;
    -- for a frame also the declared-length vectors and both refusal words.
    for k in ["accept", "prefix", "mutation"] do
      unless seen.any (·.kind == k) do throw s!"{fam.name}: no {k} vectors"
    if fam.grammar.isFrame then
      unless seen.any (·.kind == "length") do throw s!"{fam.name}: no length vectors"
      for w in ["trailer", "malformed"] do
        unless seen.any (·.refused == some w) do throw s!"{fam.name}: no {w} refusal vector"
  for ex in ← jArr "exchanges" (← jField "file" "exchanges" doc) do
    let req ← jStr "exchange" (← jField "exchange" "request" ex)
    unless names.contains req do throw s!"exchange names an unknown request family {req}"
    for rep in ← jArr "exchange" (← jField "exchange" "replies" ex) do
      let rep ← jStr "exchange reply" rep
      unless names.contains rep do throw s!"exchange names an unknown reply family {rep}"
  return { families := fams.length, accepted, refused }

def checkPasses (text : String) (expected : Summary) : Bool :=
  match checkDoc text with
  | .ok s => s == expected
  | .error _ => false

def checkRefuses (text : String) : Bool :=
  match checkDoc text with
  | .ok _ => false
  | .error _ => true

/-- A family's grammar, by NAME (never by FNCT kind). -/
def familyGrammar (text : String) (name : String) : Except String Grammar := do
  let (_, fams) ← loadDoc text
  match fams.find? (·.1.name == name) with
  | some (f, _) => return f.grammar
  | none => throw s!"no family {name}"

def familyIs (text name : String) (g : Grammar) : Bool :=
  match familyGrammar text name with
  | .ok g' => decide (g' = g)
  | .error _ => false

end Minidregg.Compiler.FnWire
