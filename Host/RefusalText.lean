/-
# Host.RefusalText -- the clause a controller's refusal names, in words a requester reads

An `operationRejected` refusal carries its controller's typed `Reject` (`Compiler.RefusalReason`
says so: the one reason whose detail is a typed value, reached after the requester's read
authority is established). The Host commits that detail as the `repr` of the value, for example
`invocation preparation: A.Reject.scalar (B.Reject.pageMutation (C.RejectReason.overflow))` or
`guardRejected 0`. That is exact and stays committed; it is not what a person should have to read.

`render` is the one place that turns it into the clause path: each constructor reduced to its own
name in kebab case, nesting joined by `: `, a numeric argument kept as written
(`invocation preparation: scalar: page-mutation: overflow`, `guard-rejected 0`). It reads the text
only (a pure function of one string), reaches no state, and so discloses nothing the refusal frame
did not already carry to this requester. A name is a word beginning with a capital letter and made
of dot-separated segments (a qualified constructor), or a lower camel-case word of letters only
(a bare constructor); every other word, number and symbol is left exactly as it was.
-/
module

@[expose] public section

namespace Minidregg.Host.RefusalText

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '\''

/-- `pageMutation` becomes `page-mutation`. -/
def kebab (word : String) : String :=
  let dashed := String.ofList <| word.toList.flatMap fun c =>
    if c.isUpper then ['-', c.toLower] else [c]
  if dashed.startsWith "-" then (dashed.drop 1).toString else dashed

/-- A bare constructor: a lower-case letter, then letters only, with at least one capital inside
and every capital followed by a lower-case letter (`guardRejected`, `pageMutation`). -/
def isCamel (word : String) : Bool :=
  let cs := word.toList
  match cs with
  | [] => false
  | first :: rest =>
      first.isLower && cs.all Char.isAlpha && cs.any Char.isUpper &&
        (cs.zip (rest ++ ['a'])).all fun (c, next) => !c.isUpper || next.isLower

/-- A qualified constructor: at least two dot-separated segments, the first beginning with a
capital letter, none empty, each made of letters, digits and underscores. -/
def isQualified (word : String) : Bool :=
  let segments := word.splitOn "."
  segments.length ≥ 2 &&
    (segments.head?.bind (·.toList.head?)).any Char.isUpper &&
    segments.all fun s => !s.isEmpty && s.toList.all fun c => c.isAlphanum || c == '_'

/-- One word of the detail text. A sentence-final full stop after a name is kept outside it. -/
def word (w : String) : String :=
  let (body, stop) := if w.endsWith "." && w.length > 1 then (w.dropEnd 1 |>.toString, ".") else (w, "")
  if isQualified body then
    let segments := body.splitOn "."
    let ctor := kebab segments.getLast!
    -- The controller that raised it: the last segment before `Reject`/`RejectReason`.
    let owner := (segments.dropLast.reverse.dropWhile fun s => s == "Reject" || s == "RejectReason").head?
    (match owner with | some o => kebab o ++ ": " ++ ctor | none => ctor) ++ stop
  else if isCamel body then kebab body ++ stop
  else w

/-- The clause path of a controller refusal's detail. -/
def render (text : String) : String :=
  let rec go : List Char → String → String → String
    | [], pending, out => out ++ word pending
    | c :: rest, pending, out =>
        if isWordChar c then go rest (pending.push c) out
        else if c == '(' then go rest "" ((out ++ word pending).trimAsciiEnd.toString ++ ": ")
        else if c == ')' then go rest "" (out ++ word pending)
        else if c == '\n' || c == '\t' then go rest "" (out ++ word pending ++ " ")
        else go rest "" ((out ++ word pending).push c)
  collapse (go text.toList "" "")
where
  /-- Single spaces, and no space before a colon the nesting wrote. -/
  collapse (s : String) : String :=
    let rec squeeze : List Char → Bool → List Char
      | [], _ => []
      | c :: rest, prevSpace =>
          if c == ' ' then (if prevSpace then squeeze rest true else c :: squeeze rest true)
          else c :: squeeze rest false
    (String.ofList (squeeze s.toList false)).trimAscii.toString.replace ": :" ":"

#guard render "guardRejected 0" == "guard-rejected 0"
#guard render "invocation preparation: A.Reject.scalar\n  (B.Reject.pageMutation\n    (C.RejectReason.overflow))" ==
  "invocation preparation: a: scalar: b: page-mutation: c: overflow"
#guard render "ContentResource.Reject.staleAtom" == "content-resource: stale-atom"
#guard render "durable: Minidregg.Kernel.Durable.Reject.staleTarget" == "durable: durable: stale-target"
#guard render "request refused" == "request refused"
#guard render "undeclaredField 7" == "undeclared-field 7"
#guard render "path refs/tl.cast is not a reference" == "path refs/tl.cast is not a reference"
#guard render "tick 3 of 5." == "tick 3 of 5."
#guard render "Reject.descent." == "descent."
#guard render "DeclaredResourceScalar.Reject.guardRejected 0" == "declared-resource-scalar: guard-rejected 0"

end Minidregg.Host.RefusalText
