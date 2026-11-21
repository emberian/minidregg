/-
# `Kernel/ContentJson.lean` — the content command's JSON face

The request grammar of a content command (`{"type":"content","actions":[…]}`, one object per
action) and what a reader is shown of one. It is the JSON face of the content declaration
(`Kernel/ContentEffect.lean`, `contentEffect.ofJson`/`toJson`), so it sits upstream of the
registry; the Host's request decoder reads a content payload through the registry and has no
content arm. The strict helpers the grammar is written in (`failAt`, `tagged`, `decodeHex`,
`resourceKind`) are here too, and the Host's other decoders use these.
-/
module

public import Kernel.ResourceEffect
public import Kernel.ContentResource
public import Lean.Data.Json

import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.Range.Basic

@[expose] public section

namespace Minidregg.Kernel.ContentJson
open Minidregg
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController.EffectJson
  (exactObject field string nat int list optional decimal signedDecimal)
set_option autoImplicit false

def failAt {α : Type} (path message : String) : Except String α :=
  .error s!"{path}: {message}"

def object (path : String) (json : Lean.Json) :
    Except String (Std.TreeMap.Raw String Lean.Json compare) :=
  (json.getObj?).mapError (fun e => s!"{path}: {e}")

def bool (path : String) (json : Lean.Json) : Except String Bool :=
  json.getBool?.mapError (fun _ => s!"{path}: boolean expected")

def hexNibble (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def decodeHex (path : String) (json : Lean.Json) : Except String (List UInt8) := do
  let source ← string path json
  let input := source.toUTF8
  unless input.size % 2 = 0 do
    failAt path "even-length hexadecimal string expected"
  let mut output := ByteArray.empty
  for i in [:input.size / 2] do
    let high := hexNibble (Char.ofNat (input[2 * i]!.toNat))
    let low := hexNibble (Char.ofNat (input[2 * i + 1]!.toNat))
    match high, low with
    | some h, some l => output := output.push (UInt8.ofNat (16 * h + l))
    | _, _ => failAt path "even-length hexadecimal string expected"
  pure output.toList

def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)

def encodeHex (bytes : List UInt8) : String :=
  Id.run do
    let mut output := ByteArray.empty
    for byte in bytes do
      output := output.push (UInt8.ofNat ((hexDigit (byte.toNat / 16)).toNat))
      output := output.push (UInt8.ofNat ((hexDigit (byte.toNat % 16)).toNat))
    return String.fromUTF8! output

def tagged (path : String) (json : Lean.Json) : Except String
    (String × Std.TreeMap.Raw String Lean.Json compare) := do
  let obj ← object path json
  let tag ← string (path ++ ".type") (← field path "type" obj)
  pure (tag, obj)

def resourceKind (path : String) (json : Lean.Json) : Except String ResourceKind := do
  match ← string path json with
  | "object" => pure .object
  | "account" => pure .account
  | "program" => pure .program
  | _ => failAt path "expected object, account, or program"

def identifier {version : Hyperdocument.CodecVersion} {domain : Hyperdocument.IdDomain}
    (path : String) (json : Lean.Json) : Except String (Hyperdocument.Identifier version domain) := do
  pure ⟨⟨← nat path json⟩⟩

def principal (path : String) (json : Lean.Json) : Except String Hyperdocument.PrincipalRef := do
  let obj ← exactObject path ["subject", "capabilityKind", "capability"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← resourceKind (path ++ ".capabilityKind") (← field path "capabilityKind" obj),
    ⟨← nat (path ++ ".capability") (← field path "capability" obj)⟩⟩

def authoredFragment (path : String) (json : Lean.Json) : Except String Hyperdocument.AuthoredFragment := do
  let obj ← exactObject path ["ciphertext", "wrapping", "author", "operation", "wrappedBy", "wrappedAt"] json
  pure ⟨← decodeHex (path ++ ".ciphertext") (← field path "ciphertext" obj),
    ← decodeHex (path ++ ".wrapping") (← field path "wrapping" obj),
    ← principal (path ++ ".author") (← field path "author" obj),
    ← identifier (path ++ ".operation") (← field path "operation" obj),
    ← principal (path ++ ".wrappedBy") (← field path "wrappedBy" obj),
    ← identifier (path ++ ".wrappedAt") (← field path "wrappedAt" obj)⟩

def atomKind (path : String) (json : Lean.Json) : Except String Hyperdocument.AtomKind := do
  let (tag, _) ← tagged path json
  match tag with
  | "text" => exactObject path ["type"] json *> pure .text
  | "inlineObject" =>
      let obj ← exactObject path ["type", "schema"] json
      pure (.inlineObject ⟨← nat (path ++ ".schema") (← field path "schema" obj)⟩)
  | "sealedObject" =>
      let obj ← exactObject path ["type", "schema", "fragment"] json
      pure (.sealedObject ⟨← nat (path ++ ".schema") (← field path "schema" obj)⟩
        (← authoredFragment (path ++ ".fragment") (← field path "fragment" obj)))
  | _ => failAt (path ++ ".type") "expected text, inlineObject or sealedObject"

def transclusionMode (path : String) (json : Lean.Json) :
    Except String Hyperdocument.TransclusionMode := do
  match ← string path json with
  | "snapshot" => pure .snapshot | "live" => pure .live
  | _ => failAt path "expected snapshot or live"

def atomRecord (path : String) (json : Lean.Json) : Except String Hyperdocument.AtomRecord := do
  let obj ← exactObject path ["document", "kind", "payload", "createdBy", "createdAt", "revision",
    "tombstonedAt"] json
  pure ⟨← identifier (path ++ ".document") (← field path "document" obj),
    ← atomKind (path ++ ".kind") (← field path "kind" obj),
    ← decodeHex (path ++ ".payload") (← field path "payload" obj),
    ← principal (path ++ ".createdBy") (← field path "createdBy" obj),
    ← identifier (path ++ ".createdAt") (← field path "createdAt" obj),
    ← identifier (path ++ ".revision") (← field path "revision" obj),
    ← optional (path ++ ".tombstonedAt") identifier (← field path "tombstonedAt" obj)⟩

def anchorBias (path : String) (json : Lean.Json) : Except String Hyperdocument.AnchorBias := do
  match ← string path json with
  | "before" => pure .before | "after" => pure .after
  | _ => failAt path "expected before or after"

def deathPolicy (path : String) (json : Lean.Json) : Except String Hyperdocument.EndpointDeathPolicy := do
  match ← string path json with
  | "invalidate" => pure .invalidate
  | "keepTombstone" => pure .keepTombstone
  | "preferPrevious" => pure .preferPrevious
  | "preferNext" => pure .preferNext
  | "preferPreviousThenNext" => pure .preferPreviousThenNext
  | "preferNextThenPrevious" => pure .preferNextThenPrevious
  | _ => failAt path "unknown endpoint death policy"

def stablePoint (path : String) (json : Lean.Json) : Except String Hyperdocument.StablePoint := do
  let obj ← exactObject path ["run", "neighbor", "bias", "death"] json
  pure ⟨← identifier (path ++ ".run") (← field path "run" obj),
    ← optional (path ++ ".neighbor") identifier (← field path "neighbor" obj),
    ← anchorBias (path ++ ".bias") (← field path "bias" obj),
    ← deathPolicy (path ++ ".death") (← field path "death" obj)⟩

def stableRange (path : String) (json : Lean.Json) : Except String Hyperdocument.StableRange := do
  let obj ← exactObject path ["start", "finish"] json
  pure ⟨← stablePoint (path ++ ".start") (← field path "start" obj),
    ← stablePoint (path ++ ".finish") (← field path "finish" obj)⟩

def pin (path : String) (json : Lean.Json) :
    Except String (Hyperdocument.AtomId × Hyperdocument.OperationId) := do
  let obj ← exactObject path ["atom", "revision"] json
  pure (← identifier (path ++ ".atom") (← field path "atom" obj),
    ← identifier (path ++ ".revision") (← field path "revision" obj))

def transcludeRequest (path : String) (json : Lean.Json) :
    Except String ContentResource.TranscludeRequest := do
  let obj ← exactObject path ["source", "range", "mode", "pins"] json
  pure ⟨← nat (path ++ ".source") (← field path "source" obj),
    ← stableRange (path ++ ".range") (← field path "range" obj),
    ← transclusionMode (path ++ ".mode") (← field path "mode" obj),
    ← list (path ++ ".pins") pin (← field path "pins" obj)⟩

def linkTarget (path : String) (json : Lean.Json) : Except String Hyperdocument.LinkTarget := do
  let (tag, _) ← tagged path json
  match tag with
  | "document" =>
      let obj ← exactObject path ["type", "id"] json
      pure (.document (← identifier (path ++ ".id") (← field path "id" obj)))
  | "element" =>
      let obj ← exactObject path ["type", "id"] json
      pure (.element (← identifier (path ++ ".id") (← field path "id" obj)))
  | "range" =>
      let obj ← exactObject path ["type", "document", "range"] json
      pure (.range (← identifier (path ++ ".document") (← field path "document" obj))
        (← stableRange (path ++ ".range") (← field path "range" obj)))
  | "external" =>
      let obj ← exactObject path ["type", "scheme", "authority", "path"] json
      pure (.external (← decodeHex (path ++ ".scheme") (← field path "scheme" obj))
        (← decodeHex (path ++ ".authority") (← field path "authority" obj))
        (← decodeHex (path ++ ".path") (← field path "path" obj)))
  | _ => failAt (path ++ ".type") "unknown link target"

/-- `{"type":"splice","index":N,"child":E}`, `{"type":"move","child":E,"index":N}` or
`{"type":"remove","child":E}`. -/
def elementOp (path : String) (json : Lean.Json) : Except String ContentResource.ElementOp := do
  let (tag, _) ← tagged path json
  match tag with
  | "splice" =>
      let obj ← exactObject path ["type", "index", "child"] json
      pure (.splice (← nat (path ++ ".index") (← field path "index" obj))
        (← identifier (path ++ ".child") (← field path "child" obj)))
  | "move" =>
      let obj ← exactObject path ["type", "child", "index"] json
      pure (.move (← identifier (path ++ ".child") (← field path "child" obj))
        (← nat (path ++ ".index") (← field path "index" obj)))
  | "remove" =>
      let obj ← exactObject path ["type", "child"] json
      pure (.remove (← identifier (path ++ ".child") (← field path "child" obj)))
  | _ => failAt (path ++ ".type") "expected splice, move or remove"

/-- `{"type":"atom","atom":A}` or `{"type":"element","element":E}`. -/
def markTarget (path : String) (json : Lean.Json) : Except String ContentResource.MarkTarget := do
  let (tag, _) ← tagged path json
  match tag with
  | "atom" =>
      let obj ← exactObject path ["type", "atom"] json
      pure (.atom (← identifier (path ++ ".atom") (← field path "atom" obj)))
  | "element" =>
      let obj ← exactObject path ["type", "element"] json
      pure (.element (← identifier (path ++ ".element") (← field path "element" obj)))
  | _ => failAt (path ++ ".type") "noSuchTarget: expected atom or element"

/-- `{"type":"bold"|"italic"|"code"|"heading"}` or
`{"type":"link","link":L,"target":TARGET}`; any other kind is refused
`unknownKind` here, since the kernel's grammar cannot carry one. -/
def markSpec (path : String) (json : Lean.Json) : Except String ContentResource.MarkSpec := do
  let (tag, _) ← tagged path json
  match tag with
  | "bold" =>
      let _ ← exactObject path ["type"] json
      pure ContentResource.MarkSpec.bold
  | "italic" =>
      let _ ← exactObject path ["type"] json
      pure ContentResource.MarkSpec.italic
  | "code" =>
      let _ ← exactObject path ["type"] json
      pure ContentResource.MarkSpec.code
  | "heading" =>
      let _ ← exactObject path ["type"] json
      pure ContentResource.MarkSpec.heading
  | "link" =>
      let obj ← exactObject path ["type", "link", "target"] json
      pure (.link (← identifier (path ++ ".link") (← field path "link" obj))
        (← linkTarget (path ++ ".target") (← field path "target" obj)))
  | other =>
      failAt (path ++ ".type") s!"unknownKind: {other} (expected bold, italic, code, heading or link)"

/-- Protected body provenance is normalized by the content receiver. -/
def annotationBody (path : String) (json : Lean.Json) : Except String Hyperdocument.AnnotationBody := do
  match json with
  | .str _ => pure (.inline (← decodeHex path json))
  | _ =>
      let obj ← exactObject path ["type", "fragment"] json
      if (← string (path ++ ".type") (← field path "type" obj)) != "sealed" then
        failAt path "expected sealed annotation body"
      else pure (.sealed (← authoredFragment (path ++ ".fragment") (← field path "fragment" obj)))

/-- The guard of `rewrapAnnotation` is the annotation's exact canonical store entry: the
bytes a signed view carries as the entry's `canonical`, address then record. It must be
canonical and must name the annotation being rewrapped; the record it carries is the
prior state the action is guarded on. -/
def annotationBefore (path : String) (annotation : Hyperdocument.AnnotationId)
    (json : Lean.Json) : Except String Hyperdocument.AnnotationRecord := do
  let bytes ← decodeHex path json
  let codec := StoreCodec.entryStream HyperdocumentCell.contentWire
  match codec.toLawful.decode bytes with
  | some entry =>
      match entry with
      | ⟨⟨.annotations, identifier⟩, record⟩ =>
          let identifier : Hyperdocument.AnnotationId := identifier
          let record : Hyperdocument.AnnotationRecord := record
          if identifier.digest.value != annotation.digest.value then
            failAt path "annotation guard names another annotation"
          else pure record
      | _ => failAt path "annotation guard is not an annotation entry"
  | none => failAt path "invalid exact annotation guard"

def contentAction (path : String) (json : Lean.Json) : Except String ContentResource.Action := do
  let (tag, _) ← tagged path json
  match tag with
  | "createDocument" =>
      let obj ← exactObject path ["type", "rootElement", "schema"] json
      pure (.createDocument (← identifier (path ++ ".rootElement") (← field path "rootElement" obj))
        ⟨← nat (path ++ ".schema") (← field path "schema" obj)⟩)
  | "createContainer" =>
      let obj ← exactObject path ["type", "element"] json
      pure (.createContainer (← identifier (path ++ ".element") (← field path "element" obj)))
  | "editElement" =>
      let obj ← exactObject path ["type", "element", "revision", "op"] json
      pure (.editElement ⟨← identifier (path ++ ".element") (← field path "element" obj),
        ← identifier (path ++ ".revision") (← field path "revision" obj),
        ← elementOp (path ++ ".op") (← field path "op" obj)⟩)
  | "createAtom" =>
      let obj ← exactObject path ["type", "atom", "kind", "payload"] json
      pure (.createAtom (← identifier (path ++ ".atom") (← field path "atom" obj))
        (← atomKind (path ++ ".kind") (← field path "kind" obj))
        (← decodeHex (path ++ ".payload") (← field path "payload" obj)))
  | "createRun" =>
      let obj ← exactObject path ["type", "run", "atoms"] json
      pure (.createRun (← identifier (path ++ ".run") (← field path "run" obj))
        (← list (path ++ ".atoms") identifier (← field path "atoms" obj)))
  | "editAtom" =>
      let obj ← exactObject path ["type", "atom", "before", "kind", "payload", "tombstone"] json
      pure (.editAtom ⟨← identifier (path ++ ".atom") (← field path "atom" obj),
        ← atomRecord (path ++ ".before") (← field path "before" obj),
        ← atomKind (path ++ ".kind") (← field path "kind" obj),
        ← decodeHex (path ++ ".payload") (← field path "payload" obj),
        ← bool (path ++ ".tombstone") (← field path "tombstone" obj)⟩)
  | "link" =>
      let obj ← exactObject path ["type", "link", "source", "target", "relation"] json
      pure (.link (← identifier (path ++ ".link") (← field path "link" obj))
        (← optional (path ++ ".source") stableRange (← field path "source" obj))
        (← linkTarget (path ++ ".target") (← field path "target" obj))
        ⟨← nat (path ++ ".relation") (← field path "relation" obj)⟩)
  | "annotate" =>
      let obj ← exactObject path ["type", "annotation", "atom", "revision", "body"] json
      pure (.annotate (← identifier (path ++ ".annotation") (← field path "annotation" obj))
        (← identifier (path ++ ".atom") (← field path "atom" obj))
        (← identifier (path ++ ".revision") (← field path "revision" obj))
        (← annotationBody (path ++ ".body") (← field path "body" obj)))
  | "rewrapAtom" =>
      let obj ← exactObject path ["type", "atom", "before", "wrapping"] json
      pure (.rewrapAtom (← identifier (path ++ ".atom") (← field path "atom" obj))
        (← atomRecord (path ++ ".before") (← field path "before" obj))
        (← decodeHex (path ++ ".wrapping") (← field path "wrapping" obj)))
  | "rewrapAnnotation" =>
      let obj ← exactObject path ["type", "annotation", "before", "wrapping"] json
      let annotation ← identifier (path ++ ".annotation") (← field path "annotation" obj)
      pure (.rewrapAnnotation annotation
        (← annotationBefore (path ++ ".before") annotation (← field path "before" obj))
        (← decodeHex (path ++ ".wrapping") (← field path "wrapping" obj)))
  | "unlink" =>
      let obj ← exactObject path ["type", "link"] json
      pure (.unlink (← identifier (path ++ ".link") (← field path "link" obj)))
  | "mark" =>
      let obj ← exactObject path ["type", "mark", "target", "revision", "kind"] json
      pure (.mark (← identifier (path ++ ".mark") (← field path "mark" obj))
        ⟨← markTarget (path ++ ".target") (← field path "target" obj),
          ← identifier (path ++ ".revision") (← field path "revision" obj),
          ← markSpec (path ++ ".kind") (← field path "kind" obj)⟩)
  | "unmark" =>
      let obj ← exactObject path ["type", "mark"] json
      pure (.unmark (← identifier (path ++ ".mark") (← field path "mark" obj)))
  | "insertRun" =>
      let obj ← exactObject path ["type", "run", "anchor", "atoms"] json
      pure (.insertRun (← identifier (path ++ ".run") (← field path "run" obj))
        (← optional (path ++ ".anchor") stablePoint (← field path "anchor" obj))
        (← list (path ++ ".atoms") identifier (← field path "atoms" obj)))
  | "transclude" =>
      let obj ← exactObject path ["type", "transclusion", "link", "request"] json
      pure (.transclude (← identifier (path ++ ".transclusion") (← field path "transclusion" obj))
        (← identifier (path ++ ".link") (← field path "link" obj))
        (← transcludeRequest (path ++ ".request") (← field path "request" obj)))
  | _ => failAt (path ++ ".type") "unknown content action"

def contentCommand (path : String) (json : Lean.Json) : Except String ContentResource.Command := do
  let obj ← exactObject path ["actions"] json
  pure ⟨← list (path ++ ".actions") contentAction (← field path "actions" obj)⟩

/-- A content payload read from its request object: `type` and `actions`, nothing else. -/
def contentOfJson (path : String) (json : Lean.Json) : Except String ContentResource.Command := do
  let obj ← exactObject path ["type", "actions"] json
  contentCommand path (.mkObj [("actions", ← field path "actions" obj)])

/-! ## What a reader is shown of a content command -/

/-- An atom's payload as a reader is shown it: its exact length, and the text when it is text. -/
def textPayloadJson (kind : Hyperdocument.AtomKind) (payload : List UInt8) : Lean.Json :=
  let base := [("exactBytes", decimal payload.length),
    ("trust", Lean.Json.str "untrusted source text or bytes")]
  match kind with
  | .text =>
      match String.fromUTF8? payload.toByteArray with
      | some value => Lean.Json.mkObj <| base ++
          [("encoding", .str "utf8"), ("text", .str value)]
      | none => Lean.Json.mkObj <| base ++
          [("encoding", .str "hex"), ("bytes", .str (encodeHex payload))]
  | .inlineObject schema => Lean.Json.mkObj <| base ++
      [("encoding", .str "hex"), ("schema", decimal schema.value),
       ("bytes", .str (encodeHex payload))]
  | .sealedObject schema fragment => Lean.Json.mkObj
      [("exactBytes", decimal (fragment.ciphertext.length + fragment.wrapping.length)),
       ("trust", .str "untrusted encrypted source bytes"), ("encoding", .str "sealed"),
       ("schema", decimal schema.value), ("ciphertext", .str (encodeHex fragment.ciphertext)),
       ("wrapping", .str (encodeHex fragment.wrapping))]

def contentActionJson (action : ContentResource.Action) : Lean.Json :=
  match action with
  | .createAtom atom kind payload => Lean.Json.mkObj
      [("type", .str "createAtom"), ("atom", decimal atom.digest.value),
       ("payload", textPayloadJson kind payload)]
  | .editAtom edit => Lean.Json.mkObj
      [("type", .str "editAtom"), ("atom", decimal edit.atomId.digest.value),
       ("before", textPayloadJson edit.before.kind edit.before.payload),
       ("replacement", textPayloadJson edit.kind edit.payload),
       ("tombstone", .bool edit.tombstone)]
  | other => Lean.Json.mkObj
      [("type", .str "otherContentAction"),
       ("exactActionHex", .str (encodeHex (ContentResource.actionStream.encode other)))]

/-- A content command's fields beside `type`, as a reader is shown them: the action count and
each action (an atom's text when it is text, any other action's exact bytes). This is the
reader's view, not the request grammar `contentOfJson` reads. -/
def contentToJson (command : ContentResource.Command) : List (String × Lean.Json) :=
  [("actionCount", decimal command.actions.length),
   ("actions", .arr (command.actions.toArray.map contentActionJson))]

/-- What a member is shown of a content command before signing: its size in canonical bytes. -/
def contentDisplay (command : ContentResource.Command) : List String :=
  [s!"content command ({(ContentResource.commandCodec.encode command).length} bytes)"]

end Minidregg.Kernel.ContentJson
