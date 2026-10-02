/- Read-only views of explicit legacy content carried into the current store.
Callers first obtain an authorized current content view. References remain
legacy atom references; they never become fabricated range-history openings. -/
import Compiler.LegacyContentCarry
import Kernel.DocumentHistory
import Lean

namespace Minidregg.Host.LegacyContentView
open Lean
open Minidregg.Theory
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Theory.Hyperdocument
set_option autoImplicit false

private def decimal (value : Nat) : Json := toJson (toString value)
private def hex (bytes : List UInt8) : Json :=
  let digit := fun n : Nat => Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)
  .str (String.ofList (bytes.flatMap fun byte => [digit (byte.toNat / 16), digit (byte.toNat % 16)]))

def referenceJson (reference : LegacyContentCarry.Legacy.EmbedRef) : Json :=
  Json.mkObj [("document", decimal reference.document.digest.value),
    ("atom", decimal reference.atom.digest.value), ("revision", decimal reference.revision.digest.value),
    ("mode", .str (match reference.mode with | .snapshot => "snapshot" | .live => "live"))]

def referenceFields (reference : StoredTransclusionRef) : List (String × Json) :=
  match LegacyContentCarry.inspectReference reference with
  | none => []
  | some legacy => [("legacyReference", referenceJson legacy)]

def markFields (rangeJson : StableRange → Json) (record : AnnotationRecord) : List (String × Json) :=
  match LegacyContentCarry.inspectMark record with
  | none => []
  | some (identifier, mark) => [("legacyMark", Json.mkObj [
      ("id", decimal identifier.digest.value), ("kindDigest", decimal mark.kind.value),
      ("payload", hex mark.payload), ("range", rangeJson mark.range),
      ("visibilityPolicy", decimal mark.visibilityPolicy.value),
      ("tombstoned", .bool mark.tombstonedAt.isSome)])]

/-- Finds a renderable carried page without installing document ownership. -/
def documentOf? (store : ContentResource.ContentStore) : Option DocumentId :=
  (StoreCodec.entries HyperdocumentCell.contentWire store).findSome? fun entry =>
    match entry with
    | ⟨⟨.fields, key⟩, _⟩ =>
      match key.owner with
      | .document document =>
        if (LegacyContentCarry.carriedDocument store document).isSome then some document else none
      | _ => none
    | _ => none

def rootOf? (store : ContentResource.ContentStore) (document : DocumentId) : Option ElementId :=
  (ContentResource.rootOf store document).orElse fun _ =>
    (LegacyContentCarry.carriedDocument store document).map (·.root)

def lines (store : ContentResource.ContentStore) (document : DocumentId)
    (marks : List (MarkId × MarkRecord)) : List (ElementId × DocumentHistory.Line) :=
  (LegacyContentCarry.documentOrder store document).map fun element =>
    (element, DocumentHistory.lineOf store marks element)

/-- Only a supplied, current-authorized source page can yield bytes. A legacy
snapshot whose atom revision moved remains a visible unresolved historical
reference; a current page is never substituted for that historical revision. -/
def renderReference (source : Option ContentResource.ContentStore)
    (reference : LegacyContentCarry.Legacy.EmbedRef) : Json :=
  let empty := fun name => Json.mkObj [("view", .str name)]
  match source with
  | none => empty "unavailable"
  | some store =>
    match store ⟨.atoms, reference.atom⟩ with
    | none => empty "unavailable"
    | some atom =>
      if atom.document != reference.document || atom.tombstonedAt.isSome then empty "invalidated"
      else match reference.mode with
      | .snapshot =>
          if atom.revision != reference.revision then empty "moved"
          else Json.mkObj [("view", .str "snapshot"), ("lines", .arr #[hex atom.bodyBytes])]
      | .live => Json.mkObj [("view", .str "live"), ("lines", .arr #[hex atom.bodyBytes]),
          ("revised", .bool (atom.revision != reference.revision))]

end Minidregg.Host.LegacyContentView
