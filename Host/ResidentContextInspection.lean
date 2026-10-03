/- Context-document inspection derives selection/dependencies from the actual
native resource-view frame. It does not fetch sources, verify a transport
signature, grant reads, or certify external summaries. The participant client
first obtains/adopts its current signed resource read. -/
import Kernel.ResidentContextProjection
import Kernel.NativeObservationController
import Host.LegacyContentView
import Lean.Data.Json
namespace Minidregg.Host.ResidentContextInspection
open Lean
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.CellRegistry
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.ResidentContextProjection
set_option autoImplicit false
abbrev Result := Except String
private def decimal (n : Nat) : Json := .str (toString n)
private def optDecimal (n : Option Nat) : Json := (n.map decimal).getD .null
private def digits := "0123456789abcdef".toList
private def hex (bytes : List UInt8) : Json := .str <| String.ofList <|
  bytes.flatMap fun byte => [digits[byte.toNat / 16]?.getD '0', digits[byte.toNat % 16]?.getD '0']
private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none
private def unhex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexDigit a
    let lo ← hexDigit b
    let tail ← unhex rest
    pure (UInt8.ofNat (hi * 16 + lo) :: tail)
  | [_] => none
private def field (json : Json) (name : String) : Result Json :=
  json.getObjVal? name
private def string (json : Json) (name : String) : Result String := do
  (← field json name).getStr?
private def natural (json : Json) (name : String) : Result Nat := do
  let s ← string json name
  let some n := s.toNat? | throw s!"{name}: expected canonical decimal"
  unless toString n = s do throw s!"{name}: expected canonical decimal"
  pure n
private def input (bytes : List UInt8) : Result Json := do
  let some text := String.fromUTF8? (ByteArray.mk bytes.toArray) | throw "context input is not UTF-8"
  Json.parse text
private def documentOf? (store : ContentResource.ContentStore) : Option DocumentId :=
  ((StoreCodec.entries HyperdocumentCell.contentWire store).findSome? fun entry =>
    match entry with
    | ⟨⟨.documents, identifier⟩, _⟩ => some identifier
    | _ => none).orElse fun _ => LegacyContentView.documentOf? store
private def rowJson (row : Row) : Json :=
  .mkObj [("source", decimal row.dependency.source.source),
    ("sourceRoot", decimal row.dependency.source.root.value),
    ("element", decimal row.dependency.element), ("revision", decimal row.dependency.revision),
    ("parent", optDecimal row.dependency.parent), ("predecessor", optDecimal row.dependency.predecessor),
    ("payloadDigest", decimal row.dependency.payload.value), ("payload", hex row.bytes)]
/-- One bounded selection from a CURRENT resource view. Historical frames
deliberately fail this receiving boundary; history remains separately available. -/
def document (bytes : List UInt8) : Result Json := do
  let json ← input bytes
  let fields ← json.getObj?
  unless fields.size = 4 do throw "context input requires target, view, maxRows, maxBytes"
  let source ← natural json "target"
  let maxRows ← natural json "maxRows"
  let maxBytes ← natural json "maxBytes"
  unless maxRows > 0 ∧ maxRows ≤ 256 ∧ maxBytes > 0 ∧ maxBytes ≤ 65536 do
    throw "context bounds require rows1..256 and bytes1..65536"
  let some view := unhex (← string json "view").toList | throw "context view is not lowercase hex"
  let some value := NativeObservationController.resourceViewCodec.decode view
    | throw "context selection requires current canonical native resource view"
  let some ⟨.content, payload⟩ :=
      PackedCell.decode CanonicalCellRegistry.registry value.2.1
    | throw "context selection requires a content resource"
  let store := payload.logical
  let some document := documentOf? store | throw "context source has no document"
  let pin : SourcePin := ⟨source, value.1⟩
  let rows := documentRows pin store document []
  let projection := project maxRows maxBytes rows
  let unsupported := (DocumentHistory.lines store document []).filter fun row =>
    match row.2 with
    | .embed _ _ | .runs | .opaque | .missing => true
    | .atom _ none _ => true
    | _ => false
  pure <| .mkObj [("type", "mini-context-document-v1"),
    ("source", decimal source), ("sourceRoot", decimal value.1.value),
    ("document", decimal document.digest.value),
    ("maxRows", decimal maxRows), ("maxBytes", decimal maxBytes),
    ("sourceRows", decimal projection.sourceRows), ("unsupportedRows", decimal unsupported.length), ("omittedRows", decimal projection.omittedRows),
    ("selectedBytes", decimal (byteCount projection.rows)),
    ("rows", .arr (projection.rows.toArray.map rowJson)),
    ("support", .arr #[.mkObj [("source", decimal source), ("root", decimal value.1.value)]]),
    ("authority", "participant-current-signed-read-required")]

private def pin (json : Json) : Result SourcePin := do
  let fields ← json.getObj?
  unless fields.size = 2 do throw "support pin requires source and root"
  pure ⟨← natural json "source", ⟨← natural json "root"⟩⟩
private def pins (json : Json) (name : String) : Result (List SourcePin) := do
  let values ← (← field json name).getArr?
  unless values.size ≤ 16 do throw "context support exceeds16 sources"
  values.toList.mapM pin
/-- Summary/proposal support is exact source identity and current source root.
The caller supplies roots from current participant-admitted observations. -/
def support (bytes : List UInt8) : Result Json := do
  let json ← input bytes
  let fields ← json.getObj?
  unless fields.size = 2 do throw "support input requires dependencies and current"
  let dependencies ← pins json "dependencies"
  let current ← pins json "current"
  let fresh := supported dependencies current
  pure <| .mkObj [("type", "mini-context-support-v1"), ("current", .bool fresh),
    ("status", if fresh then "current" else "invalidated")]

end Minidregg.Host.ResidentContextInspection
