/- Shared framing for source-owned controller payloads in actual content cells.
Payload interpretation is separate from native lifecycle/kind/schema framing.
No raw physical post is admitted merely because this helper can construct it.
-/
import Compiler.CanonicalCellRegistry
import Kernel.DurableDataIntent
import Kernel.ContentResource

namespace Minidregg.Compiler.ContentControlFrame
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

structure Pin where
  cell : CellId
  atom : AtomId
  schema : Digest
  owner : SubjectId
  deriving DecidableEq

def pinStream : StreamCodec Pin :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product (HyperdocumentCodec.identifierStream .v1 .atom)
      (StreamCodec.product digestStream TypedAuthorizationRequestCodec.subjectIdStream)))
    (fun pin => (pin.cell, pin.atom, pin.schema, pin.owner))
    (fun (cell, atom, schema, owner) => ⟨cell, atom, schema, owner⟩)
    (by intro pin; cases pin; rfl)

def atom (pin : Pin) (bytes : List UInt8) : Option AtomRecord := do
  let .live packed ← ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry |>.decode bytes
    | none
  match packed with
  | ⟨.content, content⟩ => do
      let actual ← Hyperdocument.lookup content.logical .atoms pin.atom
      if actual.document != Kernel.ContentResource.documentOf pin.cell.value ||
          actual.kind != .inlineObject pin.schema || actual.tombstonedAt.isSome then none
      else some actual
  | _ => none

def readPayload (pin : Pin) (bytes : List UInt8) : Option (List UInt8) :=
  (atom pin bytes).map AtomRecord.payload

/-- A normal content edit keeps its expected exact pre-atom. The actual native
receiver still checks owner/current authority, content laws, funding and bounds. -/
def editPayload (pin : Pin) (bytes payload : List UInt8) :
    Option Kernel.ContentResource.Command := do
  let before ← atom pin bytes
  pure ⟨[.editAtom ⟨pin.atom, before, .inlineObject pin.schema, payload, false⟩]⟩

def replacePayload (pin : Pin) (bytes : List UInt8) (operation : OperationId)
    (payload : List UInt8) : Option (List UInt8) := do
  let .live packed ← ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry |>.decode bytes
    | none
  match packed with
  | ⟨.content, content⟩ => do
      let before ← atom pin bytes
      let after := editAtomRecord operation
        ⟨pin.atom, before, .inlineObject pin.schema, payload, false⟩
      let post := content.logical.set ⟨.atoms, pin.atom⟩ (some after)
      pure <| ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry |>.encode
        (.live ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer post⟩)
  | _ => none

@[simp] theorem pin_roundtrip (pin : Pin) :
    pinStream.toLawful.decode (pinStream.encode pin) = some pin :=
  pinStream.toLawful.decode_encode pin

#assert_axioms pin_roundtrip
end Minidregg.Compiler.ContentControlFrame
