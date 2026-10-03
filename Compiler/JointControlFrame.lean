/- Source control is a schema-pinned atom in a real native content ResourceCell.
The payload codec never replaces its physical lifecycle/kind/policy metadata.
Changes are admitted by the actual content receiver, using editAtom with its
exact current AtomRecord. This module does not manufacture a raw DataWrite. -/
import Kernel.JointControlCell
import Compiler.CanonicalCellRegistry
import Kernel.ContentResource
namespace Minidregg.Compiler.JointControlFrame
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.JointControlCell
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
    (fun p => (p.cell,p.atom,p.schema,p.owner)) (fun (c,a,s,o) => ⟨c,a,s,o⟩) (by intro p; cases p; rfl)

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

def readControl (pin : Pin) (bytes : List UInt8) : Option Control := do
  let actual ← atom pin bytes
  JointControlCell.decode actual.payload

/-- The source-authored content method has one guarded semantic edit. Its whole
physical post is later checked against this decoded control transition. -/
def edit (pin : Pin) (bytes : List UInt8) (next : Control) : Option Kernel.ContentResource.Command := do
  let before ← atom pin bytes
  pure ⟨[.editAtom ⟨pin.atom,before,.inlineObject pin.schema,controlStream.encode next,false⟩]⟩

/-- Kernel-owned continuation of the admitted promise. This edits the same
schema-pinned atom while preserving all other content/lifecycle metadata. The
operation is never accepted as a client-provided physical post. -/
def replace (pin : Pin) (bytes : List UInt8) (operation : OperationId)
    (next : Control) : Option (List UInt8) := do
  let .live packed ← ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry |>.decode bytes
    | none
  match packed with
  | ⟨.content, content⟩ => do
      let before ← atom pin bytes
      let after := editAtomRecord operation
        ⟨pin.atom,before,.inlineObject pin.schema,controlStream.encode next,false⟩
      let post := content.logical.set ⟨.atoms,pin.atom⟩ (some after)
      pure <| ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry |>.encode
        (.live ⟨.content,CellState.materialize HyperdocumentCell.contentMaterializer post⟩)
  | _ => none

/-- Reject unknown/retired lifecycle envelopes, wrong resource kinds, wrong
schema/document/atom identity, tombstones and noncanonical control payloads. -/
def ordinaryGate {rootBytes : List UInt8 → Digest} (domain : Digest) (pin : Pin)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    Except JointControlCell.Reject Unit :=
  JointControlCell.ordinaryGate (readControl pin) domain pin.cell snapshot intent
end Minidregg.Compiler.JointControlFrame
