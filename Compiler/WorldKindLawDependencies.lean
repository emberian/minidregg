/- Mandatory structural law roots, derived from authenticated target bytes.
Current exports are resolved by the shared law resolver. This module supplies
neither a predicate evaluator nor caller-selected parents.
-/
import Compiler.CanonicalCellRegistry
import Pred.LawComposition

namespace Minidregg.Compiler.WorldKindLawDependencies

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.LawComposition

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry

/-- Source-owned selector coordinates for an existing target. Admission must
also require `loadTarget` success; absence never authorizes an empty projection.
These slots precede extensible payload projections so they cannot be shadowed. -/
def targetSelectorSlots (directory : Directory Nat Registry) (target : Nat) :
    List (String × Int) :=
  match directory.slots target with
  | .present cell => [("target/storageKind", Int.ofNat cell.kind.tag.toNat),
      ("world/request/birth", 0)]
  | .absent => []

structure Dependencies where
  additional : List PolicyRef
  readGuards : List (Nat × Digest)

private def ofCell (deployment : CanonicalCellRegistry.Deployment)
    (directory : Directory Nat Registry) (cell : PackedCell Registry) : Option Dependencies :=
  match cell with
  | ⟨.worldInstance, payload⟩ => do
      let binding ← payload.logical WorldKindCell.descriptorAddress
      if !decide (WorldKindCell.instanceLaw payload.logical) then none else do
        let kindId := binding.descriptor.kind
        match directory.slots kindId with
        | .present source@⟨.worldKind, definition⟩ =>
            if CanonicalCellRegistry.CellLaw deployment kindId source then
              -- Read the current definition for existence/identity; do not
              -- require its current revision to equal an older instance's.
              let _ ← definition.logical WorldKindCell.definitionAddress
              some ⟨[⟨⟨kindId⟩, .descendants, .head⟩],
                [(kindId, ResourceBirthCodec.physicalRoot (.live source))]⟩
            else none
        | _ => none
  | _ => some ⟨[], []⟩

/-- Reads and ordinary edits load the descriptor from the actual current
target. Its guard remains even when the composed policy itself only reads the
kind's export. A surrounding write leg may discharge the same guard. -/
def loadTarget (deployment : CanonicalCellRegistry.Deployment)
    (directory : Directory Nat Registry) (target : Nat) : Option Dependencies := do
  match directory.slots target with
  | .present cell =>
      if CanonicalCellRegistry.CellLaw deployment target cell then
        let dependencies ← ofCell deployment directory cell
        some { dependencies with readGuards :=
          (target, ResourceBirthCodec.physicalRoot (.live cell)) :: dependencies.readGuards }
      else none
  | _ => none

/-- A recipient observes the exact admitted post, but structural dependency
selection cannot change with a payload edit. The receiving source supplies
the actual old-cell and preserved-binding proofs from that transaction. -/
def loadPost (deployment : CanonicalCellRegistry.Deployment)
    (directory : Directory Nat Registry) (target : Nat)
    (old next : PackedCell Registry)
    (_present : directory.slots target = .present old)
    (_bindingPreserved : CanonicalCellRegistry.instanceBinding old =
      CanonicalCellRegistry.instanceBinding next) : Option Dependencies :=
  if CanonicalCellRegistry.CellLaw deployment target next then
    loadTarget deployment directory target
  else none

/-- Newborn targets are absent from the old directory. Their source-prepared,
signed birth item selects the kind, whose current identity/root/ROM defaults
are checked before current exported restrictions evaluate the birth effect. -/
def loadBirth (deployment : CanonicalCellRegistry.Deployment)
    (directory : Directory Nat Registry) (item : ResourceBirth.BirthItem Registry) :
    Option Dependencies :=
  if CanonicalCellRegistry.CellLaw deployment item.create.cellId item.create.cell ∧
      CanonicalCellRegistry.kindBirthValid deployment directory item.create.cell = true then
    ofCell deployment directory item.create.cell
  else none

end Minidregg.Compiler.WorldKindLawDependencies
