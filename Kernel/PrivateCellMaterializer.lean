/-
# Kernel.PrivateCellMaterializer -- the receiver's seam to the private materializer

The private root and its carried structure live below the registry, over any wire
(`Compiler.PrivateCellRoot`: `Kept`, `aux`, `keptRoot`, `rootAvailable`, `set_index`,
`materializer`). This module ties the receiver to them at a registry kind's tag (`kindTag`):
* `keptCell_root`: a kept cell's root is the structure's read at the kind-level context, by `rfl`;
* `keptCell_root_of_kind`: so it is the root the kind's materializer computes from its store
  bytes, with no premise about the cell (`kindCtx` is a function of the wire);
* `keptCell_holds`: a kept cell's index and mask are a carried structure of its store.
The hiding results (stated over `KeptCell.root`, `Serve` over `(ctx, mask, index)`) therefore
describe the root a private materializer computes.
-/
module

public import Kernel.PrivateCellReceiver
public import Theory.CellStateAux
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Kernel.PrivateCellMaterializer

set_option autoImplicit false

open Minidregg.Compiler
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.PrivateCellReceiver
open Minidregg.Compiler.PrivateCellIndex (indexEntries indexIgnoresBlinding)
open Minidregg.Compiler.PrivateCellRoot (kindCtx)
open Minidregg.Kernel.PrivateCellView (kindTag)

variable {kind : CanonicalCellRegistry.Kind} (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind))

/-- **The seam**: the receiver's kept root is this structure's read at the kind-level context,
so the hiding results (stated over `KeptCell.root`, `Serve` over `(ctx, mask, index)`) describe
the root the materializer computes. -/
theorem keptCell_root (cell : KeptCell wire) :
    cell.root = Compiler.PrivateCellRoot.keptRoot wire (kindTag kind) (kindCtx wire) ⟨cell.index, cell.mask⟩ :=
  rfl

/-- **Context uniformity**: every kept cell of a wire has the root the kind's materializer
computes from its store bytes at the kind-level context. `kindCtx` is a function of the wire
alone, so no parameter set can carry another context: this needs no premise about the cell. -/
theorem keptCell_root_of_kind
    (codec : Minidregg.Theory.IndexedProgram.LawfulCodec (Store (CanonicalCellRegistry.layout kind)))
    (rootBytes : List UInt8 → Digest) (agree : ∀ store, rootBytes (codec.encode store) = privateRoot wire (kindCtx wire) store)
    (cell : KeptCell wire) :
    cell.root = rootBytes (codec.encode cell.fit.store) := by
  rw [agree]
  exact cell.root_eq

/-- And a kept cell's carried structure holds of its store. -/
theorem keptCell_holds (cell : KeptCell wire) :
    Compiler.PrivateCellRoot.KeptHolds wire (kindTag kind) ⟨cell.index, cell.mask⟩ cell.fit.store :=
  ⟨cell.holds, cell.mask_eq.symm⟩

#assert_axioms keptCell_root
#assert_axioms keptCell_root_of_kind
#assert_axioms keptCell_holds

end Minidregg.Kernel.PrivateCellMaterializer
