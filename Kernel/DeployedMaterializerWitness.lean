/-
# Kernel.DeployedMaterializerWitness -- event-log non-vacuity

The append-only Hyperdocument event log was the fourth deployed schema blocked
by the deleted total-function carrier.  This file completes the regression
closure with one actual sparse representation, one canonical cell materializer,
and their exact shared empty root.

As in the Theory-side witness, the countability-selected codec and byte-length
root are existence witnesses, not deployment pins or cryptographic claims.
-/
import Kernel.HyperdocumentEventLog
import Theory.DeployedMaterializerWitness

namespace Minidregg.Kernel.DeployedMaterializerWitness

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.HyperdocumentEventLog

set_option autoImplicit false

deriving instance Countable for HyperdocumentEventLog.Sparse.Namespace

instance eventLogKeyCountable
    (space : HyperdocumentEventLog.Sparse.layout.Namespace) :
    Countable (HyperdocumentEventLog.Sparse.layout.Key space) := by
  cases space
  simp only [HyperdocumentEventLog.Sparse.layout]
  infer_instance

instance eventLogValueCountable
    (space : HyperdocumentEventLog.Sparse.layout.Namespace) :
    Countable (HyperdocumentEventLog.Sparse.layout.Value space) := by
  cases space
  simp only [HyperdocumentEventLog.Sparse.layout]
  infer_instance

def eventLogAddressCode :
    HyperdocumentEventLog.Sparse.Address → Hyperdocument.VersionEventId
  | ⟨.events, key⟩ => key

theorem eventLogAddressCode_injective :
    Function.Injective eventLogAddressCode := by
  rintro ⟨space, key⟩ ⟨space', key'⟩ same
  cases space
  cases space'
  simp only [eventLogAddressCode] at same
  cases same
  rfl

instance : Countable HyperdocumentEventLog.Sparse.Address :=
  Function.Injective.countable eventLogAddressCode_injective

instance : Countable HyperdocumentEventLog.Sparse.Store :=
  Function.Injective.countable
    (f := fun store : HyperdocumentEventLog.Sparse.Store => store.entries)
    (by
      intro left right same
      cases left
      cases right
      cases same
      rfl)

noncomputable def eventLogCodec :
    LawfulCodec HyperdocumentEventLog.Sparse.Store :=
  Minidregg.Theory.DeployedMaterializerWitness.codecOfCountable
    HyperdocumentEventLog.Sparse.Store

noncomputable def eventLogRepresentation :
    HyperdocumentEventLog.Representation Digest where
  sparseCodec := eventLogCodec
  rootBytes := Minidregg.Theory.DeployedMaterializerWitness.lengthRoot

noncomputable def eventLogSparseMaterializer :
    HyperdocumentEventLog.Sparse.Materializer Digest :=
  eventLogRepresentation.sparseMaterializer

noncomputable def eventLogCellMaterializer :
    CellState.Materializer HyperdocumentEventLog.cellSchema Digest :=
  eventLogRepresentation.cellMaterializer

noncomputable def eventLogSparseCell :
    HyperdocumentEventLog.Sparse.Cell eventLogSparseMaterializer :=
  Minidregg.Kernel.SparseAuthenticatedState.materialize
    eventLogSparseMaterializer HyperdocumentEventLog.Sparse.empty

noncomputable def eventLogCell :
    CellState.Materialized eventLogCellMaterializer :=
  CellState.materialize eventLogCellMaterializer
    HyperdocumentEventLog.Sparse.empty.toCellState

theorem eventLog_materializer_nonempty :
    Nonempty
      (CellState.Materializer HyperdocumentEventLog.cellSchema Digest) :=
  ⟨eventLogCellMaterializer⟩

@[simp] theorem eventLogCell_absent
    (address : HyperdocumentEventLog.Sparse.Address) :
    eventLogCell.logical.fields address = none :=
  rfl

@[simp] theorem eventLog_empty_roots_exact :
    eventLogCell.root = eventLogSparseCell.root :=
  HyperdocumentEventLog.Representation.roots_exact
    eventLogRepresentation HyperdocumentEventLog.Sparse.empty

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.DeployedMaterializerWitness.eventLog_materializer_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eventLog_materializer_nonempty
/-- info: 'Minidregg.Kernel.DeployedMaterializerWitness.eventLog_empty_roots_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eventLog_empty_roots_exact

end Minidregg.Kernel.DeployedMaterializerWitness
