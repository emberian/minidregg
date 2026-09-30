/-
# Kernel.DeployedMaterializerWitness -- event-log non-vacuity

The append-only Hyperdocument event log was the fourth deployed schema blocked
by the deleted total-function carrier.  This file completes the regression
closure with one actual materializer and its empty cell.  (The former pair of
"sparse" and "cell" materializers with an exact shared root is gone: the log
store is the cell state.)

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

instance eventLogNamespaceCountable :
    Countable HyperdocumentEventLog.Sparse.layout.Namespace :=
  inferInstanceAs (Countable HyperdocumentEventLog.Sparse.Namespace)

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

/-- The event log's existence materializer (countability-selected codec,
byte-length root).  There is one materializer: the log store is the cell. -/
noncomputable def eventLogCellMaterializer :
    CellState.Materializer HyperdocumentEventLog.Sparse.layout Digest :=
  Minidregg.Theory.DeployedMaterializerWitness.materializerOfCountable
    HyperdocumentEventLog.Sparse.layout

noncomputable def eventLogCell :
    CellState.Materialized eventLogCellMaterializer :=
  CellState.materialize eventLogCellMaterializer HyperdocumentEventLog.Sparse.empty

theorem eventLog_materializer_nonempty :
    Nonempty (CellState.Materializer HyperdocumentEventLog.Sparse.layout Digest) :=
  ⟨eventLogCellMaterializer⟩

@[simp] theorem eventLogCell_absent
    (address : HyperdocumentEventLog.Sparse.Address) :
    eventLogCell.logical address = none :=
  rfl

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.DeployedMaterializerWitness.eventLog_materializer_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eventLog_materializer_nonempty

end Minidregg.Kernel.DeployedMaterializerWitness
