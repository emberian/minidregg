/-
# Kernel.HyperdocumentEventLog -- separate append-only causal event cell

Final Hyperdocument version events do not live in the mutable document cell.
This module gives them one typed append-only namespace: the event-log cell is
a `Store` over `Sparse.layout`, materialized like every other cell.  Fresh
event insertion is accepted only through `Store.Op.allocate`; duplicate
insertion is therefore rejected before any receipt or history claim, and the
`appendOnly` discipline refuses every overwrite or removal of a recorded event
(`overwrite_refused`, `remove_refused`).

The pre/post roots inside `VersionEventRecord` are document/content roots.  The
event-log root is independently derived from this log store and is never copied
into the record it commits.  Atomic document+event publication is a
two-incidence `MultiCellHyperedge`; this module does not fake physical
atomicity.

There is one carrier.  The former adapter into a second `CellState.Schema`
(`cellSchema`, `toCellState`/`ofCellState`, and `Representation` inducing a
"sparse" and a "cell" materializer with the same bytes) is deleted: the log
store is the cell state, and a codec/root declaration is a
`CellState.Materializer Sparse.layout Root`.
-/
import Kernel.SparseAuthenticatedState
import Theory.Hyperdocument

namespace Minidregg.Kernel.HyperdocumentEventLog

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument

namespace Sparse

inductive Namespace where
  | events
  deriving DecidableEq, Repr

def layout : Store.Layout.{0, 0, 0} where
  Namespace := Namespace
  Key := fun _ => VersionEventId
  Value := fun _ => VersionEventRecord
  discipline := fun _ => .appendOnly

abbrev Store := Minidregg.Theory.Store.Store layout
abbrev Address := Minidregg.Theory.Store.Address layout
abbrev Op := Minidregg.Theory.Store.Op layout
abbrev Patch := Minidregg.Theory.Store.Patch layout

/-- The address of one event key. -/
def eventAddress (key : VersionEventId) : Address := ⟨.events, key⟩

def empty : Store := 0

def appendOp {scheme : CausalVersionDag.ContentAddressing}
    (event : StoredVersionEvent scheme) : Op :=
  .allocate .events event.key event.record

@[simp] theorem appendOp_address
    {scheme : CausalVersionDag.ContentAddressing}
    (event : StoredVersionEvent scheme) :
    (appendOp event).address = eventAddress event.key :=
  rfl

/-- Append-only validity is exactly typed sparse freshness. -/
theorem appendOp_enabled_iff
    {scheme : CausalVersionDag.ContentAddressing}
    (store : Store) (event : StoredVersionEvent scheme) :
    (appendOp event).Enabled store ↔ store (eventAddress event.key) = none := by
  simp only [appendOp, Minidregg.Theory.Store.Op.Enabled, layout,
    Minidregg.Theory.Store.Store.Fresh, eventAddress, ne_eq, reduceCtorEq,
    not_false_eq_true, true_and]
  exact Iff.rfl

/-- The log's discipline refuses every overwrite of a recorded event. -/
theorem overwrite_refused (store : Store) (key : VersionEventId)
    (before after : VersionEventRecord) :
    ¬ (Minidregg.Theory.Store.Op.write (L := layout) .events key before after).Enabled store := by
  simp [Minidregg.Theory.Store.Op.Enabled, layout]

/-- The log's discipline refuses every removal of a recorded event. -/
theorem remove_refused (store : Store) (key : VersionEventId)
    (before : VersionEventRecord) :
    ¬ (Minidregg.Theory.Store.Op.free (L := layout) .events key before).Enabled store := by
  simp [Minidregg.Theory.Store.Op.Enabled, layout]

abbrev Materializer (Root : Type) := CellState.Materializer layout Root
abbrev Cell {Root : Type} (materializer : Materializer Root) :=
  CellState.Materialized materializer

/-- One accepted append is the validated one-operation patch at the cell's
own root. -/
abbrev AcceptedAppend
    {Root : Type} {scheme : CausalVersionDag.ContentAddressing}
    (materializer : Materializer Root) (pre : Cell materializer)
    (event : StoredVersionEvent scheme) : Prop :=
  CellState.ValidatedPatch materializer pre pre.root [appendOp event]

theorem accept
    {Root : Type} [DecidableEq Root] {scheme : CausalVersionDag.ContentAddressing}
    {materializer : Materializer Root} {pre : Cell materializer}
    (event : StoredVersionEvent scheme)
    (fresh : pre.logical (eventAddress event.key) = none) :
    AcceptedAppend materializer pre event := by
  obtain ⟨validated, _⟩ := CellState.validate_accepts materializer pre pre.root
    [appendOp event] rfl ⟨(appendOp_enabled_iff pre.logical event).2 fresh, trivial⟩
  exact validated

theorem AcceptedAppend.pre_fresh
    {Root : Type} {scheme : CausalVersionDag.ContentAddressing}
    {materializer : Materializer Root} {pre : Cell materializer}
    {event : StoredVersionEvent scheme}
    (accepted : AcceptedAppend materializer pre event) :
    pre.logical (eventAddress event.key) = none :=
  (appendOp_enabled_iff pre.logical event).1 accepted.valid.1

/-- The accepted post contains the exact addressed event record. -/
@[simp] theorem AcceptedAppend.post_contains
    {Root : Type} {scheme : CausalVersionDag.ContentAddressing}
    {materializer : Materializer Root} {pre : Cell materializer}
    {event : StoredVersionEvent scheme}
    (accepted : AcceptedAppend materializer pre event) :
    accepted.apply.logical (eventAddress event.key) = some event.record := by
  simp [CellState.ValidatedPatch.apply_logical, appendOp, eventAddress,
    Minidregg.Theory.Store.Op.apply]
  rfl

/-- Allocation has teeth: the exact same event key cannot be appended again to
the accepted post, independently of any digest-binding assumption. -/
theorem AcceptedAppend.duplicate_rejected
    {Root : Type} {scheme : CausalVersionDag.ContentAddressing}
    {materializer : Materializer Root} {pre : Cell materializer}
    {event : StoredVersionEvent scheme}
    (accepted : AcceptedAppend materializer pre event) :
    ¬ (appendOp event).Enabled accepted.apply.logical := by
  intro enabled
  have fresh := (appendOp_enabled_iff accepted.apply.logical event).1 enabled
  rw [accepted.post_contains] at fresh
  contradiction

/-- The lookup bus exposes one literal allocation row, not a host-authored
"append succeeded" flag. -/
theorem AcceptedAppend.bus_relation
    {Root : Type} {scheme : CausalVersionDag.ContentAddressing}
    {materializer : Materializer Root} {pre : Cell materializer}
    {event : StoredVersionEvent scheme}
    (accepted : AcceptedAppend materializer pre event) :
    Minidregg.Kernel.SparseAuthenticatedState.Trace.BusRelation
      0 pre.logical [appendOp event]
      (Minidregg.Kernel.SparseAuthenticatedState.Trace.busRows
        pre.logical [appendOp event]) accepted.apply.logical :=
  (Minidregg.Kernel.SparseAuthenticatedState.ExactBusClaim.ofValidated accepted).rows_semantic

end Sparse

/-- info: 'Minidregg.Kernel.HyperdocumentEventLog.Sparse.AcceptedAppend.post_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Sparse.AcceptedAppend.post_contains
/-- info: 'Minidregg.Kernel.HyperdocumentEventLog.Sparse.AcceptedAppend.duplicate_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Sparse.AcceptedAppend.duplicate_rejected
/-- info: 'Minidregg.Kernel.HyperdocumentEventLog.Sparse.overwrite_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Sparse.overwrite_refused
/-- info: 'Minidregg.Kernel.HyperdocumentEventLog.Sparse.remove_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Sparse.remove_refused

end Minidregg.Kernel.HyperdocumentEventLog
