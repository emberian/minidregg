/-
# Kernel.HyperdocumentEventLog -- separate append-only causal event cell

Final Hyperdocument version events do not live in the mutable document cell.
This module gives them one typed append-only sparse namespace and derives a
canonical `CellState` representation from the very same store.  Fresh event
insertion is accepted only through `SparseAuthenticatedState.Op.allocate`;
duplicate insertion is therefore rejected before any receipt or history claim.

The pre/post roots inside `VersionEventRecord` are document/content roots.  The
event-log root is independently derived from this log store and is never copied
into the record it commits.  Atomic document+event publication is a later
two-incidence `MultiCellHyperedge`; this module does not fake physical atomicity.
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

def layout : Minidregg.Kernel.SparseAuthenticatedState.Layout where
  Namespace := Namespace
  Key := fun _ => VersionEventId
  Value := fun _ => VersionEventRecord
  discipline := fun _ => .appendOnly

instance : DecidableEq layout.Namespace := by
  change DecidableEq Namespace
  infer_instance

instance (space : layout.Namespace) : DecidableEq (layout.Key space) := by
  cases space
  change DecidableEq VersionEventId
  infer_instance

abbrev Store := Minidregg.Kernel.SparseAuthenticatedState.Store layout
abbrev Address := Minidregg.Kernel.SparseAuthenticatedState.Address layout

def empty : Store := fun _ _ => none

def appendOp {scheme : CausalVersionDag.ContentAddressing}
    (event : StoredVersionEvent scheme) :
    Minidregg.Kernel.SparseAuthenticatedState.Op layout :=
  .allocate .events event.key event.record

@[simp] theorem appendOp_address
    {scheme : CausalVersionDag.ContentAddressing}
    (event : StoredVersionEvent scheme) :
    (appendOp event).address = (⟨.events, event.key⟩ : Address) :=
  rfl

/-- Append-only validity is exactly typed sparse freshness. -/
theorem appendOp_enabled_iff
    {scheme : CausalVersionDag.ContentAddressing}
    (store : Store) (event : StoredVersionEvent scheme) :
    (appendOp event).Enabled store ↔ store .events event.key = none := by
  simp [appendOp, Minidregg.Kernel.SparseAuthenticatedState.Op.Enabled,
    layout, Minidregg.Kernel.SparseAuthenticatedState.Fresh]

abbrev Materializer (Root : Type) :=
  Minidregg.Kernel.SparseAuthenticatedState.Materializer layout Root
abbrev Cell {Root : Type} (materializer : Materializer Root) :=
  Minidregg.Kernel.SparseAuthenticatedState.Materialized materializer

/-- One accepted append is the existing prefix-valid sparse execution. -/
abbrev AcceptedAppend
    {Root : Type} {scheme : CausalVersionDag.ContentAddressing}
    (materializer : Materializer Root) (pre : Cell materializer)
    (event : StoredVersionEvent scheme) :=
  Minidregg.Kernel.SparseAuthenticatedState.AcceptedExecution
    materializer pre [appendOp event]

def accept
    {Root : Type} {scheme : CausalVersionDag.ContentAddressing}
    {materializer : Materializer Root} {pre : Cell materializer}
    (event : StoredVersionEvent scheme)
    (fresh : pre.logical .events event.key = none) :
    AcceptedAppend materializer pre event where
  valid := by
    constructor
    · exact (appendOp_enabled_iff pre.logical event).2 fresh
    · trivial

theorem AcceptedAppend.pre_fresh
    {Root : Type} {scheme : CausalVersionDag.ContentAddressing}
    {materializer : Materializer Root} {pre : Cell materializer}
    {event : StoredVersionEvent scheme}
    (accepted : AcceptedAppend materializer pre event) :
    pre.logical .events event.key = none :=
  (appendOp_enabled_iff pre.logical event).1 accepted.valid.1

/-- The accepted sparse post contains the exact addressed event record. -/
@[simp] theorem AcceptedAppend.post_contains
    {Root : Type} {scheme : CausalVersionDag.ContentAddressing}
    {materializer : Materializer Root} {pre : Cell materializer}
    {event : StoredVersionEvent scheme}
    (accepted : AcceptedAppend materializer pre event) :
    accepted.post.logical .events event.key = some event.record := by
  simp [Minidregg.Kernel.SparseAuthenticatedState.AcceptedExecution.post,
    Minidregg.Kernel.SparseAuthenticatedState.materialize,
    Minidregg.Kernel.SparseAuthenticatedState.Trace.run, appendOp,
    Minidregg.Kernel.SparseAuthenticatedState.Op.apply,
    Minidregg.Kernel.SparseAuthenticatedState.Store.set]
  rfl

/-- Allocation has teeth: the exact same event key cannot be appended again to
the accepted post, independently of any digest-binding assumption. -/
theorem AcceptedAppend.duplicate_rejected
    {Root : Type} {scheme : CausalVersionDag.ContentAddressing}
    {materializer : Materializer Root} {pre : Cell materializer}
    {event : StoredVersionEvent scheme}
    (accepted : AcceptedAppend materializer pre event) :
    ¬ (appendOp event).Enabled accepted.post.logical := by
  rw [appendOp_enabled_iff]
  simp [accepted.post_contains]

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
        pre.logical [appendOp event]) accepted.post.logical :=
  accepted.exactBusClaim.rows_semantic

end Sparse

/-! ## Exact adapter into the canonical cell machine -/

/-- The cell schema is derived from the sparse layout's dependent address and
optional value.  It is not a second event-log state model. -/
def cellSchema : CellState.Schema where
  Field := Sparse.Address
  FieldType := fun address => Option (Sparse.layout.Value address.1)
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance : DecidableEq cellSchema.Field := by
  change DecidableEq Sparse.Address
  infer_instance

instance : DecidableEq cellSchema.Resource := by
  change DecidableEq Empty
  infer_instance

def Sparse.Store.toCellState (store : Sparse.Store) :
    CellState.LogicalState cellSchema where
  fields := fun address => store address.1 address.2
  resources := fun resource => nomatch resource

def Sparse.Store.ofCellState (state : CellState.LogicalState cellSchema) :
    Sparse.Store :=
  fun space key => state.fields ⟨space, key⟩

@[simp] theorem Sparse.Store.ofCellState_toCellState (store : Sparse.Store) :
    Sparse.Store.ofCellState store.toCellState = store := by
  funext space key
  rfl

@[simp] theorem Sparse.Store.toCellState_ofCellState
    (state : CellState.LogicalState cellSchema) :
    (Sparse.Store.ofCellState state).toCellState = state := by
  cases state with
  | mk fields resources =>
      have resourcesUnique : resources = fun resource => nomatch resource := by
        funext resource
        exact Empty.elim resource
      subst resources
      rfl

/-- One codec/root declaration induces both sparse and cell materializers. -/
structure Representation (Root : Type) where
  sparseCodec : LawfulCodec Sparse.Store
  rootBytes : List UInt8 -> Root

def Representation.cellCodec {Root : Type} (representation : Representation Root) :
    LawfulCodec (CellState.LogicalState cellSchema) where
  encode := fun state =>
    representation.sparseCodec.encode (Sparse.Store.ofCellState state)
  decode := fun bytes =>
    (representation.sparseCodec.decode bytes).map Sparse.Store.toCellState
  decode_encode := by
    intro state
    rw [representation.sparseCodec.decode_encode]
    simp

def Representation.sparseMaterializer {Root : Type}
    (representation : Representation Root) : Sparse.Materializer Root where
  codec := representation.sparseCodec
  rootBytes := representation.rootBytes

def Representation.cellMaterializer {Root : Type}
    (representation : Representation Root) :
    CellState.Materializer cellSchema Root where
  codec := representation.cellCodec
  rootBytes := representation.rootBytes

/-- The two views have definitionally the same canonical bytes. -/
@[simp] theorem Representation.bytes_exact
    {Root : Type} (representation : Representation Root)
    (store : Sparse.Store) :
    (representation.cellCodec.encode store.toCellState) =
      representation.sparseCodec.encode store := by
  simp [Representation.cellCodec]

/-- Therefore their derived roots are exact, with no collision-resistance
claim and no representation-refinement premise. -/
@[simp] theorem Representation.roots_exact
    {Root : Type} (representation : Representation Root)
    (store : Sparse.Store) :
    (CellState.materialize representation.cellMaterializer
      store.toCellState).root =
    (Minidregg.Kernel.SparseAuthenticatedState.materialize
      representation.sparseMaterializer store).root := by
  rfl

#print axioms Sparse.AcceptedAppend.post_contains
#print axioms Sparse.AcceptedAppend.duplicate_rejected
#print axioms Sparse.Store.ofCellState_toCellState
#print axioms Representation.roots_exact

end Minidregg.Kernel.HyperdocumentEventLog
