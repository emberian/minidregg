/-
# Kernel.SparseAuthenticatedState -- the timestamped bus projection of a patch

The typed sparse store, its guarded operations, patches, prefix validity,
footprints and frame law now live in `Theory.Store`; canonical materialization
and validated patches live in `Theory.CellState`.  This module keeps the one
thing that is its own: the lowering seam.  A validated patch derives one
timestamped bus row per operation, threading the exact prefix stores, and
`ExactBusClaim` binds those rows to the canonical pre- and post-roots.

The bus boundary is only a semantic equality.  It does not claim a
LogUp/Twist argument, a polynomial-commitment opening, collision resistance,
or a Rust implementation theorem; those require compiler and cryptographic
evidence over an encoding of these exact rows.

The names below `export`ed from `Theory.Store` and `Theory.CellState` are
aliases of the one definition each, not copies.
-/
import Theory.Store
import Theory.CellState

namespace Minidregg.Kernel.SparseAuthenticatedState

open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.CellState

set_option autoImplicit false

universe u v w y

export Minidregg.Theory.Store (Discipline Layout Address Store Op Patch)
export Minidregg.Theory.CellState (Materializer Materialized materialize ValidatedPatch)

namespace Trace

export Minidregg.Theory.Store.Patch (accessFootprint writeFootprint allocationFootprint
  freeFootprint run ValidFrom Executes run_append validFrom_append accessFootprint_append
  writeFootprint_append mem_writeFootprint_iff mem_allocationFootprint_iff run_frame
  changed_only_declared)

end Trace

/-! ## Exact timestamped lookup-bus projection -/

inductive AccessKind
  | read
  | write
  | allocate
  | free
  deriving DecidableEq, Repr

/-- A heterogeneous bus row.  Before/after values retain their namespace type.
`clock` is the operation's exact zero-based position in the patch. -/
structure BusRow (L : Layout.{u, v, w}) where
  clock : Nat
  kind : AccessKind
  space : L.Namespace
  key : L.Key space
  before : Option (L.Value space)
  after : Option (L.Value space)

/-- The bus row selected by one operation at one exact prefix store. -/
def Op.busRow {L : Layout.{u, v, w}} (clock : Nat) (_store : Store L) :
    Op L → BusRow L
  | .read space key observed => ⟨clock, .read, space, key, observed, observed⟩
  | .write space key before after => ⟨clock, .write, space, key, some before, some after⟩
  | .allocate space key value => ⟨clock, .allocate, space, key, none, some value⟩
  | .free space key before => ⟨clock, .free, space, key, some before, none⟩

namespace Trace

/-- Derive one timestamped row per operation while threading exact prefix
stores.  This is the semantic source for a LogUp*/Twist encoding. -/
def busRowsFrom {L : Layout.{u, v, w}} : Nat → Store L → Patch L → List (BusRow L)
  | _, _, [] => []
  | clock, store, op :: rest =>
      Op.busRow clock store op :: busRowsFrom (clock + 1) (op.apply store) rest

def busRows {L : Layout.{u, v, w}} (pre : Store L) (patch : Patch L) : List (BusRow L) :=
  busRowsFrom 0 pre patch

/-- The sequential memory-bus relation.  Every row is the literal projection of
one enabled operation at its exact prefix store, and the next row consumes the
store produced by that operation. -/
inductive BusRelation {L : Layout.{u, v, w}} :
    Nat → Store L → Patch L → List (BusRow L) → Store L → Prop
  | nil (clock : Nat) (store : Store L) : BusRelation clock store [] [] store
  | cons {clock : Nat} {store post : Store L} {op : Op L} {ops : Patch L}
      {rows : List (BusRow L)}
      (enabled : op.Enabled store)
      (tail : BusRelation (clock + 1) (op.apply store) ops rows post) :
      BusRelation clock store (op :: ops) (Op.busRow clock store op :: rows) post

/-- Prefix-valid execution generates an exact sequential bus relation. -/
theorem busRelation_of_valid {L : Layout.{u, v, w}} (clock : Nat) (pre : Store L)
    (patch : Patch L) (valid : Patch.ValidFrom pre patch) :
    BusRelation clock pre patch (busRowsFrom clock pre patch) (Patch.run pre patch) := by
  induction patch generalizing clock pre with
  | nil => exact .nil clock pre
  | cons op rest ih => exact .cons valid.1 (ih (clock + 1) (op.apply pre) valid.2)

/-- And conversely: a bus relation exists only over a prefix-valid patch.  A
patch with a failing guard has no rows at all. -/
theorem BusRelation.valid {L : Layout.{u, v, w}} {clock : Nat} {pre post : Store L}
    {patch : Patch L} {rows : List (BusRow L)}
    (relation : BusRelation clock pre patch rows post) : Patch.ValidFrom pre patch := by
  induction relation with
  | nil => trivial
  | cons enabled _ ih => exact ⟨enabled, ih⟩

/-- The bus relation determines the derived row list exactly. -/
theorem BusRelation.rows_exact {L : Layout.{u, v, w}} {clock : Nat} {pre post : Store L}
    {patch : Patch L} {rows : List (BusRow L)}
    (relation : BusRelation clock pre patch rows post) :
    rows = busRowsFrom clock pre patch := by
  induction relation with
  | nil => rfl
  | cons _ _ ih =>
      simp only [busRowsFrom]
      exact congrArg _ ih

/-- The bus relation also determines the final store exactly. -/
theorem BusRelation.post_exact {L : Layout.{u, v, w}} {clock : Nat} {pre post : Store L}
    {patch : Patch L} {rows : List (BusRow L)}
    (relation : BusRelation clock pre patch rows post) :
    post = Patch.run pre patch := by
  induction relation with
  | nil => rfl
  | cons _ _ ih => simpa only [Patch.run] using ih

@[simp] theorem busRowsFrom_length {L : Layout.{u, v, w}} (clock : Nat) (pre : Store L)
    (patch : Patch L) : (busRowsFrom clock pre patch).length = patch.length := by
  induction patch generalizing clock pre with
  | nil => rfl
  | cons op rest ih => simp [busRowsFrom, ih]

@[simp] theorem busRows_length {L : Layout.{u, v, w}} (pre : Store L) (patch : Patch L) :
    (busRows pre patch).length = patch.length :=
  busRowsFrom_length 0 pre patch

end Trace

/-- The semantic seam to a lookup/permutation proof dialect.  Roots are the
canonical cell roots and rows are literal patch projections.  A proof compiler
may encode this claim, but cannot replace either equality with a free digest or
a prover-selected row list. -/
structure ExactBusClaim {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {pre : Materialized M} {expectedPreRoot : Root}
    {patch : Patch L} (validated : ValidatedPatch M pre expectedPreRoot patch) where
  preRoot : Root
  postRoot : Root
  rows : List (BusRow L)
  preRoot_exact : preRoot = pre.root
  postRoot_exact : postRoot = validated.apply.root
  rows_exact : rows = Trace.busRows pre.logical patch
  rows_semantic : Trace.BusRelation 0 pre.logical patch rows validated.apply.logical

/-- Every validated patch has its exact bus claim, derived. -/
def ExactBusClaim.ofValidated {L : Layout.{u, v, w}} {Root : Type y}
    {M : Materializer L Root} {pre : Materialized M} {expectedPreRoot : Root}
    {patch : Patch L} (validated : ValidatedPatch M pre expectedPreRoot patch) :
    ExactBusClaim validated where
  preRoot := pre.root
  postRoot := validated.apply.root
  rows := Trace.busRows pre.logical patch
  preRoot_exact := rfl
  postRoot_exact := rfl
  rows_exact := rfl
  rows_semantic := Trace.busRelation_of_valid 0 pre.logical patch validated.valid

/-! ## Poles, over `Theory.Store.Example` -/

namespace Example

open Minidregg.Theory.Store.Example

/-- Satisfied: the valid sample patch has its exact two-row bus relation. -/
theorem samplePatch_busRelation :
    Trace.BusRelation 0 empty samplePatch (Trace.busRows empty samplePatch)
      (Patch.run empty samplePatch) :=
  Trace.busRelation_of_valid 0 empty samplePatch samplePatch_valid

theorem samplePatch_busRows_length : (Trace.busRows empty samplePatch).length = 2 := by
  simp [samplePatch]

/-- Refuted: a patch whose second allocation is stale has no bus relation for
any rows and any post-store. -/
theorem duplicate_allocation_no_busRelation (rows : List (BusRow layout))
    (post : Store layout) :
    ¬ Trace.BusRelation 0 empty [allocate .heap 7 42, allocate .heap 7 42] rows post :=
  fun relation => duplicate_allocation_rejected relation.valid

end Example

/-- info: 'Minidregg.Kernel.SparseAuthenticatedState.Trace.BusRelation.rows_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Trace.BusRelation.rows_exact
/-- info: 'Minidregg.Kernel.SparseAuthenticatedState.Trace.BusRelation.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Trace.BusRelation.valid
/-- info: 'Minidregg.Kernel.SparseAuthenticatedState.Example.samplePatch_busRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.samplePatch_busRelation
/-- info: 'Minidregg.Kernel.SparseAuthenticatedState.Example.duplicate_allocation_no_busRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.duplicate_allocation_no_busRelation

end Minidregg.Kernel.SparseAuthenticatedState
