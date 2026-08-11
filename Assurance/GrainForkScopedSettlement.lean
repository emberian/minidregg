/-
# Assurance.GrainForkScopedSettlement -- finite grain receipt openings

`GrainForkSettlement.FieldProjection` asks `Fin n -> S.Field` to be
surjective.  That enumerates the entire schema and is therefore empty for the
infinite address spaces used by sparse cells.  A grain receipt needs a much
narrower fact: finite scalar openings for the declared focus, exact public
pre/post roots, and a frame law outside the joint patch.

This module supplies that seam without changing the existing settlement
semantics.  A `FieldFocus` is a finite superset of one joint patch footprint.
Its coordinate type has one always-present root marker plus one coordinate per
focused field, so its `Fin width` transport is nonempty without assuming the
schema itself is finite.  The canonical typed hyperedge and public Digest roots
remain exact beside the scalar word; no cryptographic binding claim is made.
-/
import Assurance.GrainForkSettlement

namespace Minidregg.Assurance.GrainForkScopedSettlement

open Minidregg.Assurance.GrainForkSettlement
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Kernel.TypedCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w x y z b p

noncomputable section

/-! ## Finite focus, independent of whole-schema cardinality -/

/-- Finite field coordinates covering one exact canonical patch.  Extra
coordinates may be retained for a grain view; the patch itself remains the
authoritative touched set. -/
structure FieldFocus
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    {Root : Type y} (patch : CellState.Patch S Root) where
  fields : Finset S.Field
  covers : patch.fieldFootprint ⊆ fields

namespace FieldFocus

variable
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    {Root : Type y} {patch : CellState.Patch S Root}

def exact (patch : CellState.Patch S Root) : FieldFocus patch where
  fields := patch.fieldFootprint
  covers := Finset.Subset.rfl

/-- The root marker makes the carrier nonempty even for a read-only/empty
field footprint. -/
abbrev Coordinate (focus : FieldFocus patch) := Fin 1 ⊕ focus.fields

def rootCoordinate (focus : FieldFocus patch) : focus.Coordinate :=
  Sum.inl 0

def fieldCoordinate (focus : FieldFocus patch)
    (field : S.Field) (member : field ∈ focus.fields) : focus.Coordinate :=
  Sum.inr ⟨field, member⟩

instance coordinateNonempty (focus : FieldFocus patch) :
    Nonempty focus.Coordinate :=
  ⟨focus.rootCoordinate⟩

def width (focus : FieldFocus patch) : Nat :=
  Fintype.card focus.Coordinate

theorem width_positive (focus : FieldFocus patch) : 0 < focus.width :=
  Fintype.card_pos

def coordinateEquivFin (focus : FieldFocus patch) :
    focus.Coordinate ≃ Fin focus.width :=
  Fintype.equivFin focus.Coordinate

end FieldFocus

/-- Deployment-selected scalar openings.  They need not be injective at this
semantic layer; a concrete proof controller must separately state the codec
and binding properties it actually checks. -/
structure Scalarizer (S : CellState.Schema.{u, v, w, x}) (F : Type z) where
  root : Digest -> F
  field : (field : S.Field) -> Option (S.FieldType field) -> F

namespace FieldFocus

variable
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    {M : CellState.Materializer S Digest}
    {patch : CellState.Patch S Digest}
    (focus : FieldFocus patch)
    {F : Type z} (scalarizer : Scalarizer S F)

def project (cell : CellState.Materialized M) :
    Minidregg.Theory.ReactiveReceipt.Store focus.Coordinate F
  | Sum.inl _ => scalarizer.root cell.root
  | Sum.inr field =>
      scalarizer.field field.1 (cell.logical.fields field.1)

@[simp] theorem project_root (cell : CellState.Materialized M) :
    focus.project scalarizer cell focus.rootCoordinate =
      scalarizer.root cell.root :=
  rfl

@[simp] theorem project_field (cell : CellState.Materialized M)
    (field : S.Field) (member : field ∈ focus.fields) :
    focus.project scalarizer cell (focus.fieldCoordinate field member) =
      scalarizer.field field (cell.logical.fields field) :=
  rfl

def IsTouched : focus.Coordinate -> Prop
  | Sum.inl _ => True
  | Sum.inr field => field.1 ∈ patch.fieldFootprint

instance isTouchedDecidable (coordinate : focus.Coordinate) :
    Decidable (focus.IsTouched coordinate) := by
  cases coordinate with
  | inl root => simp only [IsTouched]; infer_instance
  | inr field => simp only [IsTouched]; infer_instance

def touched : Finset focus.Coordinate :=
  Finset.univ.filter focus.IsTouched

@[simp] theorem root_mem_touched : focus.rootCoordinate ∈ focus.touched := by
  simp [touched, IsTouched, rootCoordinate]

@[simp] theorem field_mem_touched (field : S.Field)
    (member : field ∈ focus.fields) :
    focus.fieldCoordinate field member ∈ focus.touched <->
      field ∈ patch.fieldFootprint := by
  simp [touched, IsTouched, fieldCoordinate]

def finProject (cell : CellState.Materialized M) :
    Minidregg.Theory.ReactiveReceipt.Store (Fin focus.width) F :=
  fun index =>
    focus.project scalarizer cell (focus.coordinateEquivFin.symm index)

def finTouched : Finset (Fin focus.width) :=
  focus.touched.map focus.coordinateEquivFin.toEmbedding

@[simp] theorem finProject_at_root (cell : CellState.Materialized M) :
    focus.finProject scalarizer cell
        (focus.coordinateEquivFin focus.rootCoordinate) =
      scalarizer.root cell.root := by
  simp [finProject]

@[simp] theorem finProject_at_field (cell : CellState.Materialized M)
    (field : S.Field) (member : field ∈ focus.fields) :
    focus.finProject scalarizer cell
        (focus.coordinateEquivFin (focus.fieldCoordinate field member)) =
      scalarizer.field field (cell.logical.fields field) := by
  simp [finProject]

end FieldFocus

/-! ## Adapter for the existing accepted grain settlement -/

section Settlement

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {portal : Portal} {projection : AuthorizationProjection S}
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance}
    {declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence}
    {L : Minidregg.Kernel.SparseAuthenticatedState.Layout.{u, v, w}}
    {sparseMaterializer :
      Minidregg.Kernel.SparseAuthenticatedState.Materializer L Digest}
    {Plane : Type p} [DecidableEq Plane]
    {sparseState : Plane ->
      Minidregg.Kernel.SparseAuthenticatedState.Materialized sparseMaterializer}
    {base : CanonicalHead}
    {cut : FocusCut (L := L) (sparseMaterializer := sparseMaterializer)
      (Plane := Plane) (sparseState := sparseState) base declaration}

/-- The existing cut already proves that its finite focus is exactly the joint
patch footprint.  This adapter merely reifies that proof as the scoped carrier. -/
def settlementFieldFocus
    (_settlement : AcceptedSettlement (law := law) cut) :
    FieldFocus declaration.jointPatch where
  fields := cut.focus.fields
  covers := by
    rw [cut.fieldsExact]

omit [DecidableEq Incidence] in
@[simp] theorem settlementFieldFocus_fields
    (settlement : AcceptedSettlement (law := law) cut) :
    (settlementFieldFocus settlement).fields = cut.focus.fields :=
  rfl

omit [DecidableEq Incidence] in
theorem settlementFieldFocus_exact
    (settlement : AcceptedSettlement (law := law) cut) :
    (settlementFieldFocus settlement).fields =
      declaration.jointPatch.fieldFootprint :=
  cut.fieldsExact

theorem settlementScopedFrame
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer S F)
    (coordinate : (settlementFieldFocus settlement).Coordinate)
    (outside : coordinate ∉ (settlementFieldFocus settlement).touched) :
    (settlementFieldFocus settlement).project scalarizer settlement.post coordinate =
      (settlementFieldFocus settlement).project scalarizer declaration.pre coordinate := by
  cases coordinate with
  | inl root =>
      exact False.elim (outside (by simp [FieldFocus.touched,
        FieldFocus.IsTouched]))
  | inr field =>
      apply congrArg (scalarizer.field field.1)
      apply settlement.commit.field_frame field.1
      intro named
      exact outside (by simp [FieldFocus.touched,
        FieldFocus.IsTouched, named])

def settlementScopedDelta
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer S F) :
    Minidregg.Theory.ReactiveReceipt.ReceiptDelta
      ((settlementFieldFocus settlement).project scalarizer declaration.pre)
      ((settlementFieldFocus settlement).project scalarizer settlement.post) where
  touched := (settlementFieldFocus settlement).touched
  frame := settlementScopedFrame settlement scalarizer

theorem settlementFinScopedFrame
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer S F)
    (index : Fin (settlementFieldFocus settlement).width)
    (outside : index ∉ (settlementFieldFocus settlement).finTouched) :
    (settlementFieldFocus settlement).finProject scalarizer settlement.post index =
      (settlementFieldFocus settlement).finProject scalarizer declaration.pre index := by
  apply settlementScopedFrame settlement scalarizer
  intro member
  exact outside (Finset.mem_map.mpr
    ⟨(settlementFieldFocus settlement).coordinateEquivFin.symm index, member,
      (settlementFieldFocus settlement).coordinateEquivFin.apply_symm_apply index⟩)

def settlementFinScopedDelta
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer S F) :
    Minidregg.Theory.ReactiveReceipt.ReceiptDelta
      ((settlementFieldFocus settlement).finProject scalarizer declaration.pre)
      ((settlementFieldFocus settlement).finProject scalarizer settlement.post) where
  touched := (settlementFieldFocus settlement).finTouched
  frame := settlementFinScopedFrame settlement scalarizer

omit [DecidableEq Incidence] in
@[simp] theorem settlementFinPreRootExact
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer S F) :
    (settlementFieldFocus settlement).finProject scalarizer declaration.pre
        ((settlementFieldFocus settlement).coordinateEquivFin
          (settlementFieldFocus settlement).rootCoordinate) =
      scalarizer.root declaration.pre.root := by
  simp

@[simp] theorem settlementFinPostRootExact
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer S F) :
    (settlementFieldFocus settlement).finProject scalarizer settlement.post
        ((settlementFieldFocus settlement).coordinateEquivFin
          (settlementFieldFocus settlement).rootCoordinate) =
      scalarizer.root settlement.post.root := by
  simp

def settlementScopedReceiptClaim
    {F : Type*} [Field F] [DecidableEq F]
    (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer S F)
    (headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F) :
    BoundSemanticReceiptClaim (settlementFieldFocus settlement).width F where
  witness :=
    { binding := headerCells settlement
      core := ReceiptWitness.ofDelta
        (settlementFinScopedDelta settlement scalarizer) }
  valid := ReceiptWitness.ofDelta_satisfies
    (settlementFinScopedDelta settlement scalarizer)

/-- The replacement receipt retains the same accepted semantic hyperedge and
binds its claim to the finite focus-derived delta. -/
structure ScopedCanonicalReceipt
    {F : Type*} [Field F] [DecidableEq F]
    (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer S F)
    (headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F) where
  private mk ::
  semanticHyperedge :
    Minidregg.Kernel.TypedCellHyperedge.Commit.SemanticHyperedge
      settlement.commit
  semanticHyperedgeExact : semanticHyperedge = settlement.hyperedge
  claim : BoundSemanticReceiptClaim (settlementFieldFocus settlement).width F
  claimExact : claim = settlementScopedReceiptClaim settlement scalarizer headerCells

def mintScopedReceipt
    {F : Type*} [Field F] [DecidableEq F]
    (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer S F)
    (headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F) :
    ScopedCanonicalReceipt settlement scalarizer headerCells where
  semanticHyperedge := settlement.hyperedge
  semanticHyperedgeExact := rfl
  claim := settlementScopedReceiptClaim settlement scalarizer headerCells
  claimExact := rfl

@[simp] theorem ScopedCanonicalReceipt.claim_core_exact
    {F : Type*} [Field F] [DecidableEq F]
    {settlement : AcceptedSettlement (law := law) cut}
    {scalarizer : Scalarizer S F}
    {headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F}
    (receipt : ScopedCanonicalReceipt settlement scalarizer headerCells) :
    receipt.claim.witness.core =
      ReceiptWitness.ofDelta (settlementFinScopedDelta settlement scalarizer) := by
  rw [receipt.claimExact]
  rfl

@[simp] theorem ScopedCanonicalReceipt.claim_binding_exact
    {F : Type*} [Field F] [DecidableEq F]
    {settlement : AcceptedSettlement (law := law) cut}
    {scalarizer : Scalarizer S F}
    {headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F}
    (receipt : ScopedCanonicalReceipt settlement scalarizer headerCells) :
    receipt.claim.witness.binding = headerCells settlement := by
  rw [receipt.claimExact]
  rfl

/-- The fork base and canonical pre remain exact public roots beside the
finite opening word. -/
theorem ScopedCanonicalReceipt.base_pre_exact
    {F : Type*} [Field F] [DecidableEq F]
    {settlement : AcceptedSettlement (law := law) cut}
    {scalarizer : Scalarizer S F}
    {headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F}
    (_receipt : ScopedCanonicalReceipt settlement scalarizer headerCells) :
    settlement.header.forkStateRoot = base.stateRoot /\
      cut.canonical.head.stateRoot = declaration.pre.root :=
  ⟨rfl, cut.canonicalPreStateExact⟩

theorem ScopedCanonicalReceipt.post_root_exact
    {F : Type*} [Field F] [DecidableEq F]
    {settlement : AcceptedSettlement (law := law) cut}
    {scalarizer : Scalarizer S F}
    {headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F}
    (_receipt : ScopedCanonicalReceipt settlement scalarizer headerCells) :
    settlement.header.postStateRoot = declaration.apex :=
  settlement.postRoot

end Settlement

/-! ## Concrete witness over an infinite field schema -/

namespace InfiniteSchemaWitness

/-- A deliberately infinite schema field index.  The resource lane is empty. -/
def schema : CellState.Schema where
  Field := Nat
  FieldType := fun _ => Nat
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance : DecidableEq schema.Field := inferInstanceAs (DecidableEq Nat)
instance : Infinite schema.Field := inferInstanceAs (Infinite Nat)

def patch : CellState.Patch schema Digest where
  expectedPreRoot := ⟨0⟩
  fieldFootprint := {(7 : Nat), (42 : Nat)}
  resourceFootprint := ∅
  fieldWrites :=
    [ { field := (7 : Nat), value := some (11 : Nat) },
      { field := (42 : Nat), value := some (99 : Nat) } ]
  resourceWrites := []

def focus : FieldFocus patch := FieldFocus.exact patch

/-- An explicit semantic scalarizer into an infinite proof field.  This is a
carrier witness, not a deployment codec or cryptographic commitment. -/
def encodeField (field : schema.Field)
    (value : Option (schema.FieldType field)) : Rat := by
  change Option Nat at value
  exact match value with
  | none => 0
  | some natural => (natural : Rat) + 1

def scalarizer : Scalarizer schema Rat where
  root := fun digest => (digest.value : Rat)
  field := fun field value =>
    encodeField field value

theorem focused_coordinates_nonempty : Nonempty focus.Coordinate :=
  inferInstance

theorem focused_width_positive : 0 < focus.width :=
  focus.width_positive

@[simp] theorem focused_width_exact : focus.width = 3 := by
  native_decide

@[simp] theorem seven_focused : (7 : Nat) ∈ focus.fields := by
  native_decide

@[simp] theorem fortyTwo_focused : (42 : Nat) ∈ focus.fields := by
  native_decide

/-- The adapter is finite without pretending that the whole `Nat` schema is
finite or enumerated. -/
@[simp] theorem thousand_not_focused : (1000 : Nat) ∉ focus.fields := by
  native_decide

end InfiniteSchemaWitness

/-! ## Negative tooth for the old whole-schema target -/

namespace CardinalityTooth

/-- The old field projection is empty for every infinite schema, independently
of the field encoder or proof field: no finite `Fin n` can surject onto an
infinite address type. -/
theorem no_wholeSchema_FieldProjection
    {S : CellState.Schema.{u, v, w, x}} [Infinite S.Field]
    {n : Nat} {F : Type*} [Field F] :
    Not (Nonempty (GrainForkSettlement.FieldProjection (S := S) n F)) := by
  rintro ⟨projection⟩
  exact not_surjective_finite_infinite projection.keyAt
    projection.keyAt_surjective

end CardinalityTooth

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.GrainForkScopedSettlement.settlementScopedFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms settlementScopedFrame
/-- info: 'Minidregg.Assurance.GrainForkScopedSettlement.settlementScopedReceiptClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms settlementScopedReceiptClaim
/-- info: 'Minidregg.Assurance.GrainForkScopedSettlement.ScopedCanonicalReceipt.post_root_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ScopedCanonicalReceipt.post_root_exact
/-- info: 'Minidregg.Assurance.GrainForkScopedSettlement.CardinalityTooth.no_wholeSchema_FieldProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CardinalityTooth.no_wholeSchema_FieldProjection

end

end Minidregg.Assurance.GrainForkScopedSettlement
