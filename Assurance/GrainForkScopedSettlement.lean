/-
# Assurance.GrainForkScopedSettlement -- finite grain receipt openings

`GrainForkSettlement.FieldProjection` asks `Fin n -> Address L` to be
surjective.  That enumerates the entire layout and is therefore empty for the
infinite address spaces used by sparse cells.  A grain receipt needs a much
narrower fact: finite scalar openings for the declared focus, exact public
pre/post roots, and a frame law outside the joint patch.

This module supplies that seam without changing the existing settlement
semantics.  A `FieldFocus` is a finite superset of one joint patch's write
footprint.  Its coordinate type has one always-present root marker plus one
coordinate per focused address, so its `Fin width` transport is nonempty
without assuming the layout itself is finite.  The canonical typed hyperedge and public Digest roots
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

universe u v w y z b p

noncomputable section

/-! ## Finite focus, independent of whole-schema cardinality -/

/-- Finite address coordinates covering one exact canonical patch.  Extra
coordinates may be retained for a grain view; the patch itself remains the
authoritative touched set. -/
structure FieldFocus
    {L : Store.Layout.{u, v, w}} (patch : Store.Patch L) where
  fields : Finset (Store.Address L)
  covers : Store.Patch.writeFootprint patch ⊆ fields

namespace FieldFocus

variable
    {L : Store.Layout.{u, v, w}} {patch : Store.Patch L}

def exact (patch : Store.Patch L) : FieldFocus patch where
  fields := Store.Patch.writeFootprint patch
  covers := Finset.Subset.rfl

/-- The root marker makes the carrier nonempty even for a read-only/empty
field footprint. -/
abbrev Coordinate (focus : FieldFocus patch) := Fin 1 ⊕ focus.fields

def rootCoordinate (focus : FieldFocus patch) : focus.Coordinate :=
  Sum.inl 0

def fieldCoordinate (focus : FieldFocus patch)
    (field : Store.Address L) (member : field ∈ focus.fields) : focus.Coordinate :=
  Sum.inr ⟨field, member⟩

instance coordinateNonempty (focus : FieldFocus patch) :
    Nonempty focus.Coordinate :=
  ⟨focus.rootCoordinate⟩

def width (focus : FieldFocus patch) : Nat :=
  Fintype.card focus.Coordinate

theorem width_positive (focus : FieldFocus patch) : 0 < focus.width :=
  Fintype.card_pos

theorem width_eq (focus : FieldFocus patch) : focus.width = 1 + focus.fields.card := by
  simp [width, Coordinate]

def coordinateEquivFin (focus : FieldFocus patch) :
    focus.Coordinate ≃ Fin focus.width :=
  Fintype.equivFin focus.Coordinate

end FieldFocus

/-- Deployment-selected scalar openings.  They need not be injective at this
semantic layer; a concrete proof controller must separately state the codec
and binding properties it actually checks. -/
structure Scalarizer (L : Store.Layout.{u, v, w}) (F : Type z) where
  root : Digest -> F
  field : (address : Store.Address L) -> Option (L.Value address.1) -> F

namespace FieldFocus

variable
    {L : Store.Layout.{u, v, w}}
    {M : CellState.Materializer L Digest}
    {patch : Store.Patch L}
    (focus : FieldFocus patch)
    {F : Type z} (scalarizer : Scalarizer L F)

def project (cell : CellState.Materialized M) :
    Minidregg.Theory.ReactiveReceipt.Store focus.Coordinate F
  | Sum.inl _ => scalarizer.root cell.root
  | Sum.inr field =>
      scalarizer.field field.1 (cell.logical field.1)

@[simp] theorem project_root (cell : CellState.Materialized M) :
    focus.project scalarizer cell focus.rootCoordinate =
      scalarizer.root cell.root :=
  rfl

@[simp] theorem project_field (cell : CellState.Materialized M)
    (field : Store.Address L) (member : field ∈ focus.fields) :
    focus.project scalarizer cell (focus.fieldCoordinate field member) =
      scalarizer.field field (cell.logical field) :=
  rfl

def IsTouched : focus.Coordinate -> Prop
  | Sum.inl _ => True
  | Sum.inr field => field.1 ∈ Store.Patch.writeFootprint patch

instance isTouchedDecidable (coordinate : focus.Coordinate) :
    Decidable (focus.IsTouched coordinate) := by
  cases coordinate with
  | inl root => simp only [IsTouched]; infer_instance
  | inr field => simp only [IsTouched]; infer_instance

def touched : Finset focus.Coordinate :=
  Finset.univ.filter focus.IsTouched

@[simp] theorem root_mem_touched : focus.rootCoordinate ∈ focus.touched := by
  simp [touched, IsTouched, rootCoordinate]

@[simp] theorem field_mem_touched (field : Store.Address L)
    (member : field ∈ focus.fields) :
    focus.fieldCoordinate field member ∈ focus.touched <->
      field ∈ Store.Patch.writeFootprint patch := by
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
    (field : Store.Address L) (member : field ∈ focus.fields) :
    focus.finProject scalarizer cell
        (focus.coordinateEquivFin (focus.fieldCoordinate field member)) =
      scalarizer.field field (cell.logical field) := by
  simp [finProject]

end FieldFocus

/-! ## Adapter for the existing accepted grain settlement -/

section Settlement

variable
    {L : Store.Layout.{u, v, w}}
    {M : CellState.Materializer L Digest}
    {portal : Portal} {projection : AuthorizationProjection L}
    {Incidence : Type z} [Fintype Incidence]
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance}
    {declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence}
    {SL : Store.Layout.{u, v, w}}
    {sparseMaterializer : CellState.Materializer SL Digest}
    {Plane : Type p} [DecidableEq Plane]
    {sparseState : Plane -> CellState.Materialized sparseMaterializer}
    {base : CanonicalHead}
    {cut : FocusCut (SL := SL) (sparseMaterializer := sparseMaterializer)
      (Plane := Plane) (sparseState := sparseState) base declaration}

/-- The existing cut already proves that its finite focus is exactly the joint
patch footprint.  This adapter merely reifies that proof as the scoped carrier. -/
def settlementFieldFocus
    (_settlement : AcceptedSettlement (law := law) cut) :
    FieldFocus declaration.jointPatch where
  fields := cut.focus.addresses
  covers := by
    rw [cut.addressesExact]

@[simp] theorem settlementFieldFocus_fields
    (settlement : AcceptedSettlement (law := law) cut) :
    (settlementFieldFocus settlement).fields = cut.focus.addresses :=
  rfl

theorem settlementFieldFocus_exact
    (settlement : AcceptedSettlement (law := law) cut) :
    (settlementFieldFocus settlement).fields =
      Store.Patch.writeFootprint declaration.jointPatch :=
  cut.addressesExact

theorem settlementScopedFrame
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer L F)
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
      apply settlement.commit.frame field.1
      intro named
      exact outside (by simp [FieldFocus.touched,
        FieldFocus.IsTouched, named])

def settlementScopedDelta
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer L F) :
    Minidregg.Theory.ReactiveReceipt.ReceiptDelta
      ((settlementFieldFocus settlement).project scalarizer declaration.pre)
      ((settlementFieldFocus settlement).project scalarizer settlement.post) where
  touched := (settlementFieldFocus settlement).touched
  frame := settlementScopedFrame settlement scalarizer

theorem settlementFinScopedFrame
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer L F)
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
    (scalarizer : Scalarizer L F) :
    Minidregg.Theory.ReactiveReceipt.ReceiptDelta
      ((settlementFieldFocus settlement).finProject scalarizer declaration.pre)
      ((settlementFieldFocus settlement).finProject scalarizer settlement.post) where
  touched := (settlementFieldFocus settlement).finTouched
  frame := settlementFinScopedFrame settlement scalarizer

@[simp] theorem settlementFinPreRootExact
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer L F) :
    (settlementFieldFocus settlement).finProject scalarizer declaration.pre
        ((settlementFieldFocus settlement).coordinateEquivFin
          (settlementFieldFocus settlement).rootCoordinate) =
      scalarizer.root declaration.pre.root := by
  simp

@[simp] theorem settlementFinPostRootExact
    {F : Type*} (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer L F) :
    (settlementFieldFocus settlement).finProject scalarizer settlement.post
        ((settlementFieldFocus settlement).coordinateEquivFin
          (settlementFieldFocus settlement).rootCoordinate) =
      scalarizer.root settlement.post.root := by
  simp

def settlementScopedReceiptClaim
    {F : Type*} [Field F] [DecidableEq F]
    (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer L F)
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
    (scalarizer : Scalarizer L F)
    (headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F) where
  private mk ::
  semanticHyperedge :
    Minidregg.Kernel.TypedCellHyperedge.Commit.SemanticHyperedge law declaration
  semanticHyperedgeExact : semanticHyperedge = settlement.hyperedge
  claim : BoundSemanticReceiptClaim (settlementFieldFocus settlement).width F
  claimExact : claim = settlementScopedReceiptClaim settlement scalarizer headerCells

def mintScopedReceipt
    {F : Type*} [Field F] [DecidableEq F]
    (settlement : AcceptedSettlement (law := law) cut)
    (scalarizer : Scalarizer L F)
    (headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F) :
    ScopedCanonicalReceipt settlement scalarizer headerCells where
  semanticHyperedge := settlement.hyperedge
  semanticHyperedgeExact := rfl
  claim := settlementScopedReceiptClaim settlement scalarizer headerCells
  claimExact := rfl

@[simp] theorem ScopedCanonicalReceipt.claim_core_exact
    {F : Type*} [Field F] [DecidableEq F]
    {settlement : AcceptedSettlement (law := law) cut}
    {scalarizer : Scalarizer L F}
    {headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F}
    (receipt : ScopedCanonicalReceipt settlement scalarizer headerCells) :
    receipt.claim.witness.core =
      ReceiptWitness.ofDelta (settlementFinScopedDelta settlement scalarizer) := by
  rw [receipt.claimExact]
  rfl

@[simp] theorem ScopedCanonicalReceipt.claim_binding_exact
    {F : Type*} [Field F] [DecidableEq F]
    {settlement : AcceptedSettlement (law := law) cut}
    {scalarizer : Scalarizer L F}
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
    {scalarizer : Scalarizer L F}
    {headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F}
    (_receipt : ScopedCanonicalReceipt settlement scalarizer headerCells) :
    settlement.header.forkStateRoot = base.stateRoot /\
      cut.canonical.head.stateRoot = declaration.pre.root :=
  ⟨rfl, cut.canonicalPreStateExact⟩

theorem ScopedCanonicalReceipt.post_root_exact
    {F : Type*} [Field F] [DecidableEq F]
    {settlement : AcceptedSettlement (law := law) cut}
    {scalarizer : Scalarizer L F}
    {headerCells : AcceptedSettlement (law := law) cut -> BindingIx -> F}
    (_receipt : ScopedCanonicalReceipt settlement scalarizer headerCells) :
    settlement.header.postStateRoot = declaration.apex :=
  settlement.postRoot

end Settlement

/-! ## Concrete witness over an infinite address layout -/

namespace InfiniteSchemaWitness

/-- A deliberately infinite key space: one RAM namespace keyed by `Nat`. -/
abbrev layout : Store.Layout.{0, 0, 0} where
  Namespace := Unit
  Key := fun _ => Nat
  Value := fun _ => Nat
  discipline := fun _ => .ram

instance : Infinite (Store.Address layout) :=
  Infinite.of_injective (fun key : Nat => (⟨(), key⟩ : Store.Address layout))
    (fun _ _ same => by simpa using same)

def patch : Store.Patch layout :=
  [@Store.Op.allocate layout () 7 11, @Store.Op.allocate layout () 42 99]

def focus : FieldFocus patch := FieldFocus.exact patch

/-- An explicit semantic scalarizer into an infinite proof field.  This is a
carrier witness, not a deployment codec or cryptographic commitment. -/
def encodeField (_address : Store.Address layout) (value : Option Nat) : Rat :=
  match value with
  | none => 0
  | some natural => (natural : Rat) + 1

def scalarizer : Scalarizer layout Rat where
  root := fun digest => (digest.value : Rat)
  field := encodeField

theorem focused_coordinates_nonempty : Nonempty focus.Coordinate :=
  inferInstance

theorem focused_width_positive : 0 < focus.width :=
  focus.width_positive

theorem focused_fields_card : focus.fields.card = 2 := by
  decide

@[simp] theorem focused_width_exact : focus.width = 3 := by
  rw [FieldFocus.width_eq, focused_fields_card]

@[simp] theorem seven_focused : (⟨(), 7⟩ : Store.Address layout) ∈ focus.fields := by
  decide

@[simp] theorem fortyTwo_focused : (⟨(), 42⟩ : Store.Address layout) ∈ focus.fields := by
  decide

/-- The adapter is finite without pretending that the whole `Nat` key space is
finite or enumerated. -/
@[simp] theorem thousand_not_focused :
    (⟨(), 1000⟩ : Store.Address layout) ∉ focus.fields := by
  decide

end InfiniteSchemaWitness

/-! ## Negative tooth for the old whole-layout target -/

namespace CardinalityTooth

/-- The whole-layout field projection is empty for every infinite address
type, independently of the encoder or proof field: no finite `Fin n` can
surject onto an infinite address type. -/
theorem no_wholeSchema_FieldProjection
    {L : Store.Layout.{u, v, w}} [Infinite (Store.Address L)]
    {n : Nat} {F : Type*} [Field F] :
    Not (Nonempty (GrainForkSettlement.FieldProjection (L := L) n F)) := by
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
/-- info: 'Minidregg.Assurance.GrainForkScopedSettlement.InfiniteSchemaWitness.focused_width_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms InfiniteSchemaWitness.focused_width_exact

end

end Minidregg.Assurance.GrainForkScopedSettlement
