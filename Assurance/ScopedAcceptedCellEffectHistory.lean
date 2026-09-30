/-
# Assurance.ScopedAcceptedCellEffectHistory -- finite openings, exact roots

`AcceptedCellEffectHistory.HistoryProjection` asks one fixed finite field word
to represent *every* materialized cell and then asks the root of that word to
equal the canonical cell root.  That is a useful interface only after a
deployment has proved that its complete state carrier fits the chosen word.
It is not such a proof, and it cannot be instantiated for an unbounded root
stream over a finite field.

This module gives the deliberately narrower production seam.  One accepted
patch chooses a finite observation scope containing its declared footprint.
The algebraic word contains only openings in that scope plus one always-present
root-marker coordinate.  Exact Digest roots remain public typed data beside
the word; this module does not claim that a finite list of local openings
reconstructs, binds, or cryptographically commits the whole cell.

The coordinate carrier is structurally finite even when the layout's address
type is infinite.  It is transported to `Fin width` for the existing receipt relation,
with `0 < width` proved from the root-marker coordinate.  Hyperdocument effects
use their exact declaration footprint and therefore never enumerate the
infinite address type.
-/
import Assurance.SemanticReceiptRelation
import Theory.AcceptedCellEffect
import Theory.HyperdocumentOperations

namespace Minidregg.Assurance.ScopedAcceptedCellEffectHistory

open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.CellState
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w y z

noncomputable section

/-! ## A finite scope chosen by one canonical patch -/

/-- A finite observation scope for one patch.  It may retain extra addresses
for reactive/history consumers, but it must contain the patch's exact write
footprint.  No `Fintype (Address L)` or layout enumeration is required. -/
structure DeclaredScope
    {L : Theory.Store.Layout.{u, v, w}}
    (patch : Theory.Store.Patch L) where
  addresses : Finset (Theory.Store.Address L)
  cover : Theory.Store.Patch.writeFootprint patch ⊆ addresses

namespace DeclaredScope

variable
    {L : Theory.Store.Layout.{u, v, w}}
    {patch : Theory.Store.Patch L}

/-- The smallest scope is the declaration footprint itself. -/
def exact (patch : Theory.Store.Patch L) : DeclaredScope patch where
  addresses := Theory.Store.Patch.writeFootprint patch
  cover := Finset.Subset.rfl

/-- One coordinate is reserved for the typed root header.  The other
coordinates are precisely the finitely scoped addresses. -/
abbrev Coordinate (scope : DeclaredScope patch) :=
  Fin 1 ⊕ scope.addresses

def rootCoordinate (scope : DeclaredScope patch) : scope.Coordinate :=
  Sum.inl 0

def addressCoordinate (scope : DeclaredScope patch)
    (address : Theory.Store.Address L) (member : address ∈ scope.addresses) :
    scope.Coordinate :=
  Sum.inr ⟨address, member⟩

instance coordinateNonempty (scope : DeclaredScope patch) :
    Nonempty scope.Coordinate :=
  ⟨scope.rootCoordinate⟩

/-- The width is finite by construction and depends on the chosen patch
scope, not on the cardinality of the layout. -/
def width (scope : DeclaredScope patch) : Nat :=
  Fintype.card scope.Coordinate

theorem width_positive (scope : DeclaredScope patch) : 0 < scope.width :=
  Fintype.card_pos

end DeclaredScope

/-! ## Scalar openings and the honest root boundary -/

/-- Deployment-selected scalar openings.  These are semantic encodings into
the accumulator field.  Injectivity, canonical wire bytes, and cryptographic
binding are intentionally not postulated here; a concrete deployment may add
the laws its proof system actually checks. -/
structure Scalarizer
    (L : Theory.Store.Layout.{u, v, w}) (F : Type z) where
  root : Digest -> F
  value : (address : Theory.Store.Address L) -> Option (L.Value address.1) -> F

namespace DeclaredScope

variable
    {L : Theory.Store.Layout.{u, v, w}}
    {M : CellState.Materializer L Digest}
    {patch : Theory.Store.Patch L}
    (scope : DeclaredScope patch)
    {F : Type z} (scalarizer : Scalarizer L F)
    {expectedPreRoot : Digest}

/-- Project only the finite declared observation scope.  The root coordinate
is a scalar opening of the exact typed root; the root itself remains available
separately as `cell.root`. -/
def project (cell : CellState.Materialized M) : Store scope.Coordinate F
  | Sum.inl _ => scalarizer.root cell.root
  | Sum.inr address => scalarizer.value address.1 (cell.logical address.1)

@[simp] theorem project_root (cell : CellState.Materialized M) :
    scope.project scalarizer cell scope.rootCoordinate =
      scalarizer.root cell.root :=
  rfl

@[simp] theorem project_address (cell : CellState.Materialized M)
    (address : Theory.Store.Address L) (member : address ∈ scope.addresses) :
    scope.project scalarizer cell (scope.addressCoordinate address member) =
      scalarizer.value address (cell.logical address) :=
  rfl

/-- The exact Digest root accompanying a scoped word.  It is not recovered
from the local word and therefore does not smuggle a global finite-state claim
into the accumulator interface. -/
structure Snapshot (cell : CellState.Materialized M) where
  root : Digest
  word : Store scope.Coordinate F
  root_exact : root = cell.root
  word_exact : word = scope.project scalarizer cell

def snapshot (cell : CellState.Materialized M) :
    Snapshot scope scalarizer cell where
  root := cell.root
  word := scope.project scalarizer cell
  root_exact := rfl
  word_exact := rfl

@[simp] theorem snapshot_root (cell : CellState.Materialized M) :
    (scope.snapshot scalarizer cell).root = cell.root :=
  rfl

@[simp] theorem snapshot_word (cell : CellState.Materialized M) :
    (scope.snapshot scalarizer cell).word = scope.project scalarizer cell :=
  rfl

/-! ## Exact scoped transition -/

/-- Root is always touched because the public post-root is part of every
committed transition.  Scoped address coordinates are touched exactly when
the canonical patch writes them. -/
def IsTouched : scope.Coordinate -> Prop
  | Sum.inl _ => True
  | Sum.inr address => address.1 ∈ Theory.Store.Patch.writeFootprint patch

instance isTouchedDecidable (coordinate : scope.Coordinate) :
    Decidable (scope.IsTouched coordinate) := by
  cases coordinate with
  | inl root => simp only [IsTouched]; infer_instance
  | inr address => simp only [IsTouched]; infer_instance

def touched : Finset scope.Coordinate :=
  Finset.univ.filter scope.IsTouched

@[simp] theorem root_mem_touched : scope.rootCoordinate ∈ scope.touched := by
  simp [touched, IsTouched, rootCoordinate]

@[simp] theorem address_mem_touched (address : Theory.Store.Address L)
    (member : address ∈ scope.addresses) :
    scope.addressCoordinate address member ∈ scope.touched <->
      address ∈ Theory.Store.Patch.writeFootprint patch := by
  simp [touched, IsTouched, addressCoordinate]

/-- The local anti-ghost law is inherited from the exact validated typed
patch.  The root coordinate cannot enter the frame premise because it is
always touched. -/
theorem project_frame
    {pre : CellState.Materialized M}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch)
    (coordinate : scope.Coordinate)
    (outside : coordinate ∉ scope.touched) :
    scope.project scalarizer validated.apply coordinate =
      scope.project scalarizer pre coordinate := by
  cases coordinate with
  | inl root =>
      exact False.elim (outside (by simp [touched, IsTouched]))
  | inr address =>
      apply congrArg (scalarizer.value address.1)
      exact Theory.Store.Patch.run_frame pre.logical patch address.1 (fun named =>
        outside (by simp [touched, IsTouched, named]))

def delta
    {pre : CellState.Materialized M}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch) :
    ReceiptDelta (scope.project scalarizer pre)
      (scope.project scalarizer validated.apply) where
  touched := scope.touched
  frame := scope.project_frame scalarizer validated

def core
    [Field F] [DecidableEq F]
    {pre : CellState.Materialized M}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch) :
    ReceiptWitness scope.Coordinate F :=
  ReceiptWitness.ofDelta (scope.delta scalarizer validated)

theorem core_valid
    [Field F] [DecidableEq F]
    {pre : CellState.Materialized M}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch) :
    (scope.core scalarizer validated).Satisfies :=
  ReceiptWitness.ofDelta_satisfies (scope.delta scalarizer validated)

@[simp] theorem core_pre
    [Field F] [DecidableEq F]
    {pre : CellState.Materialized M}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch) :
    (scope.core scalarizer validated).pre = scope.project scalarizer pre :=
  rfl

@[simp] theorem core_post
    [Field F] [DecidableEq F]
    {pre : CellState.Materialized M}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch) :
    (scope.core scalarizer validated).post =
      scope.project scalarizer validated.apply :=
  rfl

/-! ## Transport to the existing `Fin width` receipt carrier -/

def coordinateEquivFin : scope.Coordinate ≃ Fin scope.width :=
  Fintype.equivFin scope.Coordinate

def finProject (cell : CellState.Materialized M) :
    Store (Fin scope.width) F :=
  fun index => scope.project scalarizer cell (scope.coordinateEquivFin.symm index)

def finTouched : Finset (Fin scope.width) :=
  scope.touched.map scope.coordinateEquivFin.toEmbedding

theorem finProject_frame
    {pre : CellState.Materialized M}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch)
    (index : Fin scope.width) (outside : index ∉ scope.finTouched) :
    scope.finProject scalarizer validated.apply index =
      scope.finProject scalarizer pre index := by
  apply scope.project_frame scalarizer validated
  intro member
  exact outside (Finset.mem_map.mpr
    ⟨scope.coordinateEquivFin.symm index, member,
      scope.coordinateEquivFin.apply_symm_apply index⟩)

def finDelta
    {pre : CellState.Materialized M}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch) :
    ReceiptDelta (scope.finProject scalarizer pre)
      (scope.finProject scalarizer validated.apply) where
  touched := scope.finTouched
  frame := scope.finProject_frame scalarizer validated

def finCore
    [Field F] [DecidableEq F]
    {pre : CellState.Materialized M}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch) :
    ReceiptWitness (Fin scope.width) F :=
  ReceiptWitness.ofDelta (scope.finDelta scalarizer validated)

theorem finCore_valid
    [Field F] [DecidableEq F]
    {pre : CellState.Materialized M}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch) :
    (scope.finCore scalarizer validated).Satisfies :=
  ReceiptWitness.ofDelta_satisfies (scope.finDelta scalarizer validated)

@[simp] theorem finProject_at_root (cell : CellState.Materialized M) :
    scope.finProject scalarizer cell
        (scope.coordinateEquivFin scope.rootCoordinate) =
      scalarizer.root cell.root := by
  simp [finProject]

@[simp] theorem finProject_at_address (cell : CellState.Materialized M)
    (address : Theory.Store.Address L) (member : address ∈ scope.addresses) :
    scope.finProject scalarizer cell
        (scope.coordinateEquivFin (scope.addressCoordinate address member)) =
      scalarizer.value address (cell.logical address) := by
  simp [finProject]

end DeclaredScope

/-! ## Accepted effects: the root is exact without a global finite-state claim -/

namespace AcceptedAdapter

variable
    {L : Theory.Store.Layout.{u, v, w}}
    {M : CellState.Materializer L Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, y, z} L M Nullifier}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {pre : CellState.Materialized M}
    {declaration : family.Declaration} {outcome : family.Outcome declaration}

abbrev patch := family.patch declaration outcome

def exactScope : DeclaredScope (patch (family := family)
    (declaration := declaration) (outcome := outcome)) :=
  DeclaredScope.exact (family.patch declaration outcome)

/-- The public pre-root remains the exact typed root of the canonical pre-cell;
it is not reconstructed from the finite scoped word. -/
@[simp] theorem pre_root_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    pre.root = request.preStateRoot := by
  exact (AcceptedCellEffect.preRootBound accepted).symm

/-- The matching post-root is projected from the sole verifier-minted post. -/
@[simp] theorem post_root_exact :
    forall accepted : AcceptedCellEffect (portal := portal)
      (authState := authState) family request pre declaration outcome,
    accepted.prepared.post.root = accepted.prepared.postRoot :=
  fun _ => rfl

def finCore {F : Type*} [Field F] [DecidableEq F]
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (scalarizer : Scalarizer L F) :
    ReceiptWitness
      (Fin (exactScope (family := family) (declaration := declaration)
        (outcome := outcome)).width) F :=
  DeclaredScope.finCore
    (patch := family.patch declaration outcome)
    (exactScope (family := family) (declaration := declaration)
      (outcome := outcome)) scalarizer accepted.validated

theorem finCore_valid {F : Type*} [Field F] [DecidableEq F]
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (scalarizer : Scalarizer L F) :
    (AcceptedAdapter.finCore accepted scalarizer).Satisfies :=
  DeclaredScope.finCore_valid
    (patch := family.patch declaration outcome)
    (exactScope (family := family) (declaration := declaration)
      (outcome := outcome)) scalarizer accepted.validated

end AcceptedAdapter

/-! ## Hyperdocument adapter without schema enumeration -/

namespace HyperdocumentAdapter

open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations

variable
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : HyperdocumentOperations.Declaration}

/-- Exact Hyperdocument scope: the finite set of addresses this action writes.
The infinite `Hyperdocument.Address` type is never enumerated. -/
def scope (config : HyperdocumentOperations.Config)
    (declaration : HyperdocumentOperations.Declaration) :
    DeclaredScope (declaration.patch config) :=
  DeclaredScope.exact (declaration.patch config)

@[simp] theorem scope_addresses : (scope config declaration).addresses =
    Theory.Store.Patch.writeFootprint (declaration.patch config) :=
  rfl

theorem width_positive : 0 < (scope config declaration).width :=
  (scope config declaration).width_positive

def finCore {F : Type*} [Field F] [DecidableEq F]
    (accepted : HyperdocumentOperations.Accepted config projection
      authorityPre documentPre portal declaration)
    (scalarizer : Scalarizer Hyperdocument.layout F) :
    ReceiptWitness (Fin (scope config declaration).width) F :=
  DeclaredScope.finCore (patch := declaration.patch config)
    (scope config declaration) scalarizer accepted.accepted.validated

theorem finCore_valid {F : Type*} [Field F] [DecidableEq F]
    (accepted : HyperdocumentOperations.Accepted config projection
      authorityPre documentPre portal declaration)
    (scalarizer : Scalarizer Hyperdocument.layout F) :
    (HyperdocumentAdapter.finCore accepted scalarizer).Satisfies :=
  DeclaredScope.finCore_valid (patch := declaration.patch config)
    (scope config declaration) scalarizer accepted.accepted.validated

/-- Root headers remain exact typed Digests beside the finite opening word. -/
@[simp] theorem pre_root_exact
    (accepted : HyperdocumentOperations.Accepted config projection
      authorityPre documentPre portal declaration) :
    documentPre.root = declaration.intent.expectedContentRoot := by
  exact (HyperdocumentOperations.ValidOperation.preRootExact
    (HyperdocumentOperations.Accepted.semantic accepted)).symm

@[simp] theorem post_root_exact
    (accepted : HyperdocumentOperations.Accepted config projection
      authorityPre documentPre portal declaration) :
    accepted.accepted.prepared.post.root =
      accepted.accepted.prepared.postRoot :=
  rfl

/-- A declared Hyperdocument address opens from the exact canonical pre-cell. -/
theorem pre_lookup_exact {F : Type*}
    (scalarizer : Scalarizer Hyperdocument.layout F)
    (address : Hyperdocument.Address)
    (named : address ∈ Theory.Store.Patch.writeFootprint (declaration.patch config)) :
    DeclaredScope.finProject (patch := declaration.patch config)
        (scope config declaration) scalarizer documentPre
        (DeclaredScope.coordinateEquivFin (patch := declaration.patch config)
          (scope config declaration)
          ((scope config declaration).addressCoordinate address named)) =
      scalarizer.value address (documentPre.logical address) := by
  exact DeclaredScope.finProject_at_address (patch := declaration.patch config)
    (scope config declaration) scalarizer documentPre address named

/-- The matching post opening is read from the sole verifier-minted post-cell,
not from a receipt-supplied parallel state. -/
theorem post_lookup_exact {F : Type*}
    (accepted : HyperdocumentOperations.Accepted config projection
      authorityPre documentPre portal declaration)
    (scalarizer : Scalarizer Hyperdocument.layout F)
    (address : Hyperdocument.Address)
    (named : address ∈ Theory.Store.Patch.writeFootprint (declaration.patch config)) :
    DeclaredScope.finProject (patch := declaration.patch config)
        (scope config declaration) scalarizer accepted.accepted.prepared.post
        (DeclaredScope.coordinateEquivFin (patch := declaration.patch config)
          (scope config declaration)
          ((scope config declaration).addressCoordinate address named)) =
      scalarizer.value address
        (accepted.accepted.prepared.post.logical address) := by
  exact DeclaredScope.finProject_at_address (patch := declaration.patch config)
    (scope config declaration) scalarizer
    accepted.accepted.prepared.post address named

end HyperdocumentAdapter

/-! ## Axiom pins -/

/-- info: 'Minidregg.Assurance.ScopedAcceptedCellEffectHistory.DeclaredScope.project_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DeclaredScope.project_frame
/-- info: 'Minidregg.Assurance.ScopedAcceptedCellEffectHistory.DeclaredScope.finCore_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DeclaredScope.finCore_valid
/-- info: 'Minidregg.Assurance.ScopedAcceptedCellEffectHistory.HyperdocumentAdapter.post_lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HyperdocumentAdapter.post_lookup_exact
end

end Minidregg.Assurance.ScopedAcceptedCellEffectHistory
