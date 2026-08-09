/-
# Assurance.DeclaredHyperedgeHistoryBinding -- bind the whole joint turn

`DeclaredHyperedgeReceipt` derives the nonlinear state-transition word from
joint execution.  This module fixes what its sixteen public binding cells
mean: a commitment to the admission context and the complete ordered flat
joint-turn artifact, including every request, effect declaration, and
presentation-root pin.

The 32-byte commitment's collision resistance remains an explicit security
event.  The byte-to-field cell codec must itself be injective; this is
particularly important in characteristic two, where `Nat.cast` would retain
only parity and is not a 16-bit cell codec.
-/

import Assurance.DeclaredHyperedgeReceipt
import Compiler.DeclaredHyperedgeArtifact

namespace Minidregg.Assurance.DeclaredHyperedgeHistoryBinding

open Minidregg.Kernel.DeclaredHyperedge
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CellState
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.DeclaredHyperedgeReceipt
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.DeclaredHyperedgeArtifact

set_option autoImplicit false

/-- A registered representation of one fixed 32-byte digest as sixteen field
cells.  For Tower fields this is a basis/packing map, never `Nat.cast`. -/
structure HeaderCellCodec (F : Type*) where
  encode : HeaderBytes.FixedBytes32 -> BindingIx -> F
  injective : Function.Injective encode

/-- The Lean-declared commitment interface.  Its implementation/suite is
selected by the clause controller; this record asserts no collision theorem. -/
structure JointHeaderCommitment where
  commit : AdmissionContext -> Header -> HeaderBytes.FixedBytes32

def JointHeaderCommitment.cells {F : Type*}
    (commitment : JointHeaderCommitment) (codec : HeaderCellCodec F)
    (context : AdmissionContext) (header : Header) : BindingIx -> F :=
  codec.encode (commitment.commit context header)

/-- The exact event which a commitment collision-resistance game must rule
out.  Keeping it data-specific avoids calling registry membership security. -/
def JointHeaderCommitment.Collision
    (commitment : JointHeaderCommitment)
    (context : AdmissionContext) (left right : Header) : Prop :=
  left ≠ right /\ commitment.commit context left = commitment.commit context right

theorem cells_equal_implies_commitment_equal
    {F : Type*} (commitment : JointHeaderCommitment)
    (codec : HeaderCellCodec F) (context : AdmissionContext)
    (left right : Header)
    (equal : commitment.cells codec context left =
      commitment.cells codec context right) :
    commitment.commit context left = commitment.commit context right :=
  codec.injective equal

theorem binding_alias_implies_equal_or_collision
    {F : Type*} (commitment : JointHeaderCommitment)
    (codec : HeaderCellCodec F) (context : AdmissionContext)
    (left right : Header)
    (equal : commitment.cells codec context left =
      commitment.cells codec context right) :
    left = right \/ commitment.Collision context left right := by
  by_cases same : left = right
  · exact Or.inl same
  · exact Or.inr ⟨same, cells_equal_implies_commitment_equal
      commitment codec context left right equal⟩

variable {portal : Portal}
variable {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
variable {Incidence : Type} [Fintype Incidence] [DecidableEq Incidence]

def jointHeader
    (declaration : Declaration portal materializer Incidence)
    (presentationRoot : Incidence -> Digest) : Header :=
  ofDeclaration declaration presentationRoot

/-- Canonical history claim for the complete joint declaration.  The state
core comes only from `execute`; the binding cells come only from the declared
context+header commitment and injective cell codec. -/
def historyClaim
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (presentationRoot : Incidence -> Digest)
    (commitment : JointHeaderCommitment)
    (codec : HeaderCellCodec F)
    (context : AdmissionContext) :
    BoundSemanticReceiptClaim n F :=
  DeclaredHyperedgeReceipt.historyClaim projection declaration model
    (fun admitted => commitment.cells codec admitted
      (jointHeader declaration presentationRoot)) context

@[simp] theorem historyClaim_binding_exact
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (presentationRoot : Incidence -> Digest)
    (commitment : JointHeaderCommitment)
    (codec : HeaderCellCodec F)
    (context : AdmissionContext) :
    (historyClaim projection declaration model presentationRoot commitment
      codec context).witness.binding =
      commitment.cells codec context
        (jointHeader declaration presentationRoot) := rfl

@[simp] theorem historyClaim_core_exact
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (model : BoundedModel declaration n F)
    (presentationRoot : Incidence -> Digest)
    (commitment : JointHeaderCommitment)
    (codec : HeaderCellCodec F)
    (context : AdmissionContext) :
    (historyClaim projection declaration model presentationRoot commitment
      codec context).witness.core =
      executeCore projection declaration model := rfl

/-- Equality of two accumulated joint-header bindings exposes precisely the
remaining cryptographic fork: the complete artifacts are equal, or the
selected header commitment collided. -/
theorem history_binding_equal_implies_headers_equal_or_collision
    {F : Type*} (commitment : JointHeaderCommitment)
    (codec : HeaderCellCodec F) (context : AdmissionContext)
    (left right : Header)
    (equal : commitment.cells codec context left =
      commitment.cells codec context right) :
    left = right \/ commitment.Collision context left right :=
  binding_alias_implies_equal_or_collision commitment codec context left right equal

#print axioms historyClaim_binding_exact
#print axioms historyClaim_core_exact
#print axioms history_binding_equal_implies_headers_equal_or_collision

end Minidregg.Assurance.DeclaredHyperedgeHistoryBinding
