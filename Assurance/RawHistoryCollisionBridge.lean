/-
# Assurance.RawHistoryCollisionBridge -- the retained attempt reaches the reduction

`RawHistoryBcsOpenings` keeps the adversary's unequal accepted column instead
of erasing it, and `equivocalTranscript_equivocation` shows that branch is
inhabited.  On its own that is a carrier with nowhere to go: a retained
`ColumnEquivocation` is only worth keeping if the landed Merkle reduction can
consume it.

This module connects them.  Any executable `CommitmentScheme` from the
authenticated-column vocabulary is an `OpeningScheme` with its binding field
absent, and a `ColumnEquivocation` over that opening scheme IS the
`BindingFailure` the reduction takes as input.  At the deployed Merkle
instantiation, `bindingFailure_implies_extractedCollision` then turns it into
an exact path-specific framed cSHAKE collision.

So the three-way split of `attribution_split` now has a real destination for
its middle branch: not "some binding assumption was violated", but a named
adversarial opening pair with two decoded depth-`k` paths to the same root and
different leaf values.

**The one residual, named.**  The Merkle collision extractor is stated at
`Domain = Fin (2 ^ k)`, while a retained-history transcript is indexed by
`ReceiptCoordinate n = Fin (Fintype.card (BoundReceiptIx n))`.
`bindingFailure_of_columnEquivocation` holds at any `Fin m` and therefore
already covers the receipt alphabet; `extractedCollision_of_columnEquivocation`
does not, because it needs `Fintype.card (BoundReceiptIx n)` to BE a power of
two.  Closing that gap is a padding embedding of the receipt coordinates,
exactly as `additiveFriLevelEquivPowerTwo` supplies on the additive side.  That
embedding is NOT built here, and no probability, collision-resistance, or ROM
claim is made anywhere in this file.
-/
import Assurance.RawHistoryBcsOpenings
import Compiler.Tower256CshakeMerkleBinding

namespace Minidregg.Assurance.RawHistoryCollisionBridge

open Minidregg.Assurance.RawHistoryBcsOpenings
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.Tower256CshakeMerkleBinding
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Loom
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

variable {Semantic Representation : Type} {m : Nat}
variable {port : ColumnPort Semantic Representation (Fin m)}

/-! ## An executable scheme is an opening scheme, minus the binding -/

/-- Forget everything except what the verifier runs.  The result is a Loom
`OpeningScheme`: `commit`, `openAt`, `verifyOpen`, completeness -- and no
binding field, because the executable Merkle checker does not have one. -/
def openingOf (scheme : CommitmentScheme port) :
    OpeningScheme Digest Representation (Fin m) (List UInt8) where
  commit := scheme.commit
  openAt := scheme.openAt
  verifyOpen root index value proof :=
    scheme.verifyOpening root index value proof = true
  verifyOpen_commit := fun column index => scheme.verifyOpening_commit column index

@[simp] theorem openingOf_commit (scheme : CommitmentScheme port)
    (column : Fin m -> Representation) :
    (openingOf scheme).commit column = scheme.commit column := rfl

@[simp] theorem openingOf_verifyOpen
    (scheme : CommitmentScheme port) (root : Digest) (index : Fin m)
    (value : Representation) (proof : List UInt8) :
    (openingOf scheme).verifyOpen root index value proof =
      (scheme.verifyOpening root index value proof = true) := rfl

/-- The two notions of position binding agree, so nothing is smuggled by the
forgetful map: a scheme that is binding as a `CommitmentScheme` is binding as
an `OpeningScheme` and conversely. -/
theorem positionBinding_iff (scheme : CommitmentScheme port) :
    scheme.PositionBinding ↔ (openingOf scheme).PositionBinding :=
  Iff.rfl

/-! ## A retained equivocation is a binding failure -/

/-- **The bridge.**  `Loom.ColumnEquivocation` over the forgetful opening
scheme is literally `BindingFailure` over the executable scheme -- both
openings accepted at the same root and coordinate, values unequal. -/
theorem bindingFailure_of_columnEquivocation (scheme : CommitmentScheme port)
    {t : Nat} {q : Fin t -> Fin m}
    {message : BcsMsg Digest Representation (List UInt8) t}
    {word : Fin m -> Representation}
    (equivocation : ColumnEquivocation (openingOf scheme) q message word) :
    ∃ (i : Fin t) (attempt : OpeningPair Representation (Fin m)),
      attempt.root = message.root ∧ attempt.index = q i ∧
        attempt.left = message.cols i ∧ attempt.right = word (q i) ∧
        BindingFailure scheme attempt := by
  obtain ⟨i, submitted, honest, unequal⟩ := equivocation
  exact ⟨i,
    { root := message.root
      index := q i
      left := message.cols i
      right := word (q i)
      leftProof := message.ops i
      rightProof := scheme.openAt word (q i) },
    rfl, rfl, rfl, rfl, submitted, honest, unequal⟩

/-! ## At the deployed Merkle instantiation, it extracts a collision -/

variable {cshake : Cshake256} {k : Nat}

/-- **The retained branch has a destination.**  At the concrete cSHAKE Merkle
scheme over a power-of-two domain, the binding failure a retained equivocation
exhibits yields the landed `ExtractedCollision`: two decoded depth-`k` paths
recomputing the same submitted root from different leaf values, plus the exact
framed leaf-or-node collision.

This is a reduction, not a bound.  It says where the failure goes, not how
often it happens; the probability of the extracted collision event remains the
explicit cSHAKE collision-resistance residual. -/
theorem extractedCollision_of_columnEquivocation
    (domains : MerkleDomains cshake)
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    {t : Nat} {q : Fin t -> Fin (2 ^ k)}
    {message : BcsMsg Digest Representation (List UInt8) t}
    {word : Fin (2 ^ k) -> Representation}
    (equivocation : ColumnEquivocation
      (openingOf (merkleCommitmentScheme domains port)) q message word) :
    ∃ (i : Fin t) (attempt : OpeningPair Representation (Fin (2 ^ k))),
      attempt.root = message.root ∧ attempt.index = q i ∧
        attempt.left = message.cols i ∧ attempt.right = word (q i) ∧
        ExtractedCollision domains port attempt := by
  obtain ⟨i, attempt, rootExact, indexExact, leftExact, rightExact, failure⟩ :=
    bindingFailure_of_columnEquivocation (merkleCommitmentScheme domains port)
      equivocation
  exact ⟨i, attempt, rootExact, indexExact, leftExact, rightExact,
    bindingFailure_implies_extractedCollision domains port attempt failure⟩

/-! ## Teeth: the bridge cannot fire where binding holds

If it could, the reduction would be manufacturing collisions out of a
collision-free hash, which would mean the equivocation carrier was wrong
rather than the scheme. -/

/-- Under the scheme's own position binding, no retained equivocation exists,
so this bridge is unreachable exactly where it should be. -/
theorem no_columnEquivocation_of_positionBinding (scheme : CommitmentScheme port)
    (binding : scheme.PositionBinding)
    {t : Nat} {q : Fin t -> Fin m}
    {message : BcsMsg Digest Representation (List UInt8) t}
    {word : Fin m -> Representation} :
    ¬ColumnEquivocation (openingOf scheme) q message word := by
  rintro ⟨j, submitted, honest, unequal⟩
  exact unequal (binding message.root (q j) (message.cols j) (word (q j))
    (message.ops j) (scheme.openAt word (q j)) submitted honest)

/-- And Merkle collision-freedom is exactly what would supply that binding, so
the two halves of the reduction meet where the landed development already put
them: `positionBinding_of_merkleCollisionFree` on one side, this bridge on the
other. -/
theorem no_columnEquivocation_of_merkleCollisionFree
    (domains : MerkleDomains cshake)
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    (collisionFree : MerkleCollisionFree domains port.representationCodec)
    {t : Nat} {q : Fin t -> Fin (2 ^ k)}
    {message : BcsMsg Digest Representation (List UInt8) t}
    {word : Fin (2 ^ k) -> Representation} :
    ¬ColumnEquivocation (openingOf (merkleCommitmentScheme domains port)) q
      message word :=
  no_columnEquivocation_of_positionBinding _
    (positionBinding_of_merkleCollisionFree domains port collisionFree)

#print axioms positionBinding_iff
#print axioms bindingFailure_of_columnEquivocation
#print axioms extractedCollision_of_columnEquivocation
#print axioms no_columnEquivocation_of_positionBinding
#print axioms no_columnEquivocation_of_merkleCollisionFree

end

end Minidregg.Assurance.RawHistoryCollisionBridge
