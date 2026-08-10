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

The Merkle collision extractor is stated at `Domain = Fin (2 ^ k)`, while a
retained-history transcript is indexed by
`ReceiptCoordinate n = Fin (Fintype.card (BoundReceiptIx n))`, whatever
cardinal the receipt binding happens to have.  `PowerTwoCover` closes that in
the deployment direction rather than by assuming the cardinal cooperates: the
tree really does live over a power-of-two leaf domain, the receipt alphabet is
its prefix, and the receipt-alphabet checker is the deployed checker
`restrict`ed.  `extractedCollision_of_restricted_equivocation` then reaches the
extractor from any alphabet size.

**What is still not claimed anywhere in this file:** that any particular
`MerkleDomains`/`ColumnPort` pair is the deployed one, that the extracted
collision event is improbable, or that cSHAKE realizes a random oracle.  These
are reductions.  The price is not here.
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

/-! ## Closing the power-of-two gap

The extractor above wants `Fin (2 ^ k)`; a retained-history transcript is
indexed by `Fin (Fintype.card (BoundReceiptIx n))`, which is whatever cardinal
the receipt binding happens to have.  The deployment direction is the honest
one: the Merkle tree really does live over a power-of-two leaf domain, and the
receipt alphabet is a PREFIX of it.  So the receipt-alphabet checker is not a
separate scheme to be related to the deployed one -- it is the deployed one,
restricted. -/

/-- A power-of-two leaf domain covering the alphabet, plus the filler symbol
the unused leaves carry.  Both are deployment data, not assumptions. -/
structure PowerTwoCover (m : Nat) (Representation : Type) where
  exponent : Nat
  covers : m ≤ 2 ^ exponent
  filler : Representation

namespace PowerTwoCover

variable (cover : PowerTwoCover m Representation)

/-- The alphabet sits in the leaf domain as its prefix. -/
def leaf (index : Fin m) : Fin (2 ^ cover.exponent) :=
  ⟨index.val, lt_of_lt_of_le index.isLt cover.covers⟩

theorem leaf_injective : Function.Injective cover.leaf := by
  intro left right equal
  simpa only [leaf, Fin.ext_iff] using equal

/-- Extend a word over the alphabet to the whole leaf domain by filling the
unused leaves.  The tree commits this; nothing about the semantic word
changes. -/
def padWord (word : Fin m -> Representation) :
    Fin (2 ^ cover.exponent) -> Representation :=
  fun index => if inside : index.val < m then word ⟨index.val, inside⟩ else cover.filler

@[simp] theorem padWord_leaf (word : Fin m -> Representation) (index : Fin m) :
    cover.padWord word (cover.leaf index) = word index := by
  simp only [padWord, leaf, index.isLt, dif_pos]

/-- **The receipt-alphabet checker is the deployed one, restricted.**  Commit
the padded word, open at the corresponding leaf, verify at that leaf.  No
binding field appears, so a retained equivocation over this view is still a
retained equivocation. -/
def restrict
    {leafPort : ColumnPort Semantic Representation (Fin (2 ^ cover.exponent))}
    (scheme : CommitmentScheme leafPort) :
    OpeningScheme Digest Representation (Fin m) (List UInt8) where
  commit word := scheme.commit (cover.padWord word)
  openAt word index := scheme.openAt (cover.padWord word) (cover.leaf index)
  verifyOpen root index value proof :=
    scheme.verifyOpening root (cover.leaf index) value proof = true
  verifyOpen_commit := by
    intro word index
    simpa only [padWord_leaf] using
      scheme.verifyOpening_commit (cover.padWord word) (cover.leaf index)

/-- A retained equivocation over the restricted view is literally one over the
leaf domain, at the corresponding leaf coordinates and the padded word. -/
theorem columnEquivocation_leaf
    {leafPort : ColumnPort Semantic Representation (Fin (2 ^ cover.exponent))}
    (scheme : CommitmentScheme leafPort)
    {t : Nat} {q : Fin t -> Fin m}
    {message : BcsMsg Digest Representation (List UInt8) t}
    {word : Fin m -> Representation}
    (equivocation : ColumnEquivocation (cover.restrict scheme) q message word) :
    ColumnEquivocation (openingOf scheme) (cover.leaf ∘ q) message
      (cover.padWord word) := by
  obtain ⟨i, submitted, honest, unequal⟩ := equivocation
  refine ⟨i, submitted, ?_, ?_⟩
  · simpa only [Function.comp_apply, padWord_leaf] using honest
  · simpa only [Function.comp_apply, padWord_leaf] using unequal

end PowerTwoCover

/-- **The residual is closed.**  A retained equivocation at the receipt
alphabet -- any cardinality -- reaches the landed Merkle extractor through the
cover, yielding the exact framed cSHAKE collision at a named query coordinate.

What is still not claimed: that any particular `MerkleDomains`/`ColumnPort`
pair is the deployed one, that the collision event is improbable, or that
cSHAKE realizes a random oracle. This is the reduction; the price is not. -/
theorem extractedCollision_of_restricted_equivocation
    (cover : PowerTwoCover m Representation)
    (domains : MerkleDomains cshake)
    (port : ColumnPort Semantic Representation (Fin (2 ^ cover.exponent)))
    {t : Nat} {q : Fin t -> Fin m}
    {message : BcsMsg Digest Representation (List UInt8) t}
    {word : Fin m -> Representation}
    (equivocation : ColumnEquivocation
      (cover.restrict (merkleCommitmentScheme domains port)) q message word) :
    ∃ (i : Fin t) (attempt : OpeningPair Representation (Fin (2 ^ cover.exponent))),
      attempt.root = message.root ∧ attempt.index = cover.leaf (q i) ∧
        attempt.left = message.cols i ∧
        attempt.right = cover.padWord word (cover.leaf (q i)) ∧
        ExtractedCollision domains port attempt :=
  extractedCollision_of_columnEquivocation domains port
    (cover.columnEquivocation_leaf (merkleCommitmentScheme domains port)
      equivocation)

/-- And the restricted view inherits the same teeth: where the deployed tree is
collision-free, the receipt alphabet admits no retained equivocation either, so
closing the gap did not open a hole. -/
theorem no_restricted_columnEquivocation_of_merkleCollisionFree
    (cover : PowerTwoCover m Representation)
    (domains : MerkleDomains cshake)
    (port : ColumnPort Semantic Representation (Fin (2 ^ cover.exponent)))
    (collisionFree : MerkleCollisionFree domains port.representationCodec)
    {t : Nat} {q : Fin t -> Fin m}
    {message : BcsMsg Digest Representation (List UInt8) t}
    {word : Fin m -> Representation} :
    ¬ColumnEquivocation (cover.restrict (merkleCommitmentScheme domains port)) q
      message word := fun equivocation =>
  no_columnEquivocation_of_merkleCollisionFree domains port collisionFree
    (cover.columnEquivocation_leaf (merkleCommitmentScheme domains port)
      equivocation)

#print axioms positionBinding_iff
#print axioms bindingFailure_of_columnEquivocation
#print axioms extractedCollision_of_columnEquivocation
#print axioms no_columnEquivocation_of_positionBinding
#print axioms no_columnEquivocation_of_merkleCollisionFree
#print axioms PowerTwoCover.padWord_leaf
#print axioms PowerTwoCover.columnEquivocation_leaf
#print axioms extractedCollision_of_restricted_equivocation
#print axioms no_restricted_columnEquivocation_of_merkleCollisionFree

end

end Minidregg.Assurance.RawHistoryCollisionBridge
