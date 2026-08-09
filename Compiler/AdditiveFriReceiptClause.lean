/-
# Compiler.AdditiveFriReceiptClause -- manifest-bound additive-FRI receipt

This module packages the proved characteristic-two additive-FRI stack as one
Lean-owned receipt clause. It does not restate a verifier: acceptance is
exactly `Loom.AdditiveFriAdaptiveCoherentAccepts`, and the error bound is
exactly `Loom.additiveFriAdaptive_coherent_sampled_sound_UD`.

The clause binds the manifest declaration, reversed/high-coordinate-first LCH
basis order, affine domain, exact power-of-two domain sizes, degree/rate
schedule, adaptive roots-before-challenges strategy, coherent query count,
and terminal value. `AcceptedSample` contains proof data, never a native Bool.

Concrete commitment binding/CR, cSHAKE/ROM transport, and Lean validation of
returned arithmetic buffers remain explicit caller-supplied data. None is
postulated here or silently folded into the ideal interactive UD theorem.
-/

import Compiler.SemanticManifest
import Loom.AdditiveFriQuery

namespace Minidregg.Compiler.AdditiveFriReceiptClause

open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom

set_option autoImplicit false

universe uRoot uOp

noncomputable section

variable {F : Type} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
variable {ell m : Nat} {Root : Nat → Type uRoot} {Op : Nat → Type uOp}

/-- The basis order supported by the landed additive tower. Round zero folds
the highest input coordinate, then rounds proceed downward. -/
inductive BasisOrder where
  | reversedHighCoordinateFirst
deriving DecidableEq, Repr

/-- Roots at round `j` are fixed by the challenge prefix strictly preceding
`j`; in particular the initial root is fixed before every challenge. The
terminal root has no query-seed argument. -/
structure RootsBeforeChallengeSchedule
    (m : Nat)
    (S : ∀ n, BindingCommitment (Root n) F
      (AdditiveFriLevels ell n) (Op n))
    (st : FriAdaptiveTranscript S) : Prop where
  initialRootFixed : ∀ r r' : Fin m → F,
    st.rootAt r 0 (Nat.zero_le m) = st.rootAt r' 0 (Nat.zero_le m)
  roundRootPrefixBound : ∀ (j : Fin m) (r r' : Fin m → F),
    (∀ i : Fin m, (i : Nat) < (j : Nat) → r i = r' i) →
      st.rootAt r j (Nat.le_of_lt j.isLt) =
        st.rootAt r' j (Nat.le_of_lt j.isLt)

/-- `FriAdaptiveTranscript` itself proves roots-before-current-challenge. This
is a dependency theorem, not a Fiat--Shamir/ROM claim. -/
theorem rootsBeforeChallenge_of_adaptive
    (S : ∀ n, BindingCommitment (Root n) F
      (AdditiveFriLevels ell n) (Op n))
    (st : FriAdaptiveTranscript S) :
    RootsBeforeChallengeSchedule m S st := by
  constructor
  · intro r r'
    unfold FriAdaptiveTranscript.rootAt
    congr 1
    funext i
    exact i.elim0
  · intro j r r' hagree
    unfold FriAdaptiveTranscript.rootAt
    congr 1
    funext i
    exact hagree ⟨i, lt_of_lt_of_le i.isLt (Nat.le_of_lt j.isLt)⟩ i.isLt

/-- Manifest-shaped public additive-FRI clause. Type indices `ell` and `m`
are repeated as first-order fields so the statement codec must bind them. -/
structure Clause
    (manifest : Manifest)
    (S : ∀ n, BindingCommitment (Root n) F
      (AdditiveFriLevels ell n) (Op n)) where
  declaration : NativeClauseDecl
  manifestUnique : manifest.ClauseIdsUnique
  registered : manifest.lookupClause declaration.clauseId = some declaration
  controllerExact :
    declaration.verifierControllerDigest = manifest.transcriptControllerDigest

  domainLog : Nat
  domainLogExact : domainLog = ell
  rounds : Nat
  roundsExact : rounds = m
  roundsWithinDomain : rounds ≤ domainLog

  tower : AdditiveFriTower F ell m
  basis : Nat → F
  basisExact : basis = tower.beta
  offset : F
  offsetExact : offset = tower.offset
  basisOrder : BasisOrder
  basisOrderExact : basisOrder = .reversedHighCoordinateFirst

  domainSize : Nat → Nat
  domainSizeExact : ∀ n, n ≤ ell → domainSize n = 2 ^ (ell - n)
  degree : Nat → Nat
  degreeWithinDomain : ∀ n, n ≤ m → degree n ≤ domainSize n
  rate : Nat → Real
  rateExact : ∀ n, n ≤ m →
    rate n = (degree n : Real) / (domainSize n : Real)

  transcript : FriAdaptiveTranscript S
  rootSchedule : RootsBeforeChallengeSchedule m S transcript
  queryCount : Nat

  /-- The terminal coordinate and value depend on round challenges but have
  no query-seed argument. -/
  finalPoint : AdditiveFriLevels ell m
  finalValue : (Fin m → F) → F
  finalValueExact : ∀ challenges,
    finalValue challenges =
      transcript.wordAt challenges m le_rfl finalPoint

namespace Clause

variable {manifest : Manifest}
variable {S : ∀ n, BindingCommitment (Root n) F
  (AdditiveFriLevels ell n) (Op n)}

local notation "BoundClause" => Clause
  (F := F) (ell := ell) (m := m) (Root := Root) (Op := Op) manifest S

/-- The actual round basis selected by the clause's bound order. -/
def roundBasis (clause : BoundClause) (round : Nat) : F :=
  additiveReverseBasis ell clause.basis round

theorem roundBasis_exact (clause : BoundClause) (round : Nat) :
    clause.roundBasis round =
      additiveReverseBasis ell clause.tower.beta round := by
  simp [roundBasis, clause.basisExact]

/-- The manifest registry determines the declaration uniquely. -/
theorem declaration_unique (clause : BoundClause)
    {other : NativeClauseDecl}
    (found : manifest.lookupClause clause.declaration.clauseId = some other) :
    other = clause.declaration :=
  manifest.lookupClause_unique clause.manifestUnique found clause.registered

/-- The terminal value is fixed before coherent queries are selected. -/
theorem finalValue_bound (clause : BoundClause)
    (challenges : Fin m → F) :
    clause.finalValue challenges =
      clause.transcript.wordAt challenges m le_rfl clause.finalPoint :=
  clause.finalValueExact challenges

end Clause

/-! ## Local acceptance and global far-word soundness

The following propositions are parameters. A deployment supplies their
concrete meanings and proofs; this module does not define cSHAKE, a Merkle
hash, arithmetic semantics, or a Rust acceptance result.
-/

/-- Explicit deployment evidence kept beside, but outside, the ideal
interactive theorem. -/
structure ExternalPremises
    (CommitmentBindingLaw CshakeRomLaw ArithmeticBufferCheck : Prop) where
  commitmentBinding : CommitmentBindingLaw
  cshakeRom : CshakeRomLaw
  /-- Lean has checked the canonical arithmetic values returned across the
  untrusted compute boundary; this asserts no separate native semantics. -/
  arithmeticBufferChecked : ArithmeticBufferCheck

/-- Honest name for local evidence: this one challenge/query sample satisfies
the existing Lean additive-FRI predicate. It says nothing by itself about a
far initial word. -/
structure AcceptedSample
    {manifest : Manifest}
    {S : ∀ n, BindingCommitment (Root n) F
      (AdditiveFriLevels ell n) (Op n)}
    (clause : Clause (F := F) (ell := ell) (m := m)
      (Root := Root) (Op := Op) manifest S)
    (CommitmentBindingLaw CshakeRomLaw ArithmeticBufferCheck : Prop) where
  challenges : Fin m → F
  querySeed : Fin clause.queryCount → PowerTwoFriLevels ell 1
  accepted : AdditiveFriAdaptiveCoherentAccepts clause.tower S clause.degree
    clause.transcript clause.queryCount challenges querySeed
  terminalValueExact : clause.finalValue challenges =
    clause.transcript.wordAt challenges m le_rfl clause.finalPoint
  external : ExternalPremises CommitmentBindingLaw CshakeRomLaw
    ArithmeticBufferCheck

/-- A global soundness certificate for a far initial word. This is separate
from `AcceptedSample`: it exposes the exact UD theorem and does not mislabel a
bad-acceptance witness as a verified receipt. -/
structure FarWordSoundnessCertificate
    [Fintype F] [DecidableEq F]
    {manifest : Manifest}
    {S : ∀ n, BindingCommitment (Root n) F
      (AdditiveFriLevels ell n) (Op n)}
    (clause : Clause (F := F) (ell := ell) (m := m)
      (Root := Root) (Op := Op) manifest S)
    (radius : Nat → Real) (tau : Real) where
  tau_le_one : tau ≤ 1
  finalRadius_nonneg : 0 ≤ radius m
  radius_shrinks : ∀ j : Fin m, radius (j + 1) + tau ≤ radius j
  degree_halves : ∀ j : Fin m,
    clause.degree j = 2 * clause.degree (j + 1)
  foldedDegree_positive : ∀ j : Fin m, 0 < clause.degree (j + 1)
  roundRadius_positive : ∀ j : Fin m, 0 < radius j
  udBand : ∀ j : Fin m, radius j < 1 -
    (2 + (clause.degree (j + 1) : Real) /
      ((clause.tower.transversal j j.isLt).card : Real)) / 3
  initialFar : ¬ close (radius 0)
    (reedSolomonCode (clause.tower.dom 0) (clause.degree 0))
    (clause.transcript.word 0 (fun i => i.elim0))

  udError : uniformProb
      ((Fin m → F) ×
        (Fin clause.queryCount → PowerTwoFriLevels ell 1))
      (fun sample => AdditiveFriAdaptiveCoherentAccepts clause.tower S
        clause.degree clause.transcript clause.queryCount sample.1 sample.2) ≤
      (m : Real) * (2 ^ (ell - 1) : Nat) /
        (Fintype.card F : Real) + (1 - tau) ^ clause.queryCount

namespace AcceptedSample

variable {manifest : Manifest}
variable {S : ∀ n, BindingCommitment (Root n) F
  (AdditiveFriLevels ell n) (Op n)}
variable {CommitmentBindingLaw CshakeRomLaw ArithmeticBufferCheck : Prop}

local notation "BoundClause" => Clause
  (F := F) (ell := ell) (m := m) (Root := Root) (Op := Op) manifest S

/-- Build local acceptance evidence. No far-word statement or native verifier
result is an input. -/
def issue
    (clause : BoundClause)
    (challenges : Fin m → F)
    (querySeed : Fin clause.queryCount → PowerTwoFriLevels ell 1)
    (accepted : AdditiveFriAdaptiveCoherentAccepts clause.tower S clause.degree
      clause.transcript clause.queryCount challenges querySeed)
    (external : ExternalPremises CommitmentBindingLaw CshakeRomLaw
      ArithmeticBufferCheck) :
    AcceptedSample clause CommitmentBindingLaw CshakeRomLaw
      ArithmeticBufferCheck where
  challenges := challenges
  querySeed := querySeed
  accepted := accepted
  terminalValueExact := clause.finalValueExact challenges
  external := external

end AcceptedSample

namespace FarWordSoundnessCertificate

variable [Fintype F] [DecidableEq F]
variable {manifest : Manifest}
variable {S : ∀ n, BindingCommitment (Root n) F
  (AdditiveFriLevels ell n) (Op n)}
variable {radius : Nat → Real} {tau : Real}

local notation "BoundClause" => Clause
  (F := F) (ell := ell) (m := m) (Root := Root) (Op := Op) manifest S

/-- Package precisely the hypotheses and conclusion of the landed additive UD
theorem. -/
def certify
    (clause : BoundClause)
    (tau_le_one : tau ≤ 1)
    (finalRadius_nonneg : 0 ≤ radius m)
    (radius_shrinks : ∀ j : Fin m, radius (j + 1) + tau ≤ radius j)
    (degree_halves : ∀ j : Fin m,
      clause.degree j = 2 * clause.degree (j + 1))
    (foldedDegree_positive : ∀ j : Fin m, 0 < clause.degree (j + 1))
    (roundRadius_positive : ∀ j : Fin m, 0 < radius j)
    (udBand : ∀ j : Fin m, radius j < 1 -
      (2 + (clause.degree (j + 1) : Real) /
        ((clause.tower.transversal j j.isLt).card : Real)) / 3)
    (initialFar : ¬ close (radius 0)
      (reedSolomonCode (clause.tower.dom 0) (clause.degree 0))
      (clause.transcript.word 0 (fun i => i.elim0))) :
    FarWordSoundnessCertificate clause radius tau where
  tau_le_one := tau_le_one
  finalRadius_nonneg := finalRadius_nonneg
  radius_shrinks := radius_shrinks
  degree_halves := degree_halves
  foldedDegree_positive := foldedDegree_positive
  roundRadius_positive := roundRadius_positive
  udBand := udBand
  initialFar := initialFar
  udError := additiveFriAdaptive_coherent_sampled_sound_UD
    clause.tower S clause.degree clause.transcript radius clause.queryCount
    tau_le_one finalRadius_nonneg radius_shrinks degree_halves
    foldedDegree_positive roundRadius_positive udBand initialFar

/-- Named projection of the exact UD challenge/query error theorem. -/
theorem exact_ud_challenge_query_error
    {clause : BoundClause}
    (certificate : FarWordSoundnessCertificate clause radius tau) :
    uniformProb
      ((Fin m → F) ×
        (Fin clause.queryCount → PowerTwoFriLevels ell 1))
      (fun sample => AdditiveFriAdaptiveCoherentAccepts clause.tower S
        clause.degree clause.transcript clause.queryCount sample.1 sample.2) ≤
      (m : Real) * (2 ^ (ell - 1) : Nat) /
        (Fintype.card F : Real) + (1 - tau) ^ clause.queryCount :=
  certificate.udError

end FarWordSoundnessCertificate

#print axioms rootsBeforeChallenge_of_adaptive
#print axioms FarWordSoundnessCertificate.exact_ud_challenge_query_error

end

end Minidregg.Compiler.AdditiveFriReceiptClause
