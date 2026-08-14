/-
# Assurance.Tower256AdditiveFriControllerAdmission -- ⚑ RETRACTED, VACUOUS

⚑ **RETRACTED 2026-08-14.  Every declaration below is quantified over
`pcs : MerklePcs ell`, and `Tower256MerkleCardinalityCore.merklePcs_empty_of_positive`
proves that carrier EMPTY for every `0 < ell`.**  So each theorem here holds
vacuously at every height that folds; none of them says anything.  The
retraction is machine-checked at the bottom of this file
(`admission_vacuous_of_positive_height`, `commonGameFamily_impossible`), not
asserted in prose.

Why the carrier is empty: `MerklePcs` demands *unconditional* position binding
from a concrete cSHAKE256 Merkle commitment.  Binding plus completeness makes
the whole-word commitment injective, but the root is 256 bits while a
positive-height Tower256 column has more than `2 ^ 256` words.  Pigeonhole.

⚑ Height zero is not a rescue: it performs no folds, and the carrier census
reports `MerklePcs` with no witness at any height.  There is no `ell` at which
this module is known to say something.

**The honest replacement is the raw (non-binding-closed) path**, which retains
extracted collision events with an explicit CR price instead of postulating an
injective finite hash:
`Assurance.Tower256AdditiveFriRawAdmission` and
`Assurance.Tower256AdditiveFriCanonicalExecutionGame`, both over
`RawMerklePcs`.  New work goes there.

This file is retained only because `Assurance.SemanticHistoryTower256CheckpointGame`
and `Assurance.Tower256AdditiveFriActualReduction` still build on it, and both
are retracted for the same reason; deleting the three together is the follow-up.

---

Original module note (describes what the declarations WOULD have meant on an
inhabited carrier):

The concrete Tower256 additive-FRI controller returns an exact ideal clause
acceptance theorem, but computational soundness still has to live in the same
game as commitment binding and Fiat--Shamir transport.  This module performs
that join without inventing any cryptography:

* one `ProofCompositionGame.SecurityGame` coin selects the controller
  execution, round transcript, and every priced failure event;
* successful controller bytes become `AcceptedSample` through the exact
  decoder/checker theorem, with no native proposition in the path;
* the common schedule's challenges and root prefixes are tied to that exact
  accepted receipt; and
* the still-missing deployment theorem is isolated as one pointwise cover:
  false controller acceptance must expose additive proximity failure, a
  concrete commitment collision/binding failure, or oracle transport failure.

That cover is the minimal PCS/ROM reduction residual.  Once supplied, the
existing common-game union bound applies without an independence assumption.
-/

import Assurance.ProofCompositionGame
import Assurance.Tower256MerkleCardinalityCore
import Compiler.Tower256AdditiveFriController

namespace Minidregg.Assurance.Tower256AdditiveFriControllerAdmission

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

variable {ell m queryCount : Nat}
variable {manifest : Manifest}
variable {pcs : MerklePcs ell}
variable {clause : FriClause pcs m manifest}
variable {verifier : Verifier (queryCount := queryCount) pcs clause}

/-! ## One accepted receipt on one common game coin -/

/-- Deterministic evidence retained at the native boundary.  It is assigned no
probability price: these are the exact bytes, Lean decode, and reflected Lean
acceptance already carried by `AcceptedReceipt`. -/
def ArithmeticBytesChecked (request : List UInt8)
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request) : Prop :=
  verifier.proofCodec.decode reply.proofBytes = some reply.receipt ∧
    Accepts pcs clause verifier.pins reply.receipt

theorem arithmeticBytesChecked (request : List UInt8)
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request) :
    ArithmeticBytesChecked request reply :=
  ⟨reply.decoded, reply.accepted⟩

/-- Security judgments for this exact accepted receipt, all drawn from one
`FailureLedger` and one coin.  `additiveProximity` is retained even though a
single accepted sample needs only binding/ROM external evidence: it is the
event which prices false low-degree acceptance in the game reduction below. -/
structure CommonCoinAdmission
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    (request : List UInt8)
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request) : Prop where
  commitmentBinding : ledger.Good .commitmentBinding omega
  oracleTransport : ledger.Good .oracleTransport omega
  additiveProximity : ledger.Good .additiveProximity omega

namespace CommonCoinAdmission

variable {Omega : Type} [Fintype Omega]
variable {ledger : FailureLedger Omega} {omega : Omega}
variable {request : List UInt8}
variable {reply : AcceptedReceipt (queryCount := queryCount)
  pcs clause verifier request}

/-- The exact controller result becomes the existing manifest-bound local
sample.  The query seed is obtained only from the controller's theorem, whose
acceptance relation already proves `queryCount = clause.queryCount`. -/
def acceptedSample
    (admission : CommonCoinAdmission ledger omega request reply) :
    AcceptedSample clause
      (ledger.Good .commitmentBinding omega)
      (ledger.Good .oracleTransport omega)
      (ArithmeticBytesChecked request reply) := by
  let result := accepts_additiveFriAdaptiveCoherentAccepts pcs clause
    verifier.pins reply.receipt reply.accepted
  let querySeed := Classical.choose result
  have accepted := Classical.choose_spec result
  exact AcceptedSample.issue clause reply.receipt.challenges querySeed accepted
    (additiveExternalPremises ledger omega admission.commitmentBinding
      admission.oracleTransport (arithmeticBytesChecked request reply))

theorem acceptedSample_rootSchedule
    (_admission : CommonCoinAdmission ledger omega request reply) :
    RootsBeforeChallengeSchedule m pcs.commitment clause.transcript :=
  clause.rootSchedule

end CommonCoinAdmission

/-! ## Exact common-game family and the minimal reduction residual -/

/-- Controller roots available before round `j`, in the same order used by
the concrete challenge framing. -/
def rootsBefore (receipt : Receipt ell m queryCount) (j : Fin m) : List Digest :=
  List.ofFn fun n : Fin ((j : Nat) + 1) =>
    have hn : (n : Nat) ≤ m := by omega
    clause.transcript.rootAt receipt.challenges n hn

/-- A family of byte-checked controller executions indexed by one finite game
coin.  `execution = none` includes native error, invalid encoding, and Lean
rejection.  The shared schedule is not a second transcript: its challenge and
root-prefix fields are proved equal to the accepted controller receipt.

`failureCover` is intentionally the one hard field.  It must be supplied by a
real commitment/ROM/proximity reduction; this structure cannot be inhabited by
an unrelated bound on another coin space. -/
structure CommonGameFamily
    (Omega : Type) [Fintype Omega]
    (Error : Type) (request : List UInt8) where
  ledger : FailureLedger Omega
  schedule : SharedOracleSchedule Omega Digest (List UInt8)
    Tower256 Digest m
  execution : Omega → Option
    (AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request)
  runner : Omega → OpaqueProofRunner Error
  executionExact : ∀ omega reply,
    execution omega = some reply →
      run (queryCount := queryCount) pcs clause verifier
        (runner omega) request = .ok reply
  /-- The exact false statement predicate selected by the application (for
  example the `initialFar` field of `FarWordSoundnessCertificate`). -/
  falseStatement : Receipt ell m queryCount → Prop
  scheduleChallengesExact : ∀ omega reply,
    execution omega = some reply →
      schedule.challenges omega = reply.receipt.challenges
  scheduleRootsExact : ∀ omega reply,
    execution omega = some reply → ∀ j : Fin m,
      schedule.rootsAt (j : Nat)
          (challengePrefix (schedule.challenges omega) j) =
        rootsBefore (clause := clause) reply.receipt j
  scheduleDomainExact : ∀ j,
    schedule.domainFor (schedule.phase j) =
      verifier.pins.challengeDomainId
  /-- **The exact remaining theorem.** A false accepting controller execution
  on this same coin exposes one of the three real additive PCS failure events. -/
  failureCover : ∀ omega reply,
    execution omega = some reply → falseStatement reply.receipt →
      (ledger .additiveProximity).event omega ∨
      (ledger .commitmentBinding).event omega ∨
      (ledger .oracleTransport).event omega

namespace CommonGameFamily

variable {Omega : Type} [Fintype Omega]
variable {Error : Type}
variable {request : List UInt8}

/-- False acceptance by the exact byte controller. -/
def FalseAccept
    (family : CommonGameFamily (pcs := pcs) (clause := clause)
      (verifier := verifier) Omega Error request) (omega : Omega) : Prop :=
  ∃ reply, family.execution omega = some reply ∧
    family.falseStatement reply.receipt

/-- A selected common-game execution retains the exact byte string returned
by that coin's arbitrary native runner. -/
theorem execution_runner_bytes
    (family : CommonGameFamily (pcs := pcs) (clause := clause)
      (verifier := verifier) Omega Error request)
    {omega : Omega}
    {reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request}
    (selected : family.execution omega = some reply) :
    family.runner omega request = .ok reply.proofBytes :=
  run_success_runner_bytes (queryCount := queryCount) pcs clause verifier
    (family.runner omega) request reply
    (family.executionExact omega reply selected)

/-- The exact three-event cover embeds in the exhaustive shared ledger. -/
theorem falseAccept_bad
    (family : CommonGameFamily (pcs := pcs) (clause := clause)
      (verifier := verifier) Omega Error request)
    (omega : Omega) (accepted : family.FalseAccept omega) :
    family.ledger.Bad omega := by
  obtain ⟨reply, execution, falseStatement⟩ := accepted
  rcases family.failureCover omega reply execution falseStatement with
    proximity | binding | transport
  · exact Or.inr (Or.inr (Or.inr (Or.inl proximity)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl binding))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl transport)))))

/-- The controller family is literally an instance of the repository's one
common proof-composition game, not a sum of bounds over separate spaces. -/
def securityGame
    (family : CommonGameFamily (pcs := pcs) (clause := clause)
      (verifier := verifier) Omega Error request) :
    SecurityGame Omega Digest (List UInt8) Tower256 Digest m where
  transcript := family.schedule
  ledger := family.ledger
  falseAccept := family.FalseAccept
  failureCover := family.falseAccept_bad

/-- End-to-end common-game price.  No independence premise occurs. -/
theorem falseAccept_le
    (family : CommonGameFamily (pcs := pcs) (clause := clause)
      (verifier := verifier) Omega Error request) :
    uniformProb Omega family.FalseAccept ≤ family.ledger.total :=
  family.securityGame.falseAccept_le

/-- Outside the exhaustive ledger's bad event, this exact controller cannot
falsely accept. -/
theorem falseAccept_impossible_of_all_good
    (family : CommonGameFamily (pcs := pcs) (clause := clause)
      (verifier := verifier) Omega Error request)
    {omega : Omega}
    (good : ∀ failure, family.ledger.Good failure omega) :
    ¬family.FalseAccept omega :=
  family.securityGame.falseAccept_impossible_of_all_good good

end CommonGameFamily

/-! ## ⚑ The retraction, machine-checked

Everything above is quantified over `pcs : MerklePcs ell`.  The two theorems
below are the retraction: at any height that folds, the carrier is empty, so
each preceding declaration is vacuously true and asserts nothing.  They are
stated here, in the file they retract, rather than in a downstream note — the
cardinality argument was moved into `Assurance.Tower256MerkleCardinalityCore`
precisely so this import is possible without a cycle. -/

/-- **Retraction.**  Hand me the `pcs` this module quantifies over together
with a height that folds, and I hand you `False`.  Every theorem in this file
is therefore vacuous at every positive height. -/
theorem admission_vacuous_of_positive_height
    (thePcs : MerklePcs ell) (positive : 0 < ell) : False :=
  Tower256MerkleCardinalityCore.merklePcs_empty_of_positive positive ⟨thePcs⟩

/-- **Retraction, at the load-bearing carrier.**  The `failureCover` field of
`CommonGameFamily` is advertised above as "the one hard field", the exact
remaining PCS/ROM reduction.  At positive height nobody has to supply it: the
whole family is impossible, so its obligation was never a real one. -/
theorem commonGameFamily_impossible
    {Omega : Type} [Fintype Omega] {Error : Type} {request : List UInt8}
    (positive : 0 < ell)
    (_family : CommonGameFamily (pcs := pcs) (clause := clause)
      (verifier := verifier) Omega Error request) : False :=
  admission_vacuous_of_positive_height pcs positive

/-- info: 'Minidregg.Assurance.Tower256AdditiveFriControllerAdmission.admission_vacuous_of_positive_height' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admission_vacuous_of_positive_height
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriControllerAdmission.commonGameFamily_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commonGameFamily_impossible

/-- info: 'Minidregg.Assurance.Tower256AdditiveFriControllerAdmission.CommonCoinAdmission.acceptedSample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CommonCoinAdmission.acceptedSample
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriControllerAdmission.CommonGameFamily.falseAccept_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CommonGameFamily.falseAccept_bad
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriControllerAdmission.CommonGameFamily.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CommonGameFamily.falseAccept_le

end


end Minidregg.Assurance.Tower256AdditiveFriControllerAdmission
