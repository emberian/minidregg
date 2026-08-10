/-
# Compiler.Tower256AdditiveFriController -- byte-only additive-FRI verification

This module closes the deterministic controller seam between the manifest-bound
additive-FRI clause and the concrete Tower256/cSHAKE/Merkle backend.

* every level commitment is the backend's actual perfect binary Merkle tree,
  reindexed by the proved little-endian additive-coordinate equivalence;
* the backend is pinned to Lean's recursive Fan--Paar Tower256 codec and the
  executable SP 800-185 cSHAKE256 implementation;
* round challenges and coherent query seeds are derived in Lean from the
  public statement and roots which are available before the corresponding
  draw;
* an arbitrary native runner returns only bytes or an opaque error;
* Lean decodes those bytes, authenticates every low/high/next opening, checks
  every additive fold equation, and checks an explicit final polynomial; and
* successful execution implies exactly `AdditiveFriAdaptiveCoherentAccepts`.

Merkle position binding is retained as the exact property needed to construct
Loom's `BindingCommitment`.  `Tower256CshakeMerkleBinding` reduces that
property to concrete framed cSHAKE collisions; the probabilistic collision,
ROM, and proximity reductions remain outside this deterministic verifier.
There is no Rust proposition or Rust field semantics in this module.
-/

import Compiler.AdditiveFriReceiptClause
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Compiler.Tower256AdditiveFriController

open Polynomial
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Loom
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

abbrev Tower256 := BinaryTower256Profile.Tower256

noncomputable section

/-! ## The exact Merkle PCS family -/

/-- First-order metadata and the exact finite-index codec for one FRI level. -/
structure LevelSpec (backend : Backend Tower256) (ell level : Nat) where
  role : ColumnRole
  roleExact : role = .checkpoint
  slotId : Digest
  semanticTypeId : Digest
  domainId : Digest
  domainCodecPin : CodecPin
  domainCodec : LawfulCodec (PowerTwoFriLevels ell level)

namespace LevelSpec

variable {backend : Backend Tower256} {ell level : Nat}

def port (spec : LevelSpec backend ell level) :
    ColumnPort Tower256 Tower256 (PowerTwoFriLevels ell level) :=
  backend.towerPort spec.role spec.slotId spec.semanticTypeId spec.domainId
    spec.domainCodecPin spec.domainCodec

def scheme (spec : LevelSpec backend ell level) : CommitmentScheme spec.port :=
  backend.additiveMerkleScheme spec.role spec.slotId spec.semanticTypeId
    spec.domainId spec.domainCodecPin spec.domainCodec

end LevelSpec

/-- One backend-selected Merkle family for every additive-FRI level.  The two
profile equalities rule out swapping either field coordinates or the hash
function while retaining this object.  `positionBinding` is the exact
cryptographic residual, not a completeness-derived theorem. -/
structure MerklePcs (ell : Nat) where
  backend : Backend Tower256
  towerExact : backend.tower = BinaryTower256Profile.profile
  cshakeAlgorithmId : Digest
  cshakeDigestCodecPin : CodecPin
  cshakeExact : backend.cshake =
    Sp800185Cshake256.controller cshakeAlgorithmId cshakeDigestCodecPin
  level : (n : Nat) → LevelSpec backend ell n
  positionBinding : ∀ n, (level n).scheme.PositionBinding

/-- Specialize the additive PCS family to the repository's single shared
concrete Tower256 backend.  Only proof-suite level metadata and the exact
position-binding theorem remain arguments. -/
def MerklePcs.ofConcrete
    {ell : Nat}
    (level : (n : Nat) → LevelSpec
      Tower256ConcreteBackend.backend ell n)
    (positionBinding : ∀ n, (level n).scheme.PositionBinding) :
    MerklePcs ell where
  backend := Tower256ConcreteBackend.backend
  towerExact := Tower256ConcreteBackend.towerExact
  cshakeAlgorithmId := Tower256ConcreteBackend.cshakeAlgorithmId
  cshakeDigestCodecPin := Tower256ConcreteBackend.digestCodecPin
  cshakeExact := Tower256ConcreteBackend.cshakeExact
  level := level
  positionBinding := positionBinding

namespace MerklePcs

variable {ell : Nat} (pcs : MerklePcs ell)

/-- The concrete finite-index binding commitment at level `n`. -/
def finiteCommitment (n : Nat) :
    BindingCommitment Digest Tower256 (PowerTwoFriLevels ell n) (List UInt8) :=
  (bindingMerkleCommitmentScheme pcs.backend.merkle (pcs.level n).port
    (pcs.positionBinding n)).toLoom

/-- Reindex the concrete tree from its little-endian integer address to the
literal additive bit-vector coordinate used by `AdditiveFriTower`.  The root,
opening bytes, and executable opening checker are unchanged. -/
def commitment (n : Nat) :
    BindingCommitment Digest Tower256 (AdditiveFriLevels ell n) (List UInt8) where
  commit word := (pcs.finiteCommitment n).commit fun index =>
    word ((additiveFriLevelEquivPowerTwo ell n).symm index)
  openAt word coordinate := (pcs.finiteCommitment n).openAt
    (fun index => word ((additiveFriLevelEquivPowerTwo ell n).symm index))
    (additiveFriLevelEquivPowerTwo ell n coordinate)
  verifyOpen root coordinate value proof :=
    (pcs.finiteCommitment n).verifyOpen root
      (additiveFriLevelEquivPowerTwo ell n coordinate) value proof
  verifyOpen_commit := by
    intro word coordinate
    simpa using (pcs.finiteCommitment n).verifyOpen_commit
      (fun index => word ((additiveFriLevelEquivPowerTwo ell n).symm index))
      (additiveFriLevelEquivPowerTwo ell n coordinate)
  binding := by
    intro root coordinate left right leftProof rightProof hleft hright
    exact (pcs.finiteCommitment n).binding root
      (additiveFriLevelEquivPowerTwo ell n coordinate)
      left right leftProof rightProof hleft hright

@[simp] theorem commitment_commit (n : Nat)
    (word : AdditiveFriLevels ell n → Tower256) :
    (pcs.commitment n).commit word =
      (pcs.finiteCommitment n).commit (fun index =>
        word ((additiveFriLevelEquivPowerTwo ell n).symm index)) :=
  rfl

/-- The value codec at every level is literally the canonical recursive
Fan--Paar codec selected by Lean. -/
theorem valueCodecExact (n : Nat) :
    (pcs.level n).port.representationCodec =
      Minidregg.Theory.BinaryTowerCodec.codec := by
  change pcs.backend.tower.valueCodec = _
  rw [pcs.towerExact]
  exact BinaryTower256Profile.profile_codec_exact

/-- The hash used by every level commitment is the concrete Lean cSHAKE256
function, not a caller-supplied native hash identifier. -/
theorem xofExact : pcs.backend.cshake.xofDigest =
    (Sp800185Cshake256.controller pcs.cshakeAlgorithmId
      pcs.cshakeDigestCodecPin).xofDigest := by
  rw [pcs.cshakeExact]

end MerklePcs

/-! ## Lean-owned transcript derivation -/

/-- Interpret a digest as the canonical little-endian Tower256 coordinate.
The modulo makes the function total on the legacy unbounded `Digest` wrapper;
the concrete cSHAKE range is already strictly below `2^256`. -/
def digestTower (digest : Digest) : Tower256 :=
  Minidregg.Theory.BinaryTowerFanPaarCodec.ofFin
    ⟨digest.value % (2 ^ 256), Nat.mod_lt _ (by positivity)⟩

/-- A receipt is semantic proof data only after a Lean-owned `LawfulCodec`
decodes the native byte string.  It carries no verdict.  The opening paths are
the exact bytes consumed by the concrete Merkle checker. -/
structure Receipt (ell m queryCount : Nat) where
  challenges : Fin m → Tower256
  querySeed : Fin queryCount → PowerTwoFriLevels ell 1
  opening : (j : Fin m) → Fin queryCount →
    FriQueryOpening Tower256 (List UInt8) (List UInt8)
  finalPolynomial : Polynomial Tower256

variable {ell m queryCount : Nat}
variable {manifest : Manifest}
variable (pcs : MerklePcs ell)

abbrev FriClause (pcs : MerklePcs ell) (m : Nat) (manifest : Manifest) := Clause
  (F := Tower256) (ell := ell) (m := m)
  (Root := fun _ => Digest) (Op := fun _ => List UInt8)
  manifest pcs.commitment

/-- Public transcript pins.  The statement bytes must include the complete
manifest/clause statement encoding selected by the artifact.  Separate
customization strings prevent challenge and query draws from sharing a cSHAKE
namespace. -/
structure TranscriptPins where
  statementBytes : List UInt8
  challengeDomainId : Digest
  queryDomainId : Digest
  domainIdsDistinct : challengeDomainId ≠ queryDomainId
  challengeCustomization : List UInt8
  queryCustomization : List UInt8
  customizationsDistinct : challengeCustomization ≠ queryCustomization

/-- The exact prefix supplied to challenge `j`: the public statement followed
by roots `0 .. j`, each computed from a word which depends only on challenges
strictly before that level. -/
def challengeInput (clause : FriClause pcs m manifest) (pins : TranscriptPins)
    (receipt : Receipt ell m queryCount) (j : Fin m) : List UInt8 :=
  envelope pins.statementBytes ++
    (List.ofFn fun n : Fin ((j : Nat) + 1) =>
      have hn : (n : Nat) ≤ m := by omega
      let root := clause.transcript.rootAt receipt.challenges n hn
      envelope (encodeLength n) ++
        envelope (pcs.backend.cshake.digestCodec.encode root)).flatten

/-- Lean's round challenge derived from the exact root prefix. -/
def derivedChallenge (clause : FriClause pcs m manifest) (pins : TranscriptPins)
    (receipt : Receipt ell m queryCount) (j : Fin m) : Tower256 :=
  digestTower (pcs.backend.cshake.xofDigest pins.challengeCustomization
    (challengeInput pcs clause pins receipt j))

/-- The post-challenge transcript bound before query sampling: statement,
all level roots through `m`, and the canonical Tower256 challenge encodings. -/
def queryPrefix (clause : FriClause pcs m manifest) (pins : TranscriptPins)
    (receipt : Receipt ell m queryCount) : List UInt8 :=
  envelope pins.statementBytes ++
    (List.ofFn fun n : Fin (m + 1) =>
      have hn : (n : Nat) ≤ m := by omega
      envelope (encodeLength n) ++ envelope
        (pcs.backend.cshake.digestCodec.encode
          (clause.transcript.rootAt receipt.challenges n hn))).flatten ++
    (List.ofFn receipt.challenges).flatMap fun challenge =>
      envelope (BinaryTower256Profile.profile.valueCodec.encode challenge)

/-- One coherent path seed drawn from the exact post-challenge transcript.
The low `ell-1` bits select the canonical power-of-two seed coordinate. -/
def derivedQuerySeed (clause : FriClause pcs m manifest) (pins : TranscriptPins)
    (receipt : Receipt ell m queryCount) (a : Fin queryCount) :
    PowerTwoFriLevels ell 1 :=
  let digest := pcs.backend.cshake.xofDigest pins.queryCustomization
    (queryPrefix pcs clause pins receipt ++ envelope (encodeLength a))
  ⟨digest.value % (2 ^ (ell - 1)), Nat.mod_lt _ (by positivity)⟩

/-- Every root included in challenge `j` is independent of challenge `j`
itself.  This is the executable framing counterpart of the clause's
prefix-typed schedule theorem. -/
theorem challengeInput_eq_of_samePrefix
    (clause : FriClause pcs m manifest) (pins : TranscriptPins)
    (left right : Receipt ell m queryCount) (j : Fin m)
    (samePrefix : ∀ i : Fin m, (i : Nat) < (j : Nat) →
      left.challenges i = right.challenges i) :
    challengeInput pcs clause pins left j =
      challengeInput pcs clause pins right j := by
  unfold challengeInput
  congr 1
  apply congrArg List.flatten
  apply List.ofFn_inj.mpr
  funext n
  apply congrArg (fun root =>
    envelope (encodeLength (n : Nat)) ++
      envelope (pcs.backend.cshake.digestCodec.encode root))
  apply congrArg (clause.transcript.root (n : Nat))
  funext i
  have hinj : (i : Nat) < (j : Nat) :=
    lt_of_lt_of_le i.isLt (Nat.lt_succ_iff.mp n.isLt)
  exact samePrefix ⟨i, lt_trans hinj j.isLt⟩ hinj

/-! ## Exact acceptance and reflection -/

/-- What the Lean verifier checks.  This is deliberately stronger and more
explicit than merely accepting a native Bool: challenges and query indices
must be the exact cSHAKE derivation, every selected Merkle opening and fold
equation must hold, and the final word must equal a degree-bounded polynomial. -/
def Accepts (clause : FriClause pcs m manifest) (pins : TranscriptPins)
    (receipt : Receipt ell m queryCount) : Prop :=
  queryCount = clause.queryCount ∧
  (∀ j, receipt.challenges j = derivedChallenge pcs clause pins receipt j) ∧
  (∀ a, receipt.querySeed a = derivedQuerySeed pcs clause pins receipt a) ∧
  (∀ (j : Fin m) (a : Fin queryCount),
    OpenedAdditiveFriQuery clause.tower j.isLt
      (pcs.commitment j) (pcs.commitment (j + 1))
      (clause.transcript.rootAt receipt.challenges j
        (Nat.le_of_lt j.isLt))
      (clause.transcript.rootAt receipt.challenges (j + 1)
        (Nat.succ_le_iff.mpr j.isLt))
      (receipt.challenges j)
      (additiveCoherentRound clause.tower.rounds_le j receipt.querySeed a)
      (receipt.opening j a)) ∧
  receipt.finalPolynomial.degree < (clause.degree m : WithBot Nat) ∧
  (∀ point,
    clause.transcript.wordAt receipt.challenges m le_rfl point =
      receipt.finalPolynomial.eval (clause.tower.dom m point))

/-- The deterministic verifier really discharges the ideal clause predicate;
there is no additional `PCSAndSampledDecider` proposition between them. -/
theorem accepts_additiveFriAdaptiveCoherentAccepts
    (clause : FriClause pcs m manifest) (pins : TranscriptPins)
    (receipt : Receipt ell m queryCount)
    (accepted : Accepts pcs clause pins receipt) :
    ∃ querySeed : Fin clause.queryCount → PowerTwoFriLevels ell 1,
      AdditiveFriAdaptiveCoherentAccepts clause.tower pcs.commitment clause.degree
        clause.transcript clause.queryCount receipt.challenges querySeed := by
  have queryCountExact : queryCount = clause.queryCount := accepted.1
  cases queryCountExact
  refine ⟨receipt.querySeed, ?_⟩
  refine ⟨?_, ?_⟩
  · intro j
    refine ⟨receipt.opening j, ?_⟩
    intro a
    exact accepted.2.2.2.1 j a
  · apply mem_reedSolomonCode_iff.mpr
    exact ⟨receipt.finalPolynomial, accepted.2.2.2.2.1,
      accepted.2.2.2.2.2⟩

/-! ## Opaque native byte execution -/

/-- A verifier artifact fixes the public proof codec in Lean.  Native code
does not get to supply or reinterpret this decoder. -/
structure Verifier (clause : FriClause pcs m manifest) where
  pins : TranscriptPins
  proofCodecPin : CodecPin
  proofCodec : LawfulCodec (Receipt ell m queryCount)
  /-- Executable verifier emitted/implemented from the Lean relation.  The
  reflection theorem, not native code, is its semantics.  This field is
  necessary because the current mathematical `binaryTower` carrier and its
  Fan--Paar equivalence are noncomputable; replacing it with `decide` would
  falsely advertise an executable field model. -/
  check : Receipt ell m queryCount → Bool
  check_iff : ∀ receipt, check receipt = true ↔
    Accepts pcs clause pins receipt

/-- Native prover/accelerator authority ends at bytes or an opaque error. -/
abbrev OpaqueProofRunner (Error : Type) :=
  List UInt8 → Except Error (List UInt8)

inductive Failure (Error : Type)
  | native (error : Error)
  | invalidEncoding
  | rejected
deriving Repr

/-- Proof-relevant successful decoding and Lean acceptance. -/
structure AcceptedReceipt (clause : FriClause pcs m manifest)
    (verifier : Verifier (queryCount := queryCount) pcs clause)
    (request : List UInt8) where
  proofBytes : List UInt8
  receipt : Receipt ell m queryCount
  decoded : verifier.proofCodec.decode proofBytes = some receipt
  accepted : Accepts pcs clause verifier.pins receipt

/-- Run arbitrary byte-producing native work and accept only after Lean's
decoder and complete additive-FRI checker succeed. -/
def run {Error : Type} (clause : FriClause pcs m manifest)
    (verifier : Verifier (queryCount := queryCount) pcs clause)
    (runner : OpaqueProofRunner Error)
    (request : List UInt8) :
    Except (Failure Error)
      (AcceptedReceipt (queryCount := queryCount) pcs clause verifier request) :=
  match returned : runner request with
  | .error error => .error (.native error)
  | .ok proofBytes =>
      match decoded : verifier.proofCodec.decode proofBytes with
      | none => .error .invalidEncoding
      | some receipt =>
          if accepted : verifier.check receipt = true then
            .ok ⟨proofBytes, receipt, decoded,
              (verifier.check_iff receipt).mp accepted⟩
          else .error .rejected

/-- Success retains the exact bytes returned by the arbitrary runner. -/
theorem run_success_runner_bytes {Error : Type}
    (clause : FriClause pcs m manifest)
    (verifier : Verifier (queryCount := queryCount) pcs clause)
    (runner : OpaqueProofRunner Error) (request : List UInt8)
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request)
    (success : run (queryCount := queryCount)
      pcs clause verifier runner request = .ok reply) :
    runner request = .ok reply.proofBytes := by
  unfold run at success
  split at success
  next error failed => simp at success
  next bytes returned =>
    split at success
    next decodeFailed => simp at success
    next receipt decoded =>
      split at success
      next accepted =>
        simp only [Except.ok.injEq] at success
        subst reply
        exact returned
      next rejected => simp at success

/-- The main control-integrity theorem: successful arbitrary native execution
means exact byte retention, exact Lean decoding, exact transcript/query/fold
acceptance, and the existing additive-FRI clause predicate. -/
theorem run_success_integrity {Error : Type}
    (clause : FriClause pcs m manifest)
    (verifier : Verifier (queryCount := queryCount) pcs clause)
    (runner : OpaqueProofRunner Error) (request : List UInt8)
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request)
    (success : run (queryCount := queryCount)
      pcs clause verifier runner request = .ok reply) :
    runner request = .ok reply.proofBytes ∧
      verifier.proofCodec.decode reply.proofBytes = some reply.receipt ∧
      Accepts pcs clause verifier.pins reply.receipt ∧
      ∃ querySeed : Fin clause.queryCount → PowerTwoFriLevels ell 1,
        AdditiveFriAdaptiveCoherentAccepts clause.tower pcs.commitment clause.degree
          clause.transcript clause.queryCount reply.receipt.challenges querySeed := by
  exact ⟨run_success_runner_bytes (queryCount := queryCount)
      pcs clause verifier runner request reply success,
    reply.decoded, reply.accepted,
    accepts_additiveFriAdaptiveCoherentAccepts pcs clause verifier.pins
      reply.receipt reply.accepted⟩

/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.MerklePcs.valueCodecExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MerklePcs.valueCodecExact
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.challengeInput_eq_of_samePrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms challengeInput_eq_of_samePrefix
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.accepts_additiveFriAdaptiveCoherentAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepts_additiveFriAdaptiveCoherentAccepts
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.run_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_success_integrity

end

end Minidregg.Compiler.Tower256AdditiveFriController
