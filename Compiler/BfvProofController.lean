/-
# Compiler.BfvProofController -- release-free BFV proof control

The current compressed-BFV development has an exact Lean theorem for all 384
integer equations, but no deployed succinct verifier.  This module therefore
owns only the narrow deterministic control boundary which already exists:

* a canonical statement byte encoding for the complete kernel digest boundary,
  public BFV identity, output commitment, and exact 384-row relation shape;
* a canonical receipt encoding and roots-before-challenges cSHAKE transcript;
* a reflected framing checker; and
* an opaque runner which returns bytes or an opaque error.

The accepted BFV path supplies its existing zero proof-codec, proof-suite, and
controller sentinels.  Nonempty proof frames are syntax, not verification.  The
typed `SuccinctSuiteInterface` is the exact residual where a future Lean
verifier must attach semantic meaning; this file constructs no instance and
claims no arithmetic soundness, PCS, collision resistance, ROM, knowledge,
privacy, or hiding theorem.
-/
import Compiler.BfvReceiptClause
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Compiler.BfvProofController

open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvInputValidity
open Minidregg.Compiler.BfvReceiptClause
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## Exact statement payload -/

/-- The canonical byte view of one 32-byte BFV identifier. -/
def digest32Bytes (digest : Digest32) : List UInt8 :=
  List.ofFn fun i : Fin 32 => UInt8.ofNat (digest i).val

/-- Ordered public identity of the exact BFV input.  Length envelopes make the
four ciphertext-row identifiers and the remaining identifiers unambiguous.
The full request codec/digest separately commits the dynamic equation family. -/
def publicInputDescriptor (claim : PublicStatement) : List UInt8 :=
  let reference := claim.input.reference
  let identifiers := reference.publicInputs
  envelope (digest32Bytes identifiers.collectiveKeyId) ++
    envelope (digest32Bytes identifiers.ciphertextSetId) ++
    ((List.ofFn fun owner : Fin ownerCount =>
      envelope (digest32Bytes (identifiers.ciphertextRowId owner))).flatten) ++
    envelope (digest32Bytes identifiers.messageTableId) ++
    envelope (digest32Bytes identifiers.bfvParametersId) ++
    envelope (digest32Bytes identifiers.relationDigest) ++
    envelope (digest32Bytes reference.sessionId) ++
    envelope (digest32Bytes reference.challengeId) ++
    envelope (StreamCodec.nat.encode reference.owner.val) ++
    envelope (digest32Bytes reference.rootId)

/-- Literal descriptor for the exact relation shape already proved by
`BfvReceiptClause.AcceptedToken`: deployed layout/codec, 12,435 owner cells,
12,416 active coordinates, 128 rounds in each of the three modulus-major
blocks, and 384 rows for the selected owner.  This is descriptor identity, not
a hash-binding or proof-system theorem. -/
def exactRelationDescriptor : List UInt8 :=
  envelope deployedLayoutId.toUTF8.toList ++
    envelope deployedRelationCodecId.toUTF8.toList ++
    envelope (StreamCodec.nat.encode ownerWitnessWidth) ++
    envelope (StreamCodec.nat.encode activeWidth) ++
    envelope (StreamCodec.nat.encode compressionRounds) ++
    envelope (StreamCodec.nat.encode RnsModulus.q0.value) ++
    envelope (StreamCodec.nat.encode RnsModulus.q1.value) ++
    envelope (StreamCodec.nat.encode RnsModulus.q2.value) ++
    envelope (StreamCodec.nat.encode equationsPerOwner)

/-- Everything the unavailable BFV proof suite would have to bind.  The effect
digest is the accepted kernel digest of the structurally encoded typed resource
effects, exact footprint, and eager nullifier.  There is no release, observer,
recipient, disclosure intent, or hiding flag in this first-order statement. -/
structure Statement where
  argsDigest : Digest
  effectsDigest : Digest
  preRoot : Digest
  publicInputDescriptor : List UInt8
  outputCommitment : Digest
  relationDescriptor : List UInt8
  clauseId : Digest
  relationId : Digest
  outputRepresentationId : Digest
  proofCodecId : Digest
  proofSuiteId : Digest
  controllerDigest : Digest
deriving DecidableEq, Repr

/-- The constructor takes every deployment pin explicitly.  The authoritative
accepted BFV path supplies its current zero sentinels; a future suite can use
assigned pins only after those identities enter the accepted request itself. -/
def canonicalStatement (argsDigest effectsDigest preRoot : Digest)
    (claim : PublicStatement)
    (outputCommitment outputRepresentationId proofCodecId proofSuiteId
      controllerDigest : Digest) : Statement where
  argsDigest := argsDigest
  effectsDigest := effectsDigest
  preRoot := preRoot
  publicInputDescriptor := publicInputDescriptor claim
  outputCommitment := outputCommitment
  relationDescriptor := exactRelationDescriptor
  clauseId := bfvClauseId
  relationId := bfvRelationId
  outputRepresentationId := outputRepresentationId
  proofCodecId := proofCodecId
  proofSuiteId := proofSuiteId
  controllerDigest := controllerDigest

private def statementWireStream :=
  StreamCodec.product digestStream <|
    StreamCodec.product digestStream <|
      StreamCodec.product digestStream <|
        StreamCodec.product bytesStream <|
          StreamCodec.product digestStream <|
            StreamCodec.product bytesStream <|
              StreamCodec.product digestStream <|
                StreamCodec.product digestStream <|
                  StreamCodec.product digestStream <|
                    StreamCodec.product digestStream <|
                      StreamCodec.product digestStream digestStream

def statementStream : StreamCodec Statement :=
  StreamCodec.xmap statementWireStream
    (fun statement =>
      (statement.argsDigest,
        (statement.effectsDigest,
          (statement.preRoot,
            (statement.publicInputDescriptor,
              (statement.outputCommitment,
                (statement.relationDescriptor,
                  (statement.clauseId,
                    (statement.relationId,
                      (statement.outputRepresentationId,
                        (statement.proofCodecId,
                          (statement.proofSuiteId,
                            statement.controllerDigest))))))))))))
    (fun wire =>
      { argsDigest := wire.1
        effectsDigest := wire.2.1
        preRoot := wire.2.2.1
        publicInputDescriptor := wire.2.2.2.1
        outputCommitment := wire.2.2.2.2.1
        relationDescriptor := wire.2.2.2.2.2.1
        clauseId := wire.2.2.2.2.2.2.1
        relationId := wire.2.2.2.2.2.2.2.1
        outputRepresentationId := wire.2.2.2.2.2.2.2.2.1
        proofCodecId := wire.2.2.2.2.2.2.2.2.2.1
        proofSuiteId := wire.2.2.2.2.2.2.2.2.2.2.1
        controllerDigest := wire.2.2.2.2.2.2.2.2.2.2.2 })
    (by intro statement; cases statement; rfl)

def statementCodec : LawfulCodec Statement := statementStream.toLawful

/-! ## Lean-owned receipt control -/

/-- Opaque proof-system payload surrounded by transcript fields Lean can
decode and recompute.  The two proof byte strings remain semantically inert. -/
structure Receipt where
  statementDigest : Digest
  arithmeticRoot : Digest
  pcsRoot : Digest
  challenge : Digest
  arithmeticProof : List UInt8
  pcsProof : List UInt8
deriving DecidableEq, Repr

private def receiptWireStream :=
  StreamCodec.product digestStream <|
    StreamCodec.product digestStream <|
      StreamCodec.product digestStream <|
        StreamCodec.product digestStream <|
          StreamCodec.product bytesStream bytesStream

def receiptStream : StreamCodec Receipt :=
  StreamCodec.xmap receiptWireStream
    (fun receipt =>
      (receipt.statementDigest,
        (receipt.arithmeticRoot,
          (receipt.pcsRoot,
            (receipt.challenge, (receipt.arithmeticProof, receipt.pcsProof))))))
    (fun wire =>
      { statementDigest := wire.1
        arithmeticRoot := wire.2.1
        pcsRoot := wire.2.2.1
        challenge := wire.2.2.2.1
        arithmeticProof := wire.2.2.2.2.1
        pcsProof := wire.2.2.2.2.2 })
    (by intro receipt; cases receipt; rfl)

def receiptCodec : LawfulCodec Receipt := receiptStream.toLawful

abbrev cshake := Tower256ConcreteBackend.backend.cshake

def statementDigestCustomization : List UInt8 :=
  "minidregg/bfv384/statement/v1".toUTF8.toList

def challengeCustomization : List UInt8 :=
  "minidregg/bfv384/challenge/v1".toUTF8.toList

def derivedStatementDigest (statement : Statement) : Digest :=
  cshake.xofDigest statementDigestCustomization (statementCodec.encode statement)

/-- Both commitment roots precede the challenge.  Neither opaque proof frame
can affect the challenge which it claims to answer. -/
def challengeInput (statement : Statement) (receipt : Receipt) : List UInt8 :=
  envelope (cshake.digestCodec.encode (derivedStatementDigest statement)) ++
    envelope (cshake.digestCodec.encode receipt.arithmeticRoot) ++
    envelope (cshake.digestCodec.encode receipt.pcsRoot)

def derivedChallenge (statement : Statement) (receipt : Receipt) : Digest :=
  cshake.xofDigest challengeCustomization (challengeInput statement receipt)

/-- Deterministic control-envelope acceptance only.  In particular, this is
not the missing 384-row succinct verifier. -/
def ControlAccepts (statement : Statement) (receipt : Receipt) : Prop :=
  statement.relationDescriptor = exactRelationDescriptor ∧
  statement.clauseId = bfvClauseId ∧
  statement.relationId = bfvRelationId ∧
  receipt.statementDigest = derivedStatementDigest statement ∧
  receipt.challenge = derivedChallenge statement receipt ∧
  receipt.arithmeticProof ≠ [] ∧
  receipt.pcsProof ≠ []

def controlCheck (statement : Statement) (receipt : Receipt) : Bool := by
  classical
  exact decide (ControlAccepts statement receipt)

theorem controlCheck_iff (statement : Statement) (receipt : Receipt) :
    controlCheck statement receipt = true ↔ ControlAccepts statement receipt := by
  classical
  exact decide_eq_true_iff

/-! ## Opaque bytes/error execution -/

abbrev OpaqueProofRunner (Error : Type) :=
  List UInt8 → Except Error (List UInt8)

inductive Failure (Error : Type)
  | native (error : Error)
  | invalidEncoding
  | rejectedControlEnvelope
deriving Repr

/-- A controlled receipt records decoding and framing, not proof semantics. -/
structure ControlledReceipt (statement : Statement) where
  proofBytes : List UInt8
  receipt : Receipt
  decoded : receiptCodec.decode proofBytes = some receipt
  controlled : ControlAccepts statement receipt

/-- The opaque runner receives exactly the Lean-selected statement bytes. -/
def run {Error : Type} (statement : Statement)
    (runner : OpaqueProofRunner Error) :
    Except (Failure Error) (ControlledReceipt statement) :=
  match runner (statementCodec.encode statement) with
  | .error error => .error (.native error)
  | .ok proofBytes =>
      match decoded : receiptCodec.decode proofBytes with
      | none => .error .invalidEncoding
      | some receipt =>
          if accepted : controlCheck statement receipt = true then
            .ok ⟨proofBytes, receipt, decoded,
              (controlCheck_iff statement receipt).mp accepted⟩
          else
            .error .rejectedControlEnvelope

theorem run_success_integrity {Error : Type} (statement : Statement)
    (runner : OpaqueProofRunner Error) (reply : ControlledReceipt statement)
    (success : run statement runner = .ok reply) :
    runner (statementCodec.encode statement) = .ok reply.proofBytes ∧
    receiptCodec.decode reply.proofBytes = some reply.receipt ∧
    ControlAccepts statement reply.receipt := by
  unfold run at success
  split at success
  next error failed => simp at success
  next bytes returned =>
    split at success
    next decodeFailed => simp at success
    next receipt decoded =>
      split at success
      next checked =>
        simp only [Except.ok.injEq] at success
        subst reply
        exact ⟨returned, decoded,
          (controlCheck_iff statement receipt).mp checked⟩
      next rejected => simp at success

/-- A future succinct verifier must be an actual Lean checker with a reflected
semantic relation and assigned deployment identity.  No interface value is
supplied here. -/
structure SuccinctSuiteInterface where
  proofCodecId : Digest
  proofSuiteId : Digest
  controllerDigest : Digest
  proofCodecAssigned : proofCodecId ≠ ⟨0⟩
  proofSuiteAssigned : proofSuiteId ≠ ⟨0⟩
  controllerAssigned : controllerDigest ≠ ⟨0⟩
  SemanticAccepts : Statement → Receipt → Prop
  check : Statement → Receipt → Bool
  check_iff : ∀ statement receipt,
    check statement receipt = true ↔ SemanticAccepts statement receipt

/-- Semantic admission is available only after an assigned suite is bound to
all three exact statement pins.  Merely constructing a reflected predicate is
insufficient. -/
structure BoundSuite (statement : Statement) where
  suite : SuccinctSuiteInterface
  proofCodecBound : statement.proofCodecId = suite.proofCodecId
  proofSuiteBound : statement.proofSuiteId = suite.proofSuiteId
  controllerBound : statement.controllerDigest = suite.controllerDigest

/-- Neither opaque proof frame participates in its own challenge. -/
theorem derivedChallenge_independent_of_proofBytes (statement : Statement)
    (left right : Receipt)
    (sameRoots : left.arithmeticRoot = right.arithmeticRoot ∧
      left.pcsRoot = right.pcsRoot) :
    derivedChallenge statement left = derivedChallenge statement right := by
  rcases sameRoots with ⟨arithmeticRoot, pcsRoot⟩
  unfold derivedChallenge challengeInput
  rw [arithmeticRoot, pcsRoot]

theorem canonicalStatement_exact (argsDigest effectsDigest preRoot : Digest)
    (claim : PublicStatement)
    (outputCommitment outputRepresentationId proofCodecId proofSuiteId
      controllerDigest : Digest) :
    let statement := canonicalStatement argsDigest effectsDigest preRoot claim
      outputCommitment outputRepresentationId proofCodecId proofSuiteId controllerDigest
    statement.publicInputDescriptor = publicInputDescriptor claim ∧
      statement.outputRepresentationId = outputRepresentationId ∧
      statement.relationDescriptor = exactRelationDescriptor ∧
      statement.clauseId = bfvClauseId ∧
      statement.relationId = bfvRelationId ∧
      statement.proofCodecId = proofCodecId ∧
      statement.proofSuiteId = proofSuiteId ∧
      statement.controllerDigest = controllerDigest := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The current canonical BFV statement cannot masquerade as a deployed
succinct suite: every deployment pin is zero, while every bound suite must
carry assigned nonzero identities. -/
theorem canonicalStatement_no_boundSuite
    (argsDigest effectsDigest preRoot : Digest) (claim : PublicStatement)
    (outputCommitment outputRepresentationId : Digest) :
    ¬Nonempty (BoundSuite (canonicalStatement argsDigest effectsDigest preRoot
      claim outputCommitment outputRepresentationId unassignedProofCodecId
      unassignedProofSuiteId unassignedControllerDigest)) := by
  rintro ⟨bound⟩
  exact bound.suite.proofCodecAssigned (by
    rw [← bound.proofCodecBound]
    rfl)

/-- info: 'Minidregg.Compiler.BfvProofController.controlCheck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms controlCheck_iff
/-- info: 'Minidregg.Compiler.BfvProofController.run_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_success_integrity
/-- info: 'Minidregg.Compiler.BfvProofController.derivedChallenge_independent_of_proofBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms derivedChallenge_independent_of_proofBytes
/-- info: 'Minidregg.Compiler.BfvProofController.canonicalStatement_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalStatement_exact
/-- info: 'Minidregg.Compiler.BfvProofController.canonicalStatement_no_boundSuite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalStatement_no_boundSuite

end

end Minidregg.Compiler.BfvProofController
