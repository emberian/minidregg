/-
# Compiler.NoteSpendProofController -- bytes/error control for the emitted note spend

The opaque boundary in this module returns only bytes or an opaque error.  Lean
owns the canonical statement codec, receipt codec, transcript framing, cSHAKE
challenge derivation, Boolean checker, and reflection theorem.  The statement
contains the complete common-kernel digest boundary as well as the exact CSE'd
note-spend descriptor emitted by `Compiler.EmitShare`.

Controller acceptance is deliberately only deterministic control acceptance.
Opaque argument/PCS byte strings receive their semantic meaning from the
separate assurance game.  This file does not claim a deployed PCS, collision
resistance, a random oracle, proof of knowledge, or hiding.
-/
import Compiler.EmitSerialize
import Compiler.EmitShare
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Compiler.NoteSpendProofController

open Minidregg.Compiler
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

abbrev Scalar := ZMod 13

/-! ## Canonical statement -/

def relationId : Digest := ⟨801⟩
def controllerId : Digest := ⟨821⟩
def unassignedProofSuiteId : Digest := ⟨0⟩
def statementCodecPin : CodecPin := ⟨⟨822⟩, ⟨823⟩, 1⟩
def receiptCodecPin : CodecPin := ⟨⟨824⟩, ⟨825⟩, 1⟩

/-- Literal canonical bytes of the existing Lean-emitted, CSE'd note-spend
descriptor.  This is descriptor identity, not a digest collision claim. -/
def exactRelationDescriptor : List UInt8 :=
  (descriptorToJson spendDescriptorShared).pretty.toUTF8.toList

/-- Everything the proof statement must bind before an opaque prover runs. -/
structure Statement where
  argsDigest : Digest
  effectsDigest : Digest
  preRoot : Digest
  nullifier : Scalar
  root : Scalar
  outputCommitment : Scalar
  relationId : Digest
  relationDescriptor : List UInt8
  controllerId : Digest
  proofSuiteId : Digest
deriving DecidableEq, Repr

def canonicalStatement (argsDigest effectsDigest preRoot : Digest)
    (nullifier root outputCommitment : Scalar) : Statement where
  argsDigest := argsDigest
  effectsDigest := effectsDigest
  preRoot := preRoot
  nullifier := nullifier
  root := root
  outputCommitment := outputCommitment
  relationId := relationId
  relationDescriptor := exactRelationDescriptor
  controllerId := controllerId
  proofSuiteId := unassignedProofSuiteId

def scalarStream : StreamCodec Scalar :=
  StreamCodec.xmap StreamCodec.nat ZMod.val (fun n => (n : Scalar)) (by
    intro value
    exact ZMod.natCast_zmod_val value)

private def statementWireStream :=
  StreamCodec.product digestStream <|
    StreamCodec.product digestStream <|
      StreamCodec.product digestStream <|
        StreamCodec.product scalarStream <|
          StreamCodec.product scalarStream <|
            StreamCodec.product scalarStream <|
              StreamCodec.product digestStream <|
                StreamCodec.product bytesStream <|
                  StreamCodec.product digestStream digestStream

def statementStream : StreamCodec Statement :=
  StreamCodec.xmap statementWireStream
    (fun statement =>
      (statement.argsDigest,
        (statement.effectsDigest,
          (statement.preRoot,
            (statement.nullifier,
              (statement.root,
                (statement.outputCommitment,
                  (statement.relationId,
                    (statement.relationDescriptor,
                      (statement.controllerId, statement.proofSuiteId))))))))))
    (fun wire =>
      { argsDigest := wire.1
        effectsDigest := wire.2.1
        preRoot := wire.2.2.1
        nullifier := wire.2.2.2.1
        root := wire.2.2.2.2.1
        outputCommitment := wire.2.2.2.2.2.1
        relationId := wire.2.2.2.2.2.2.1
        relationDescriptor := wire.2.2.2.2.2.2.2.1
        controllerId := wire.2.2.2.2.2.2.2.2.1
        proofSuiteId := wire.2.2.2.2.2.2.2.2.2 })
    (by intro statement; cases statement; rfl)

def statementCodec : LawfulCodec Statement := statementStream.toLawful

/-! ## Receipt and reflected controller relation -/

/-- Proof-system payload remains inert bytes at this layer.  Roots and the
single controller challenge are first-order transcript data checked by Lean. -/
structure Receipt where
  statementDigest : Digest
  traceRoot : Digest
  challenge : Digest
  argumentProof : List UInt8
  pcsProof : List UInt8
deriving DecidableEq, Repr

private def receiptWireStream :=
  StreamCodec.product digestStream <|
    StreamCodec.product digestStream <|
      StreamCodec.product digestStream <|
        StreamCodec.product bytesStream bytesStream

def receiptStream : StreamCodec Receipt :=
  StreamCodec.xmap receiptWireStream
    (fun receipt =>
      (receipt.statementDigest,
        (receipt.traceRoot,
          (receipt.challenge, (receipt.argumentProof, receipt.pcsProof)))))
    (fun wire =>
      { statementDigest := wire.1
        traceRoot := wire.2.1
        challenge := wire.2.2.1
        argumentProof := wire.2.2.2.1
        pcsProof := wire.2.2.2.2 })
    (by intro receipt; cases receipt; rfl)

def receiptCodec : LawfulCodec Receipt := receiptStream.toLawful

abbrev cshake := Tower256ConcreteBackend.backend.cshake

def statementDigestCustomization : List UInt8 :=
  "minidregg/note-spend/statement/v1".toUTF8.toList

def challengeCustomization : List UInt8 :=
  "minidregg/note-spend/challenge/v1".toUTF8.toList

def derivedStatementDigest (statement : Statement) : Digest :=
  cshake.xofDigest statementDigestCustomization (statementCodec.encode statement)

/-- Roots precede the challenge.  Argument and PCS proof bytes follow it and
cannot affect the challenge that they claim to answer. -/
def challengeInput (statement : Statement) (receipt : Receipt) : List UInt8 :=
  envelope (cshake.digestCodec.encode (derivedStatementDigest statement)) ++
    envelope (cshake.digestCodec.encode receipt.traceRoot)

def derivedChallenge (statement : Statement) (receipt : Receipt) : Digest :=
  cshake.xofDigest challengeCustomization (challengeInput statement receipt)

/-- Exact deterministic controller acceptance.  The nonempty byte checks are
framing checks only; cryptographic semantics are not inferred from them. -/
def Accepts (statement : Statement) (receipt : Receipt) : Prop :=
  statement.relationId = relationId ∧
  statement.relationDescriptor = exactRelationDescriptor ∧
  statement.controllerId = controllerId ∧
  statement.proofSuiteId = unassignedProofSuiteId ∧
  receipt.statementDigest = derivedStatementDigest statement ∧
  receipt.challenge = derivedChallenge statement receipt ∧
  receipt.argumentProof ≠ [] ∧
  receipt.pcsProof ≠ []

/-- Lean's Boolean reading of the complete control relation. -/
def check (statement : Statement) (receipt : Receipt) : Bool := by
  classical
  exact decide (Accepts statement receipt)

theorem check_iff (statement : Statement) (receipt : Receipt) :
    check statement receipt = true ↔ Accepts statement receipt := by
  classical
  exact decide_eq_true_iff

/-! ## Opaque bytes/error execution -/

abbrev OpaqueProofRunner (Error : Type) :=
  List UInt8 → Except Error (List UInt8)

inductive Failure (Error : Type)
  | native (error : Error)
  | invalidEncoding
  | rejected
deriving Repr

/-- Successful control retains exactly the returned bytes and their one Lean
decoding.  No caller supplies an acceptance proof. -/
structure AcceptedReceipt (statement : Statement) where
  proofBytes : List UInt8
  receipt : Receipt
  decoded : receiptCodec.decode proofBytes = some receipt
  accepted : Accepts statement receipt

/-- The runner receives only the canonical statement encoding selected by
Lean.  Its output is decoded and checked exactly once. -/
def run {Error : Type} (statement : Statement)
    (runner : OpaqueProofRunner Error) :
    Except (Failure Error) (AcceptedReceipt statement) :=
  match runner (statementCodec.encode statement) with
  | .error error => .error (.native error)
  | .ok proofBytes =>
      match decoded : receiptCodec.decode proofBytes with
      | none => .error .invalidEncoding
      | some receipt =>
          if accepted : check statement receipt = true then
            .ok ⟨proofBytes, receipt, decoded,
              (check_iff statement receipt).mp accepted⟩
          else
            .error .rejected

theorem run_success_integrity {Error : Type} (statement : Statement)
    (runner : OpaqueProofRunner Error) (reply : AcceptedReceipt statement)
    (success : run statement runner = .ok reply) :
    runner (statementCodec.encode statement) = .ok reply.proofBytes ∧
    receiptCodec.decode reply.proofBytes = some reply.receipt ∧
    Accepts statement reply.receipt := by
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
        exact ⟨returned, decoded, (check_iff statement receipt).mp checked⟩
      next rejected => simp at success

/-- Neither proof byte field can affect the challenge it answers. -/
theorem derivedChallenge_independent_of_proofBytes (statement : Statement)
    (left right : Receipt) (sameTraceRoot : left.traceRoot = right.traceRoot) :
    derivedChallenge statement left = derivedChallenge statement right := by
  unfold derivedChallenge challengeInput
  rw [sameTraceRoot]

theorem canonicalStatement_exact (argsDigest effectsDigest preRoot : Digest)
    (nullifier root outputCommitment : Scalar) :
    let statement := canonicalStatement argsDigest effectsDigest preRoot
      nullifier root outputCommitment
    statement.relationId = relationId ∧
      statement.relationDescriptor = exactRelationDescriptor ∧
      statement.controllerId = controllerId ∧
      statement.proofSuiteId = unassignedProofSuiteId := by
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms check_iff
#print axioms run_success_integrity
#print axioms derivedChallenge_independent_of_proofBytes
#print axioms canonicalStatement_exact

end

end Minidregg.Compiler.NoteSpendProofController
