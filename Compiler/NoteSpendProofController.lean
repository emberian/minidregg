/-
# Compiler.NoteSpendProofController -- bytes/error control for the emitted note spend

The opaque boundary in this module returns only bytes or an opaque error.  Lean
owns the canonical statement codec, receipt codec, transcript framing, cSHAKE
challenge derivation, Boolean checker, and reflection theorem.  The statement
contains the complete common-kernel digest boundary as well as the exact CSE'd
note-spend descriptor emitted by `Compiler.EmitShare`.

Controller acceptance is deliberately only deterministic control acceptance.
Opaque argument/PCS byte strings receive their semantic meaning from the
separate assurance game.  A reflected suite checker remains identity and
framing evidence until same-coin arithmetic, PCS, collision-resistance,
random-oracle, and knowledge laws are supplied.  This file constructs no
deployment and claims no hiding.
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
    (nullifier root outputCommitment : Scalar) (proofSuiteId : Digest) :
    Statement where
  argsDigest := argsDigest
  effectsDigest := effectsDigest
  preRoot := preRoot
  nullifier := nullifier
  root := root
  outputCommitment := outputCommitment
  relationId := relationId
  relationDescriptor := exactRelationDescriptor
  controllerId := controllerId
  proofSuiteId := proofSuiteId

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

/-- Exact deterministic control-envelope acceptance.  The nonempty byte
checks are framing checks only; cryptographic semantics are not inferred from
them.  The proof-suite pin is statement data, not something this control
checker interprets. -/
def ControlAccepts (statement : Statement) (receipt : Receipt) : Prop :=
  statement.relationId = relationId ∧
  statement.relationDescriptor = exactRelationDescriptor ∧
  statement.controllerId = controllerId ∧
  receipt.statementDigest = derivedStatementDigest statement ∧
  receipt.challenge = derivedChallenge statement receipt ∧
  receipt.argumentProof ≠ [] ∧
  receipt.pcsProof ≠ []

/-- Lean's Boolean reading of the complete control relation. -/
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

/-- A controlled receipt retains decoding and framing, not proof semantics. -/
structure ControlledReceipt (statement : Statement) where
  proofBytes : List UInt8
  receipt : Receipt
  decoded : receiptCodec.decode proofBytes = some receipt
  controlled : ControlAccepts statement receipt

/-- The runner receives only the canonical statement encoding selected by
Lean.  Its output is decoded and checked exactly once. -/
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
        exact ⟨returned, decoded, (controlCheck_iff statement receipt).mp checked⟩
      next rejected => simp at success

/-- A candidate suite is an actual Lean Boolean with a reflected acceptance
relation and a nonzero deployment identity.  This interface alone does not
say that acceptance implies note-spend arithmetic, PCS soundness, knowledge,
or hiding. -/
structure ReflectedSuiteInterface where
  proofSuiteId : Digest
  proofSuiteAssigned : proofSuiteId ≠ ⟨0⟩
  ReflectedAccepts : Statement → Receipt → Prop
  check : Statement → Receipt → Bool
  check_iff : ∀ statement receipt,
    check statement receipt = true ↔ ReflectedAccepts statement receipt

/-- Exact binding of a reflected suite to the statement-owned proof-suite
pin.  This is identity/checker evidence only; semantic admission additionally
requires same-coin reduction laws in the assurance layer. -/
structure BoundReflectedSuite (statement : Statement) where
  suite : ReflectedSuiteInterface
  proofSuiteBound : statement.proofSuiteId = suite.proofSuiteId

/-- Neither proof byte field can affect the challenge it answers. -/
theorem derivedChallenge_independent_of_proofBytes (statement : Statement)
    (left right : Receipt) (sameTraceRoot : left.traceRoot = right.traceRoot) :
    derivedChallenge statement left = derivedChallenge statement right := by
  unfold derivedChallenge challengeInput
  rw [sameTraceRoot]

theorem canonicalStatement_exact (argsDigest effectsDigest preRoot : Digest)
    (nullifier root outputCommitment : Scalar) (proofSuiteId : Digest) :
    let statement := canonicalStatement argsDigest effectsDigest preRoot
      nullifier root outputCommitment proofSuiteId
    statement.relationId = relationId ∧
      statement.relationDescriptor = exactRelationDescriptor ∧
      statement.controllerId = controllerId ∧
      statement.proofSuiteId = proofSuiteId := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The current canonical statement cannot masquerade as a deployed suite:
its proof-suite pin is zero, while every bound reflected suite must carry an
assigned nonzero identity. -/
theorem canonicalStatement_no_boundReflectedSuite
    (argsDigest effectsDigest preRoot : Digest)
    (nullifier root outputCommitment : Scalar) :
    ¬Nonempty (BoundReflectedSuite
      (canonicalStatement argsDigest effectsDigest preRoot nullifier root
        outputCommitment unassignedProofSuiteId)) := by
  rintro ⟨bound⟩
  exact bound.suite.proofSuiteAssigned (by
    rw [← bound.proofSuiteBound]
    rfl)

/-- info: 'Minidregg.Compiler.NoteSpendProofController.controlCheck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms controlCheck_iff
/-- info: 'Minidregg.Compiler.NoteSpendProofController.run_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_success_integrity
/-- info: 'Minidregg.Compiler.NoteSpendProofController.derivedChallenge_independent_of_proofBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms derivedChallenge_independent_of_proofBytes
/-- info: 'Minidregg.Compiler.NoteSpendProofController.canonicalStatement_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalStatement_exact
/-- info: 'Minidregg.Compiler.NoteSpendProofController.canonicalStatement_no_boundReflectedSuite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalStatement_no_boundReflectedSuite

end

end Minidregg.Compiler.NoteSpendProofController
