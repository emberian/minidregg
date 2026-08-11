/-
# Compiler.Tower256AdditiveFriRawDeployment -- inhabited raw PCS deployment

The raw additive-FRI controller deliberately removed the impossible universal
Merkle binding field.  This module shows that the resulting deployment
surface is not merely consistent: the repository's concrete Tower256/cSHAKE
backend supplies every Merkle level, a one-round/one-query statement is
constructed, and a closed bootstrap statement crosses the opaque byte
boundary with a Lean-accepted receipt.

The example is intentionally a plumbing witness, not a soundness claim.  Its
word is zero, so it does not satisfy the `initialFar` premise of the additive
proximity theorem.  Conversely, nothing here assumes cSHAKE collision
resistance, a ROM theorem, or native arithmetic.  The verifier relation is
Lean-owned; the current Tower256 carrier remains noncomputable, exactly as in
the general controller.
-/

import Compiler.Tower256AdditiveFriRawController
import Mathlib.Data.Finsupp.Encodable

namespace Minidregg.Compiler.Tower256AdditiveFriRawDeployment

open Polynomial
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.Tower256CshakeMerkleBinding
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Loom
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000

noncomputable section

/-! ## Stable concrete raw PCS metadata -/

/-- Compact prefix codec for bounded natural coordinates. -/
def finStream (size : Nat) : StreamCodec (Fin size) where
  encode value := StreamCodec.nat.encode value.val
  decodePrefix bytes := do
    let (value, suffix) <- StreamCodec.nat.decodePrefix bytes
    if inBounds : value < size then
      some (⟨value, inBounds⟩, suffix)
    else
      none
  decodePrefix_encode := by
    intro value suffix
    simp [StreamCodec.nat.decodePrefix_encode, value.isLt]

/-- Per-level identifiers are derived injectively from the level.  These are
the fixture namespace, not the production artifact's final registry IDs. -/
def levelId (tag level : Nat) : Digest := ⟨970000 + 4 * level + tag⟩

/-- The actual shared backend, checkpoint role, Tower256 codec, compact finite
domain codec, and stable IDs for one raw additive level. -/
def levelSpec (ell level : Nat) :
    LevelSpec Tower256ConcreteBackend.backend ell level where
  role := .checkpoint
  roleExact := rfl
  slotId := levelId 0 level
  semanticTypeId := levelId 1 level
  domainId := levelId 2 level
  domainCodecPin := ⟨levelId 3 level, levelId 2 level, 1⟩
  domainCodec := (finStream (2 ^ (ell - level))).toLawful

/-- A concrete raw Merkle PCS exists at every tree height.  There is no
`PositionBinding` field to fabricate: collision resistance remains a priced
deployment premise at the exact extracted attempts. -/
def rawPcs (ell : Nat) : RawMerklePcs ell :=
  RawMerklePcs.ofConcrete (levelSpec ell)

instance rawMerklePcsNonempty (ell : Nat) : Nonempty (RawMerklePcs ell) :=
  ⟨rawPcs ell⟩

@[simp] theorem rawPcs_backend (ell : Nat) :
    (rawPcs ell).backend = Tower256ConcreteBackend.backend := rfl

@[simp] theorem rawPcs_level_role (ell level : Nat) :
    ((rawPcs ell).level level).role = .checkpoint := rfl

/-! ## Concrete statement carriers -/

abbrev OneRoundPcs := rawPcs 1

/-- The singleton family `[1]` is linearly independent over GF(2). -/
def oneRoundTower : AdditiveFriTower Tower256 1 1 where
  beta := fun _ => 1
  offset := 0
  independent := by
    rw [linearIndependent_unique_iff]
    exact one_ne_zero
  rounds_le := le_rfl

/-- Every adaptive level is the zero word.  Roots are nevertheless the real
concrete Merkle commitments and honest openings are real path bytes. -/
def zeroTranscript : RawTranscript OneRoundPcs where
  word := fun _ _ _ => 0
  root := fun n _ => (OneRoundPcs.opening n).commit (fun _ => 0)
  root_eq_commit := by intro _ _; rfl

/-- A nonempty raw statement with one round and one coherent query. -/
def statement : Statement OneRoundPcs 1 where
  tower := oneRoundTower
  degree := fun _ => 1
  transcript := zeroTranscript
  queryCount := 1

instance statementNonempty : Nonempty (Statement OneRoundPcs 1) :=
  ⟨statement⟩

/-- A zero-round specialization used only to close the complete byte boundary
without asking the kernel to normalize a full concrete cSHAKE transcript in a
carrier-inhabitation proof.  The nontrivial one-round statement above remains
the deployed statement witness. -/
def bootstrapTower : AdditiveFriTower Tower256 1 0 where
  beta := fun _ => 1
  offset := 0
  independent := by
    rw [linearIndependent_unique_iff]
    exact one_ne_zero
  rounds_le := Nat.zero_le _

def bootstrapStatement : Statement OneRoundPcs 0 where
  tower := bootstrapTower
  degree := fun _ => 1
  transcript := zeroTranscript
  queryCount := 0

/-- Concrete domain separation for the bootstrap verifier. -/
def bootstrapPins : TranscriptPins where
  statementBytes := [0x6d, 0x69, 0x6e, 0x69, 0x64, 0x72, 0x65, 0x67, 0x67]
  challengeDomainId := ⟨970100⟩
  queryDomainId := ⟨970101⟩
  domainIdsDistinct := by decide
  challengeCustomization := [0x4d, 0x44, 0x2d, 0x46, 0x52, 0x49, 0x2d, 0x43]
  queryCustomization := [0x4d, 0x44, 0x2d, 0x46, 0x52, 0x49, 0x2d, 0x51]
  customizationsDistinct := by decide

/-- The unique empty draw/query tape and exact final zero polynomial. -/
def bootstrapReceipt : Receipt 1 0 0 where
  challenges := fun i => i.elim0
  querySeed := fun i => i.elim0
  opening := fun j => j.elim0
  finalPolynomial := 0

theorem bootstrapReceipt_accepts :
    Accepts OneRoundPcs bootstrapStatement bootstrapPins bootstrapReceipt := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => j.elim0
  · exact fun a => a.elim0
  · exact fun j => j.elim0
  · change (0 : Polynomial Tower256).degree < (1 : WithBot Nat)
    simp
  · intro point
    change (0 : Tower256) = Polynomial.eval (bootstrapTower.dom 0 point) 0
    simp

/-! ## Byte-bound verifier witness -/

/-- Encode any encodable Lean value through a unary natural fixture codec.
This is deliberately not the production receipt format. -/
def encodableCodec (alpha : Type*) [Encodable alpha] :
    LawfulCodec alpha := by
  exact
    { encode := fun value => List.replicate (Encodable.encode value) 0
      decode := fun bytes =>
        if bytes.all (fun byte => byte == 0) then Encodable.decode bytes.length
        else none
      decode_encode := by
        intro value
        simp }

/-- Empty functions carry no data, so the final polynomial is an injective
wire view of the bootstrap receipt. -/
def receiptWire (receipt : Receipt 1 0 0) :=
  receipt.finalPolynomial.toFinsupp

noncomputable instance uint8Countable : Countable UInt8 :=
  (show Function.Injective UInt8.toNat from by
    intro left right equal
    exact UInt8.toNat.inj equal).countable

noncomputable instance towerCountable : Countable Tower256 :=
  (Minidregg.Theory.BinaryTowerCodec.fieldFinEquiv 8).injective.countable

noncomputable instance towerEncodable : Encodable Tower256 :=
  Encodable.ofCountable Tower256

noncomputable instance towerDecidableEq : DecidableEq Tower256 :=
  Encodable.decidableEqOfEncodable Tower256

theorem receiptWire_injective : Function.Injective receiptWire := by
  intro left right equal
  have finalEqual : left.finalPolynomial = right.finalPolynomial :=
    Polynomial.toFinsupp_injective equal
  cases left with
  | mk leftChallenges leftSeed leftOpening leftFinal =>
      cases right with
      | mk rightChallenges rightSeed rightOpening rightFinal =>
          dsimp only at finalEqual
          subst rightFinal
          congr
          · exact Subsingleton.elim _ _
          · exact Subsingleton.elim _ _
          · exact Subsingleton.elim _ _

noncomputable instance receiptEncodable : Encodable (Receipt 1 0 0) := by
  classical
  letI : Countable (AddMonoidAlgebra Tower256 Nat) := by
    change Countable (Nat →₀ Tower256)
    infer_instance
  letI : Encodable (AddMonoidAlgebra Tower256 Nat) :=
    Encodable.ofCountable _
  exact Encodable.ofInj receiptWire receiptWire_injective

/-- Exact semantic reflection.  It is Lean-owned but, like the current
Galois-field carrier itself, not advertised as native executable code. -/
noncomputable def check (receipt : Receipt 1 0 0) : Bool :=
  by
    classical
    exact decide (Accepts OneRoundPcs bootstrapStatement bootstrapPins receipt)

theorem check_iff (receipt : Receipt 1 0 0) :
    check receipt = true <->
      Accepts OneRoundPcs bootstrapStatement bootstrapPins receipt := by
  classical
  simp [check]

def proofCodecPin : CodecPin := ⟨⟨970110⟩, ⟨970111⟩, 1⟩

/-- A complete inhabitant of the formerly high-ranked verifier carrier. -/
noncomputable def verifier :
    Tower256AdditiveFriRawController.Verifier (queryCount := 0)
      OneRoundPcs bootstrapStatement where
  pins := bootstrapPins
  proofCodecPin := proofCodecPin
  proofCodec := encodableCodec (Receipt 1 0 0)
  check := check
  check_iff := check_iff

instance verifierNonempty :
    Nonempty (Verifier (queryCount := 0) OneRoundPcs bootstrapStatement) :=
  ⟨verifier⟩

/-- An opaque runner may return the encoded honest proof bytes; Lean still
decodes and checks them before constructing `AcceptedReceipt`. -/
def honestRunner :
    Tower256AdditiveFriRawController.OpaqueProofRunner Unit := fun _ =>
  Except.ok (verifier.proofCodec.encode bootstrapReceipt)

theorem honest_run_succeeds (request : List UInt8) :
    exists reply,
      Tower256AdditiveFriRawController.run OneRoundPcs bootstrapStatement verifier
        honestRunner request = Except.ok reply := by
  have checked : verifier.check bootstrapReceipt = true :=
    (verifier.check_iff bootstrapReceipt).mpr bootstrapReceipt_accepts
  unfold Tower256AdditiveFriRawController.run
  simp only [honestRunner]
  split
  next decodeFailed =>
    have decoded := verifier.proofCodec.decode_encode bootstrapReceipt
    rw [decodeFailed] at decoded
    contradiction
  next receipt decoded =>
    have receiptExact : receipt = bootstrapReceipt := by
      apply Option.some.inj
      exact decoded.symm.trans (verifier.proofCodec.decode_encode bootstrapReceipt)
    subst receipt
    split
    next => exact ⟨_, rfl⟩
    next rejected => exact False.elim (rejected checked)

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.Tower256AdditiveFriRawDeployment.bootstrapReceipt_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bootstrapReceipt_accepts
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriRawDeployment.honest_run_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honest_run_succeeds

end

end Minidregg.Compiler.Tower256AdditiveFriRawDeployment
