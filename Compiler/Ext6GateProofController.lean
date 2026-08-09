/-
# Compiler.Ext6GateProofController -- Lean-owned control for the Ext6 gate proof

This module fixes the deterministic control surface around the already-proved
`GateFactoredExt6` construction.  It does not implement an Ext6 PCS and it does
not assign semantics to native code.  An arbitrary native runner returns only
bytes or an opaque error.  Lean selects the receipt codec, derives every
challenge with the repository's concrete cSHAKE implementation, and reflects
the complete algebraic verifier relation.

The transcript order is literal data:

1. the canonical Lean statement preimage and trace root precede `gamma`;
2. the seven operand roots are bound after `gamma`;
3. round message `i` precedes round challenge `i`;
4. all seven terminal values precede fresh `eta`; and
5. the eta-aggregated trace opening and final-LDT proof remain opaque bytes
   whose cryptographic meaning is supplied only by the admission layer.

No Tower constants are copied here.  The XOF is the single shared concrete
backend's cSHAKE controller.  Ext6 challenges are interpreted in Lean as six
BabyBear limbs using the already-defined modulus and `toExt6` construction.
-/

import Compiler.EmitSerialize
import Compiler.GateTraceRelationExt6
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Compiler.Ext6GateProofController

open scoped BigOperators
open Minidregg.Compiler.GateFactoredExt6
open Minidregg.Compiler.GateMleExt6
open Minidregg.Compiler.GateTraceRelationExt6
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Loom Polynomial
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

/-! ## Exact statement and transcript suite -/

/-- The canonical byte representation of the exact Lean descriptor consumed
by this proof.  Native code never gets to author or reinterpret this value. -/
def descriptorBytes (descriptor : ConstraintDescriptor BabyBear) : List UInt8 :=
  (descriptorToJson descriptor).pretty.toUTF8.toList

/-- Interpret one 32-byte cSHAKE digest as six little-endian radix-`babyBearP`
limbs and then use the proved Ext6 constructor.  Bias/ROM security is an
explicit admission premise; this deterministic interpretation claims neither. -/
def digestToExt6 (digest : Digest) : Ext6Q :=
  toExt6 fun i : Fin 6 =>
    ((digest.value / babyBearP ^ i.val) % babyBearP : Nat)

/-- A concrete statement fixes the exact emitted descriptor, its disjoint cube
encoding, its public base-field prefix, and the number of advertised zero
padding cells. -/
structure Statement (m nPadding : Nat) where
  descriptor : ConstraintDescriptor BabyBear
  encoding : Fin (descriptorResiduals descriptor (fun _ => 0)).length ↪
    (Fin m -> Bool)
  publicValues : Fin descriptor.nPublic -> BabyBear

/-- The type of the residual list does not depend on the chosen trace values;
this reuses one statement-owned encoding for every candidate trace. -/
def Statement.encodingFor {m nPadding : Nat} (statement : Statement m nPadding)
    (trace : Nat -> BabyBear) :
    Fin (descriptorResiduals statement.descriptor trace).length ↪ (Fin m -> Bool) := by
  simpa only [descriptorResiduals_length] using statement.encoding

/-- Proof-suite codecs and transcript domains.  They are Lean objects with
round-trip laws, not claims about a native representation. -/
structure Suite where
  babyBearCodecPin : CodecPin
  babyBearCodec : LawfulCodec BabyBear
  ext6CodecPin : CodecPin
  ext6Codec : LawfulCodec Ext6Q
  roundMessageCodecPin : CodecPin
  roundMessageCodec : LawfulCodec (Polynomial Ext6Q)
  gammaDomainId : Digest
  roundDomainId : Digest
  etaDomainId : Digest
  gammaRoundDistinct : gammaDomainId ≠ roundDomainId
  gammaEtaDistinct : gammaDomainId ≠ etaDomainId
  roundEtaDistinct : roundDomainId ≠ etaDomainId
  gammaCustomization : List UInt8
  roundCustomization : List UInt8
  etaCustomization : List UInt8
  gammaRoundCustomizationDistinct : gammaCustomization ≠ roundCustomization
  gammaEtaCustomizationDistinct : gammaCustomization ≠ etaCustomization
  roundEtaCustomizationDistinct : roundCustomization ≠ etaCustomization

/-- The one cSHAKE implementation used throughout this controller. -/
abbrev cshake := Tower256ConcreteBackend.backend.cshake

def encodeDigest (digest : Digest) : List UInt8 :=
  cshake.digestCodec.encode digest

def encodeExt6 (suite : Suite) (value : Ext6Q) : List UInt8 :=
  suite.ext6Codec.encode value

def encodeRoundMessage (suite : Suite) (message : Polynomial Ext6Q) : List UInt8 :=
  suite.roundMessageCodec.encode message

/-! ## Canonical statement preimage -/

variable {m nPadding : Nat}

/-- First-order payload absorbed before any proof root.  Public values are
already encoded by the suite's lawful BabyBear codec; cube rows are literal
Boolean bytes in residual-index then coordinate-index order. -/
structure StatementPreimagePayload where
  descriptor : List UInt8
  rounds : Nat
  padding : Nat
  publicRows : List (List UInt8)
  encodingRows : List (List UInt8)
deriving Repr

private def statementPreimageWireStream :=
  StreamCodec.product Tower256ConcreteBackend.bytesStream <|
    StreamCodec.product StreamCodec.nat <|
      StreamCodec.product StreamCodec.nat <|
        StreamCodec.product
          (StreamCodec.list Tower256ConcreteBackend.bytesStream)
          (StreamCodec.list Tower256ConcreteBackend.bytesStream)

/-- A single prefix-decodable codec fixes the statement framing; callers do
not supply a free transcript byte string. -/
def statementPreimageStream : StreamCodec StatementPreimagePayload :=
  StreamCodec.xmap statementPreimageWireStream
    (fun payload =>
      (payload.descriptor,
        (payload.rounds,
          (payload.padding, (payload.publicRows, payload.encodingRows)))))
    (fun wire =>
      { descriptor := wire.1
        rounds := wire.2.1
        padding := wire.2.2.1
        publicRows := wire.2.2.2.1
        encodingRows := wire.2.2.2.2 })
    (by intro payload; cases payload; rfl)

def statementPreimageCodec : LawfulCodec StatementPreimagePayload :=
  statementPreimageStream.toLawful

def encodeBool : Bool -> UInt8
  | false => 0
  | true => 1

/-- Canonical payload constructor factored out so the component-injectivity
tooth below has no dependent-structure casts. -/
def canonicalPayloadOf (suite : Suite) (m nPadding : Nat)
    (descriptor : ConstraintDescriptor BabyBear)
    (encoding : Fin (descriptorResiduals descriptor (fun _ => 0)).length ↪
      (Fin m -> Bool))
    (publicValues : Fin descriptor.nPublic -> BabyBear) :
    StatementPreimagePayload where
  descriptor := descriptorBytes descriptor
  rounds := m
  padding := nPadding
  publicRows := List.ofFn fun j => suite.babyBearCodec.encode (publicValues j)
  encodingRows := List.ofFn fun k => List.ofFn fun i => encodeBool (encoding k i)

/-- The unique statement preimage absorbed by gamma. -/
def canonicalStatementPreimage (suite : Suite)
    (statement : Statement m nPadding) : List UInt8 :=
  statementPreimageCodec.encode
    (canonicalPayloadOf suite m nPadding statement.descriptor
      statement.encoding statement.publicValues)

private theorem lawfulCodec_encode_injective {alpha : Type}
    (codec : LawfulCodec alpha) : Function.Injective codec.encode := by
  intro left right equal
  have decoded := congrArg codec.decode equal
  rw [codec.decode_encode, codec.decode_encode] at decoded
  exact Option.some.inj decoded

/-- Changing either a public value or a cube-encoding bit changes the canonical
preimage.  This is byte-preimage injectivity only; it claims no digest collision
resistance. -/
theorem canonicalStatementPreimage_components_injective
    (suite : Suite) (m nPadding : Nat)
    (descriptor : ConstraintDescriptor BabyBear)
    (leftEncoding rightEncoding :
      Fin (descriptorResiduals descriptor (fun _ => 0)).length ↪ (Fin m -> Bool))
    (leftPublic rightPublic : Fin descriptor.nPublic -> BabyBear)
    (equal : statementPreimageCodec.encode
        (canonicalPayloadOf suite m nPadding descriptor leftEncoding leftPublic) =
      statementPreimageCodec.encode
        (canonicalPayloadOf suite m nPadding descriptor rightEncoding rightPublic)) :
    leftPublic = rightPublic ∧ leftEncoding = rightEncoding := by
  have payloadEqual := lawfulCodec_encode_injective statementPreimageCodec equal
  have publicRowsEqual := congrArg StatementPreimagePayload.publicRows payloadEqual
  have encodingRowsEqual := congrArg StatementPreimagePayload.encodingRows payloadEqual
  constructor
  · funext j
    have rowEqual := congrFun (List.ofFn_inj.mp publicRowsEqual) j
    exact lawfulCodec_encode_injective suite.babyBearCodec rowEqual
  · apply DFunLike.coe_injective
    funext k i
    have outerEqual := congrFun (List.ofFn_inj.mp encodingRowsEqual) k
    have bitEqual := congrFun (List.ofFn_inj.mp outerEqual) i
    cases hleft : leftEncoding k i <;> cases hright : rightEncoding k i <;>
      simp [encodeBool, hleft, hright] at bitEqual ⊢

/-! ## Native receipt data -/

/-- All proof data is inert until the Lean relation below accepts it.  PCS and
LDT proofs remain byte strings; the native boundary contains no verdict. -/
structure Receipt (m : Nat) where
  traceRoot : Digest
  operandRoot : Fin 7 -> Digest
  gamma : Ext6Q
  roundMessage : Fin m -> Polynomial Ext6Q
  roundChallenge : Fin m -> Ext6Q
  terminalValue : Fin 7 -> Ext6Q
  eta : Ext6Q
  aggregateValue : Ext6Q
  traceOpeningProof : List UInt8
  operandOpeningProof : Fin 7 -> List UInt8
  finalLdtProof : List UInt8

variable {m nPadding : Nat}

/-- Prefix committed before `gamma`: the canonical statement preimage (exact
descriptor, dimensions, public values, and cube encoding) and the base-trace
commitment root. -/
def gammaInput (suite : Suite) (statement : Statement m nPadding)
    (receipt : Receipt m) : List UInt8 :=
  envelope (canonicalStatementPreimage suite statement) ++
    envelope (encodeDigest suite.gammaDomainId) ++
    envelope (encodeDigest receipt.traceRoot)

def derivedGamma (suite : Suite) (statement : Statement m nPadding)
    (receipt : Receipt m) : Ext6Q :=
  digestToExt6 (cshake.xofDigest suite.gammaCustomization
    (gammaInput suite statement receipt))

/-- Prefix after `gamma` and before the first sumcheck message.  The seven
operand commitments are in the exact `terminalOrder` index order. -/
def operandPrefix (suite : Suite) (statement : Statement m nPadding)
    (receipt : Receipt m) : List UInt8 :=
  gammaInput suite statement receipt ++
    envelope (encodeExt6 suite receipt.gamma) ++
    (List.ofFn fun j : Fin 7 =>
      envelope (encodeLength j) ++ envelope (encodeDigest (receipt.operandRoot j))).flatten

/-- Exact Fiat--Shamir prefix for round `i`.  Each earlier pair is encoded as
message then challenge; the current message is encoded without its answer. -/
def roundInput (suite : Suite) (statement : Statement m nPadding)
    (receipt : Receipt m) (i : Fin m) : List UInt8 :=
  operandPrefix suite statement receipt ++
    envelope (encodeDigest suite.roundDomainId) ++
    (List.ofFn fun k : Fin ((i : Nat) + 1) =>
      have hkm : (k : Nat) < m := lt_of_lt_of_le k.isLt (Nat.succ_le_iff.mpr i.isLt)
      let message := receipt.roundMessage ⟨k, hkm⟩
      envelope (encodeLength k) ++ envelope (encodeRoundMessage suite message) ++
        if hki : (k : Nat) < (i : Nat) then
          envelope (encodeExt6 suite (receipt.roundChallenge ⟨k, lt_trans hki i.isLt⟩))
        else []).flatten

def derivedRoundChallenge (suite : Suite) (statement : Statement m nPadding)
    (receipt : Receipt m) (i : Fin m) : Ext6Q :=
  digestToExt6 (cshake.xofDigest suite.roundCustomization
    (roundInput suite statement receipt i))

/-- All round messages/challenges and all seven terminal values precede eta. -/
def etaInput (suite : Suite) (statement : Statement m nPadding)
    (receipt : Receipt m) : List UInt8 :=
  operandPrefix suite statement receipt ++
    (List.ofFn fun i : Fin m =>
      envelope (encodeLength i) ++
        envelope (encodeRoundMessage suite (receipt.roundMessage i)) ++
        envelope (encodeExt6 suite (receipt.roundChallenge i))).flatten ++
    envelope (encodeDigest suite.etaDomainId) ++
    (List.ofFn fun j : Fin 7 =>
      envelope (encodeLength j) ++ envelope (encodeExt6 suite (receipt.terminalValue j))).flatten

def derivedEta (suite : Suite) (statement : Statement m nPadding)
    (receipt : Receipt m) : Ext6Q :=
  digestToExt6 (cshake.xofDigest suite.etaCustomization
    (etaInput suite statement receipt))

/-! ## Lean-owned algebraic acceptance -/

/-- Runtime order is exactly `(mulA,mulB,mulC,addA,addB,addC,zero)`. -/
def terminalExpression (values : Fin 7 -> Ext6Q) : Ext6Q :=
  values 0 * values 1 - values 2 + values 3 + values 4 - values 5 + values 6

/-- The aggregate equation checked after fresh eta.  The constants and weights
are derived from the exact descriptor, exact `gamma`, and exact sumcheck point;
only the claimed aggregate value comes from the receipt. -/
def etaAggregateLeft (statement : Statement m nPadding)
    (receipt : Receipt m) : Ext6Q :=
  let trace0 : Nat -> BabyBear := fun _ => 0
  let enc := statement.encodingFor trace0
  let terminal := fun j : Fin 7 =>
    terminalFunctional (terminalOrder j) statement.descriptor trace0 enc
      receipt.gamma receipt.roundChallenge
  let values := extendedValues (nPadding := nPadding) receipt.terminalValue
    (fun j => algebraMap BabyBear Ext6Q (statement.publicValues j))
  let constants := extendedConstants
    (nPublic := statement.descriptor.nPublic) (nPadding := nPadding) terminal
  ∑ j : Fin (7 + statement.descriptor.nPublic + nPadding),
    receipt.eta ^ j.val * (values j - constants j)

/-- Totalized views used by `scChain`; the verifier never reads them beyond
the statically fixed `m` rounds. -/
def roundMessages (receipt : Receipt m) : Nat -> Polynomial Ext6Q := fun i =>
  if h : i < m then receipt.roundMessage ⟨i, h⟩ else 0

def roundChallenges (receipt : Receipt m) : Nat -> Ext6Q := fun i =>
  if h : i < m then receipt.roundChallenge ⟨i, h⟩ else 0

/-- The exact deterministic relation reflected by the verifier.  Cryptographic
authentication is absent by design and is joined in the admission module. -/
def Accepts (suite : Suite) (statement : Statement m nPadding)
    (receipt : Receipt m) : Prop :=
  receipt.gamma = derivedGamma suite statement receipt ∧
  (∀ i, receipt.roundChallenge i =
    derivedRoundChallenge suite statement receipt i) ∧
  receipt.eta = derivedEta suite statement receipt ∧
  (∀ i : Fin m, (receipt.roundMessage i).degree < ((2 + 1 : Nat) : WithBot Nat)) ∧
  (∀ i : Fin m,
    (receipt.roundMessage i).eval 0 + (receipt.roundMessage i).eval 1 =
      scChain 0 (roundMessages receipt) (roundChallenges receipt) i) ∧
  scChain 0 (roundMessages receipt) (roundChallenges receipt) m =
    terminalExpression receipt.terminalValue ∧
  etaAggregateLeft statement receipt = receipt.aggregateValue

/-- A reflected verifier fixes the receipt codec in Lean.  The Boolean checker
may be emitted later; its theorem is the only semantics it has. -/
structure Verifier (suite : Suite) (statement : Statement m nPadding) where
  receiptCodecPin : CodecPin
  receiptCodec : LawfulCodec (Receipt m)
  check : Receipt m -> Bool
  check_iff : ∀ receipt, check receipt = true ↔ Accepts suite statement receipt

abbrev OpaqueProofRunner (Error : Type) :=
  List UInt8 -> Except Error (List UInt8)

inductive Failure (Error : Type)
  | native (error : Error)
  | invalidEncoding
  | rejected
deriving Repr

structure AcceptedReceipt (suite : Suite) (statement : Statement m nPadding)
    (verifier : Verifier suite statement) (request : List UInt8) where
  proofBytes : List UInt8
  receipt : Receipt m
  decoded : verifier.receiptCodec.decode proofBytes = some receipt
  accepted : Accepts suite statement receipt

def run {Error : Type} (suite : Suite) (statement : Statement m nPadding)
    (verifier : Verifier suite statement) (runner : OpaqueProofRunner Error)
    (request : List UInt8) :
    Except (Failure Error) (AcceptedReceipt suite statement verifier request) :=
  match runner request with
  | .error error => .error (.native error)
  | .ok proofBytes =>
      match decoded : verifier.receiptCodec.decode proofBytes with
      | none => .error .invalidEncoding
      | some receipt =>
          if checked : verifier.check receipt = true then
            .ok ⟨proofBytes, receipt, decoded, (verifier.check_iff receipt).mp checked⟩
          else .error .rejected

theorem run_success_integrity {Error : Type} (suite : Suite)
    (statement : Statement m nPadding) (verifier : Verifier suite statement)
    (runner : OpaqueProofRunner Error) (request : List UInt8)
    (reply : AcceptedReceipt suite statement verifier request)
    (success : run suite statement verifier runner request = .ok reply) :
    runner request = .ok reply.proofBytes ∧
      verifier.receiptCodec.decode reply.proofBytes = some reply.receipt ∧
      Accepts suite statement reply.receipt := by
  unfold run at success
  split at success
  next error returned => simp at success
  next proofBytes returned =>
    split at success
    next decodeFailed => simp at success
    next receipt decoded =>
      split at success
      next checked =>
        simp only [Except.ok.injEq] at success
        subst reply
        exact ⟨returned, decoded, (verifier.check_iff receipt).mp checked⟩
      next rejected => simp at success

/-- The current round answer cannot affect the bytes hashed to obtain itself. -/
theorem roundInput_eq_of_same_current
    (suite : Suite) (statement : Statement m nPadding)
    (left right : Receipt m) (i : Fin m)
    (sameFixed : left.traceRoot = right.traceRoot ∧
      left.gamma = right.gamma ∧ left.operandRoot = right.operandRoot)
    (sameMessages : ∀ k : Fin m, (k : Nat) ≤ (i : Nat) ->
      left.roundMessage k = right.roundMessage k)
    (samePrior : ∀ k : Fin m, (k : Nat) < (i : Nat) ->
      left.roundChallenge k = right.roundChallenge k) :
    roundInput suite statement left i = roundInput suite statement right i := by
  rcases sameFixed with ⟨hroot, hgamma, hroots⟩
  unfold roundInput operandPrefix gammaInput
  rw [hroot, hgamma, hroots]
  congr 1
  apply congrArg List.flatten
  apply List.ofFn_inj.mpr
  funext k
  have hkm : (k : Nat) < m := lt_of_lt_of_le k.isLt (Nat.succ_le_iff.mpr i.isLt)
  have hki : (k : Nat) ≤ (i : Nat) := Nat.lt_succ_iff.mp k.isLt
  dsimp only
  rw [sameMessages ⟨k, hkm⟩ hki]
  split
  · rename_i prior
    rw [samePrior ⟨k, hkm⟩ prior]
  · rfl

#print axioms run_success_integrity
#print axioms roundInput_eq_of_same_current
#print axioms canonicalStatementPreimage_components_injective

end

end Minidregg.Compiler.Ext6GateProofController
