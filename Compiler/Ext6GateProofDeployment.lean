/-
# Compiler.Ext6GateProofDeployment -- a closed Ext6 control deployment

This module closes the first-order carriers needed to run the Ext6 gate-proof
controller: suite and controller identities, versioned lawful codecs, one
nontrivial emitted statement, and the reflected bytes/error verifier.

The codecs below are total proof-side enumeration codecs.  They make the Lean
carrier concrete and injective, but are deliberately not advertised as a
released native ABI: `Ext6Q` is currently noncomputable.  A future executable
wire codec may replace them only under new versioned pins.

Nothing here is a PCS, proximity, binding, random-oracle, challenge-sampling,
or final-LDT theorem.  Native authority still ends at bytes or an opaque error;
only Lean decoding and `Accepts` can produce an accepted receipt.
-/

import Compiler.Ext6GateProofController
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Logic.Equiv.List

namespace Minidregg.Compiler.Ext6GateProofDeployment

open Minidregg.Compiler.Ext6GateProofController
open Minidregg.Compiler.GateMleExt6
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

/-! ## Versioned identity and proof-side codecs -/

def suiteId : Digest := ⟨986000⟩
def controllerId : Digest := ⟨986001⟩

def babyBearCodecPin : CodecPin := ⟨⟨986010⟩, ⟨986011⟩, 1⟩
def ext6CodecPin : CodecPin := ⟨⟨986012⟩, ⟨986013⟩, 1⟩
def roundMessageCodecPin : CodecPin := ⟨⟨986014⟩, ⟨986015⟩, 1⟩
def receiptCodecPin : CodecPin := ⟨⟨986016⟩, ⟨986017⟩, 1⟩

theorem suiteId_nonzero : suiteId ≠ ⟨0⟩ := by decide
theorem controllerId_nonzero : controllerId ≠ ⟨0⟩ := by decide

/-- The assigned identity pair carried by this exact deployment. -/
structure DeploymentIdentity where
  suiteId : Digest
  controllerId : Digest
  suiteAssigned : suiteId ≠ ⟨0⟩
  controllerAssigned : controllerId ≠ ⟨0⟩
  rolesDistinct : suiteId ≠ controllerId

def identity : DeploymentIdentity where
  suiteId := suiteId
  controllerId := controllerId
  suiteAssigned := suiteId_nonzero
  controllerAssigned := controllerId_nonzero
  rolesDistinct := by decide

@[simp] theorem identity_suiteId : identity.suiteId = suiteId := rfl
@[simp] theorem identity_controllerId : identity.controllerId = controllerId := rfl

/-- A total lawful codec for any countable proof-side carrier.  The chosen
enumeration is part of the pin version; it is not a native executability claim. -/
noncomputable def countableCodec (alpha : Type*) [Countable alpha] :
    LawfulCodec alpha := by
  letI : Encodable alpha := Encodable.ofCountable alpha
  exact
    { encode := fun value => StreamCodec.nat.toLawful.encode (Encodable.encode value)
      decode := fun bytes =>
        match StreamCodec.nat.toLawful.decode bytes with
        | some value => Encodable.decode value
        | none => none
      decode_encode := by
        intro value
        change (match StreamCodec.nat.toLawful.decode
          (StreamCodec.nat.toLawful.encode (Encodable.encode value)) with
          | some value => Encodable.decode value
          | none => none) = some value
        rw [StreamCodec.nat.toLawful.decode_encode]
        exact Encodable.encodek value }

def gammaDomainId : Digest := ⟨986020⟩
def roundDomainId : Digest := ⟨986021⟩
def etaDomainId : Digest := ⟨986022⟩

def gammaCustomization : List UInt8 :=
  [0x45, 0x36, 0x47, 0x31]
def roundCustomization : List UInt8 :=
  [0x45, 0x36, 0x52, 0x31]
def etaCustomization : List UInt8 :=
  [0x45, 0x36, 0x45, 0x31]

local instance polynomialCountable (alpha : Type*) [Countable alpha] [Semiring alpha] :
    Countable (Polynomial alpha) := by
  letI : Countable (AddMonoidAlgebra alpha Nat) := by
    change Countable (Nat →₀ alpha)
    infer_instance
  exact Polynomial.toFinsupp_injective.countable

local instance ext6Countable : Countable Ext6Q := by
  exact (AdjoinRoot.mk_surjective (g := ext6Polynomial)).countable

local instance digestCountable : Countable Digest := by
  exact (show Function.Injective Digest.value from by
    intro left right equal
    cases left
    cases right
    cases equal
    rfl).countable

local instance uint8Countable : Countable UInt8 := by
  exact (show Function.Injective UInt8.toFin from by
    intro left right equal
    rw [← UInt8.ofFin_toFin left, ← UInt8.ofFin_toFin right, equal]).countable

/-- A complete inhabitant of the controller's proof-suite carrier. -/
noncomputable def suite : Suite where
  babyBearCodecPin := babyBearCodecPin
  babyBearCodec := countableCodec BabyBear
  ext6CodecPin := ext6CodecPin
  ext6Codec := countableCodec Ext6Q
  roundMessageCodecPin := roundMessageCodecPin
  roundMessageCodec := countableCodec (Polynomial Ext6Q)
  gammaDomainId := gammaDomainId
  roundDomainId := roundDomainId
  etaDomainId := etaDomainId
  gammaRoundDistinct := by decide
  gammaEtaDistinct := by decide
  roundEtaDistinct := by decide
  gammaCustomization := gammaCustomization
  roundCustomization := roundCustomization
  etaCustomization := etaCustomization
  gammaRoundCustomizationDistinct := by decide
  gammaEtaCustomizationDistinct := by decide
  roundEtaCustomizationDistinct := by decide

instance suiteNonempty : Nonempty Suite := ⟨suite⟩

@[simp] theorem suite_babyBear_codec_roundtrip (value : BabyBear) :
    suite.babyBearCodec.decode (suite.babyBearCodec.encode value) = some value :=
  suite.babyBearCodec.decode_encode value

@[simp] theorem suite_ext6_codec_roundtrip (value : Ext6Q) :
    suite.ext6Codec.decode (suite.ext6Codec.encode value) = some value :=
  suite.ext6Codec.decode_encode value

/-! ## One nontrivial emitted statement -/

abbrev Rounds : Nat := 5
abbrev Padding : Nat := 8

theorem demoResidualCount :
    (descriptorResiduals demoDescriptor (fun _ => 0)).length = 23 := by
  decide

/-- The 23 residual coordinates of the emitted range descriptor occupy
distinct points of the five-dimensional Boolean cube. -/
noncomputable def demoEncoding :
    Fin (descriptorResiduals demoDescriptor (fun _ => 0)).length ↪
      (Fin Rounds → Bool) where
  toFun index := (Fintype.equivFin (Fin Rounds → Bool)).symm
    ⟨index.val, by
      have hi : index.val < 23 := by
        simpa only [demoResidualCount] using index.isLt
      have hi32 : index.val < 32 := lt_trans hi (by omega)
      simpa [Rounds] using hi32⟩
  inj' := by
    intro left right equal
    have castEqual := (Fintype.equivFin (Fin Rounds → Bool)).symm.injective equal
    apply Fin.ext
    simpa using congrArg
      (fun index : Fin (Fintype.card (Fin Rounds → Bool)) => index.val)
      castEqual

/-- The deployed demo statement proves the emitted four-bit range descriptor
with public value `13`, over five sumcheck rounds and eight advertised padding
cells. -/
noncomputable def statement : Statement Rounds Padding where
  descriptor := demoDescriptor
  encoding := demoEncoding
  publicValues := fun _ => 13

instance statementNonempty : Nonempty (Statement Rounds Padding) := ⟨statement⟩

@[simp] theorem statement_descriptor : statement.descriptor = demoDescriptor := rfl
@[simp] theorem statement_public (i : Fin statement.descriptor.nPublic) :
    statement.publicValues i = 13 := rfl

/-! ## Reflected verifier and opaque runner framing -/

abbrev ReceiptCarrier (m : Nat) :=
  Digest × (Fin 7 → Digest) × Ext6Q ×
  (Fin m → Polynomial Ext6Q) × (Fin m → Ext6Q) ×
  (Fin 7 → Ext6Q) × Ext6Q × Ext6Q ×
  List UInt8 × (Fin 7 → List UInt8) × List UInt8

def receiptCarrier (receipt : Receipt Rounds) : ReceiptCarrier Rounds :=
  (receipt.traceRoot, receipt.operandRoot, receipt.gamma,
    receipt.roundMessage, receipt.roundChallenge, receipt.terminalValue,
    receipt.eta, receipt.aggregateValue, receipt.traceOpeningProof,
    receipt.operandOpeningProof, receipt.finalLdtProof)

theorem receiptCarrier_injective : Function.Injective receiptCarrier := by
  intro left right equal
  rcases left with ⟨leftTrace, leftOperands, leftGamma, leftMessages,
    leftChallenges, leftTerminals, leftEta, leftAggregate, leftTraceProof,
    leftOperandProofs, leftFinalProof⟩
  rcases right with ⟨rightTrace, rightOperands, rightGamma, rightMessages,
    rightChallenges, rightTerminals, rightEta, rightAggregate, rightTraceProof,
    rightOperandProofs, rightFinalProof⟩
  have fields :
      leftTrace = rightTrace ∧ leftOperands = rightOperands ∧
      leftGamma = rightGamma ∧ leftMessages = rightMessages ∧
      leftChallenges = rightChallenges ∧ leftTerminals = rightTerminals ∧
      leftEta = rightEta ∧ leftAggregate = rightAggregate ∧
      leftTraceProof = rightTraceProof ∧
      leftOperandProofs = rightOperandProofs ∧
      leftFinalProof = rightFinalProof := by
    simpa only [receiptCarrier, Prod.mk.injEq] using equal
  rcases fields with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

local instance receiptCountable : Countable (Receipt Rounds) :=
  receiptCarrier_injective.countable

noncomputable def check (receipt : Receipt Rounds) : Bool := by
  classical
  exact decide (Accepts suite statement receipt)

theorem check_iff (receipt : Receipt Rounds) :
    check receipt = true ↔ Accepts suite statement receipt := by
  classical
  simp [check]

/-- A complete verifier carrier: exact receipt codec, Lean checker, and the
reflection theorem connecting the Boolean result to the controller relation. -/
noncomputable def verifier : Verifier suite statement where
  receiptCodecPin := receiptCodecPin
  receiptCodec := countableCodec (Receipt Rounds)
  check := check
  check_iff := check_iff

instance verifierNonempty : Nonempty (Verifier suite statement) := ⟨verifier⟩

def nativeErrorRunner {Error : Type} (error : Error) : OpaqueProofRunner Error :=
  fun _ => .error error

@[simp] theorem run_native_error {Error : Type} (error : Error)
    (request : List UInt8) :
    run suite statement verifier (nativeErrorRunner error) request =
      .error (.native error) := by
  simp [run, nativeErrorRunner]

/-- The empty byte string is not a valid receipt in the compact enumeration
framing, so a native success flag alone cannot cross the Lean boundary. -/
def malformedRunner : OpaqueProofRunner Unit := fun _ => .ok []

@[simp] theorem verifier_decode_empty : verifier.receiptCodec.decode [] = none := by
  simp [verifier, countableCodec, StreamCodec.toLawful, StreamCodec.nat,
    StreamCodec.decodeNatPrefix]

/-- A successful opaque run proves exactly byte retention, lawful decoding,
and the deterministic controller relation.  No security premise occurs. -/
theorem success_control_only {Error : Type} (runner : OpaqueProofRunner Error)
    (request : List UInt8) (reply : AcceptedReceipt suite statement verifier request)
    (success : run suite statement verifier runner request = .ok reply) :
    runner request = .ok reply.proofBytes ∧
      verifier.receiptCodec.decode reply.proofBytes = some reply.receipt ∧
      Accepts suite statement reply.receipt :=
  run_success_integrity suite statement verifier runner request reply success

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.Ext6GateProofDeployment.demoResidualCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demoResidualCount
/-- info: 'Minidregg.Compiler.Ext6GateProofDeployment.success_control_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success_control_only

end

end Minidregg.Compiler.Ext6GateProofDeployment
