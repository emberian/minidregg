/-
# `Compiler.DialectBundle` — typed heterogeneous closure before receipts

This file supplies one small enabling algebra for the compiler spine:

* a dialect is anchored by the `Signature` whose free terms it compiles;
* exposed input/output ports retain their payload type and a semantic fingerprint;
* closure mechanisms stay honest (`airConstrained` is not renamed a seam, and a
  native check is not renamed a proof);
* heterogeneous composition computes the meet (weakest common assurance) of its
  producer, consumer, and link closures; and
* the strongest receipt view requires BOTH proof-verified assurance and a closed
  boundary.  Negative theorems show that a crypto/native floor, refusal, or an
  exposed port cannot be promoted into that view.

This is deliberately not a runtime receipt format and does not choose a digest
algorithm.  `SemanticFingerprint` stores digest words behind a payload-type phantom
index; a deployment dialect may interpret those words using its versioned canonical
hash scheme.  No Breadstuffs IR or port representation is imported.
-/
import Compiler.Signature

namespace Minidregg.Compiler

universe uSig vSig uPayload uArtifact

/-! ## Dialects and typed semantic fingerprints -/

/-- A compilation dialect is anchored by its source signature.  Runtime schemas,
target IRs, and receipt encodings are intentionally outside this bounded module. -/
structure Dialect where
  signature : Signature.{uSig, vSig}

/-- Source terms of a dialect use the repository's existing initial algebra. -/
abbrev Dialect.Term (D : Dialect.{uSig, vSig}) : Type max uSig vSig :=
  Minidregg.Compiler.Term D.signature

/-- A semantic fingerprint indexed by the type of value crossing a port.

The phantom `Payload` index prevents a fingerprint for one payload type from being
silently used for another.  The words are deliberately algorithm-neutral here: a
concrete dialect must obtain them from its canonical, domain-separated encoding. -/
structure SemanticFingerprint (Payload : Type uPayload) where
  words : List UInt64
deriving DecidableEq, Repr

/-- Direction is part of a port's type, so producer/producer and consumer/consumer
connections are not accepted by `PortMatch`. -/
inductive PortDirection
  | input
  | output
deriving DecidableEq, Repr

/-- An exposed port keeps the dialect, payload, and direction in its type and the
semantic fingerprint in its value.  Two different dialects can still connect when
they expose the same payload semantics. -/
structure ExposedPort (D : Dialect.{uSig, vSig}) (Payload : Type uPayload)
    (direction : PortDirection) where
  label : String
  fingerprint : SemanticFingerprint Payload
deriving Repr

/-- A typed heterogeneous connection: output to input, with exact semantic
fingerprint equality.  `Producer` and `Consumer` need not be the same dialect. -/
structure PortMatch
    {Producer Consumer : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    (outPort : ExposedPort Producer Payload .output)
    (inPort : ExposedPort Consumer Payload .input) : Prop where
  sameFingerprint : outPort.fingerprint = inPort.fingerprint

/-! ## Closure classes and the assurance meet lattice -/

/-- The mechanism by which one compilation fragment or link claims closure.

The first three mechanisms are eligible for the proof-verified assurance grade.
The remaining constructors are explicit trust floors or rejection; none can be
silently promoted by composition. -/
inductive ClosureClass
  | airConstrained
  | seamCertified
  | proofEngineBound
  | cryptoFloor
  | nativeChecked
  | refused
deriving DecidableEq, Repr

/-- Aggregate assurance.  This is a small honest lattice, not a total ranking:
`cryptoFloor` and `nativeChecked` are incomparable.  Their meet is `nonProof`, the
shared statement that some non-proof obligation remains. -/
inductive TrustGrade
  | refused
  | nonProof
  | cryptoFloor
  | nativeChecked
  | proofVerified
deriving DecidableEq, Repr

namespace TrustGrade

/-- Meet computes the weakest assurance supported by both inputs.

`proofVerified` is top, `refused` is bottom, and the incomparable crypto/native
floors meet at `nonProof`. -/
def meet : TrustGrade → TrustGrade → TrustGrade
  | .refused, _ | _, .refused => .refused
  | .proofVerified, b => b
  | a, .proofVerified => a
  | .nonProof, _ | _, .nonProof => .nonProof
  | .cryptoFloor, .cryptoFloor => .cryptoFloor
  | .nativeChecked, .nativeChecked => .nativeChecked
  | .cryptoFloor, .nativeChecked | .nativeChecked, .cryptoFloor => .nonProof

instance : Min TrustGrade := ⟨meet⟩

@[simp] theorem meet_refused_left (a : TrustGrade) : meet .refused a = .refused := by
  cases a <;> rfl

@[simp] theorem meet_refused_right (a : TrustGrade) : meet a .refused = .refused := by
  cases a <;> rfl

@[simp] theorem meet_proofVerified_left (a : TrustGrade) :
    meet .proofVerified a = a := by
  cases a <;> rfl

@[simp] theorem meet_proofVerified_right (a : TrustGrade) :
    meet a .proofVerified = a := by
  cases a <;> rfl

theorem meet_comm (a b : TrustGrade) : meet a b = meet b a := by
  cases a <;> cases b <;> rfl

theorem meet_assoc (a b c : TrustGrade) : meet (meet a b) c = meet a (meet b c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem meet_self (a : TrustGrade) : meet a a = a := by
  cases a <;> rfl

/-- The meet has strongest assurance exactly when both operands do.  This is the
central anti-promotion tooth used below. -/
theorem meet_eq_proofVerified_iff (a b : TrustGrade) :
    meet a b = .proofVerified ↔ a = .proofVerified ∧ b = .proofVerified := by
  cases a <;> cases b <;> decide

end TrustGrade

/-- The assurance honestly provided by each closure mechanism. -/
def ClosureClass.trust : ClosureClass → TrustGrade
  | .airConstrained | .seamCertified | .proofEngineBound => .proofVerified
  | .cryptoFloor => .cryptoFloor
  | .nativeChecked => .nativeChecked
  | .refused => .refused

/-- Weakest assurance of three closure obligations (producer, consumer, link).
Associativity of `meet` makes the bracketing semantically irrelevant. -/
def weakestOfThree (a b c : ClosureClass) : TrustGrade :=
  TrustGrade.meet (TrustGrade.meet a.trust b.trust) c.trust

/-- A three-way composition is strongest exactly when all three mechanisms are
proof-verified mechanisms. -/
theorem weakestOfThree_eq_proofVerified_iff (a b c : ClosureClass) :
    weakestOfThree a b c = .proofVerified ↔
      a.trust = .proofVerified ∧ b.trust = .proofVerified ∧ c.trust = .proofVerified := by
  unfold weakestOfThree
  rw [TrustGrade.meet_eq_proofVerified_iff, TrustGrade.meet_eq_proofVerified_iff]
  tauto

/-! ## Open fragments and heterogeneous composition -/

/-- A compiled source fragment with exactly one exposed typed port.

The closure class is a type index, so composition cannot overwrite it.  The term is
the current `Signature.Term`; no second source syntax is introduced. -/
structure OpenFragment (D : Dialect.{uSig, vSig}) (Payload : Type uPayload)
    (direction : PortDirection) (closure : ClosureClass) where
  source : D.Term
  port : ExposedPort D Payload direction

/-- A heterogeneous output/input composition.  The connection closes the displayed
ports, and its aggregate trust is computed rather than supplied by the caller. -/
structure Composition
    (Producer Consumer : Dialect.{uSig, vSig}) (Payload : Type uPayload)
    (producerClosure consumerClosure linkClosure : ClosureClass) where
  producer : OpenFragment Producer Payload .output producerClosure
  consumer : OpenFragment Consumer Payload .input consumerClosure
  matched : PortMatch producer.port consumer.port

/-- The aggregate assurance of a composition is the weakest of its two fragments
and the link mechanism. -/
def Composition.trust
    {Producer Consumer : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    {producerClosure consumerClosure linkClosure : ClosureClass}
    (_ : Composition Producer Consumer Payload
      producerClosure consumerClosure linkClosure) : TrustGrade :=
  weakestOfThree producerClosure consumerClosure linkClosure

/-! ## Strongest-receipt eligibility and anti-promotion teeth -/

/-- Whether an artifact boundary still has an exposed semantic port. -/
inductive BoundaryState
  | closed
  | exposed
deriving DecidableEq, Repr

/-- The minimal view used to gate construction of the strongest receipt class. -/
structure ReceiptView where
  trust : TrustGrade
  boundary : BoundaryState
deriving DecidableEq, Repr

/-- Strongest proof-verified receipts require proof assurance and no exposed port. -/
def ReceiptView.StrongestEligible (view : ReceiptView) : Prop :=
  view.trust = .proofVerified ∧ view.boundary = .closed

/-- The strongest receipt is indexed by the artifact type and by the function that
computes its receipt view.  It cannot substitute an unrelated caller-supplied view:
eligibility is checked against `viewOf artifact` itself.  Later runtime work may add
claims/evidence without weakening this constructor boundary. -/
structure ProofVerifiedReceipt (Artifact : Type uArtifact)
    (viewOf : Artifact → ReceiptView) where
  artifact : Artifact
  eligible : (viewOf artifact).StrongestEligible

/-- An open fragment remains visibly exposed even if its local mechanism is a
proof-verified one. -/
def OpenFragment.receiptView
    {D : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    {direction : PortDirection} {closure : ClosureClass}
    (_ : OpenFragment D Payload direction closure) : ReceiptView :=
  ⟨closure.trust, .exposed⟩

/-- The displayed matched pair has a closed boundary; its trust is still the
computed meet of all closure mechanisms. -/
def Composition.receiptView
    {Producer Consumer : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    {producerClosure consumerClosure linkClosure : ClosureClass}
    (composition : Composition Producer Consumer Payload
      producerClosure consumerClosure linkClosure) : ReceiptView :=
  ⟨composition.trust, .closed⟩

/-- **Unclosed-port tooth.** No fragment with an exposed port can be promoted to
the strongest receipt, even when its local constraints are proof-verified. -/
theorem OpenFragment.exposed_not_strongestEligible
    {D : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    {direction : PortDirection} {closure : ClosureClass}
    (fragment : OpenFragment D Payload direction closure) :
    ¬ fragment.receiptView.StrongestEligible := by
  intro h
  exact BoundaryState.noConfusion h.2

/-- Artifact-indexed form of the unclosed-port tooth: the strongest receipt type
for open fragments is empty. -/
theorem OpenFragment.noProofVerifiedReceipt
    {D : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    {direction : PortDirection} {closure : ClosureClass} :
    IsEmpty (ProofVerifiedReceipt
      (OpenFragment D Payload direction closure) OpenFragment.receiptView) := by
  constructor
  intro receipt
  exact receipt.artifact.exposed_not_strongestEligible receipt.eligible

/-- **Native-link tooth.** A native-checked weld cannot be promoted through otherwise
proof-verified producer and consumer fragments. -/
theorem Composition.nativeLink_not_strongestEligible
    {Producer Consumer : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    {producerClosure consumerClosure : ClosureClass}
    (composition : Composition Producer Consumer Payload
      producerClosure consumerClosure .nativeChecked) :
    ¬ composition.receiptView.StrongestEligible := by
  intro h
  have hall := (weakestOfThree_eq_proofVerified_iff
    producerClosure consumerClosure .nativeChecked).mp h.1
  exact TrustGrade.noConfusion hall.2.2

/-- Artifact-indexed form of the native-link tooth: there is no strongest receipt
whose artifact is such a composition. -/
theorem Composition.noProofVerifiedReceipt_nativeLink
    {Producer Consumer : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    {producerClosure consumerClosure : ClosureClass} :
    IsEmpty (ProofVerifiedReceipt
      (Composition Producer Consumer Payload
        producerClosure consumerClosure .nativeChecked)
      Composition.receiptView) := by
  constructor
  intro receipt
  exact receipt.artifact.nativeLink_not_strongestEligible receipt.eligible

/-- **Cryptographic-floor tooth.** A cryptographic assumption is recorded as a
floor; it is not silently upgraded into a proof-verified link. -/
theorem Composition.cryptoLink_not_strongestEligible
    {Producer Consumer : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    {producerClosure consumerClosure : ClosureClass}
    (composition : Composition Producer Consumer Payload
      producerClosure consumerClosure .cryptoFloor) :
    ¬ composition.receiptView.StrongestEligible := by
  intro h
  have hall := (weakestOfThree_eq_proofVerified_iff
    producerClosure consumerClosure .cryptoFloor).mp h.1
  exact TrustGrade.noConfusion hall.2.2

/-- Artifact-indexed form of the cryptographic-floor tooth. -/
theorem Composition.noProofVerifiedReceipt_cryptoLink
    {Producer Consumer : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    {producerClosure consumerClosure : ClosureClass} :
    IsEmpty (ProofVerifiedReceipt
      (Composition Producer Consumer Payload
        producerClosure consumerClosure .cryptoFloor)
      Composition.receiptView) := by
  constructor
  intro receipt
  exact receipt.artifact.cryptoLink_not_strongestEligible receipt.eligible

/-- **Refusal tooth.** A refused link remains refused under every composition. -/
theorem Composition.refusedLink_not_strongestEligible
    {Producer Consumer : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    {producerClosure consumerClosure : ClosureClass}
    (composition : Composition Producer Consumer Payload
      producerClosure consumerClosure .refused) :
    ¬ composition.receiptView.StrongestEligible := by
  intro h
  have hall := (weakestOfThree_eq_proofVerified_iff
    producerClosure consumerClosure .refused).mp h.1
  exact TrustGrade.noConfusion hall.2.2

/-- Positive non-vacuity: an AIR-constrained producer, seam-certified consumer, and
proof-engine-bound link do retain the strongest assurance after composition. -/
theorem Composition.proofClosures_strongestEligible
    {Producer Consumer : Dialect.{uSig, vSig}} {Payload : Type uPayload}
    (composition : Composition Producer Consumer Payload
      .airConstrained .seamCertified .proofEngineBound) :
    composition.receiptView.StrongestEligible := by
  exact ⟨rfl, rfl⟩

/-! The three computed examples make the non-linear lattice executable: proof is
top, a single floor survives against proof, and mixed floors expose `nonProof`. -/

example : weakestOfThree .airConstrained .seamCertified .proofEngineBound =
    .proofVerified := rfl

example : weakestOfThree .airConstrained .seamCertified .nativeChecked =
    .nativeChecked := rfl

example : weakestOfThree .cryptoFloor .proofEngineBound .nativeChecked =
    .nonProof := rfl

end Minidregg.Compiler
