/-
# Compiler.Tower256CshakeMerkleBinding -- position binding reduces to XOF collisions

`Tower256CshakeMerkleController` proves honest opening correctness, but quite
deliberately does not manufacture collision resistance.  This module closes
the standard deterministic part of that security argument:

* the exact cSHAKE customization and framed byte inputs of leaf and node
  collisions are first-order Lean propositions;
* the unary-length envelope is parsed and proved injective, so lawful value
  and digest codecs really do distinguish the framed XOF inputs;
* every accepted proof decodes to a path of exactly the tree depth;
* two accepted different values at one `(root, index)` yield a concrete leaf
  or node collision; consequently collision-freedom implies the controller's
  exact `CommitmentScheme.PositionBinding` proposition; and
* a generic monotone event pricer transports the binding-failure price to the
  collision-event price without asserting any cSHAKE probability, CR theorem,
  random-oracle model, or native semantics.

The collision-free corollary is the ideal logical form needed by the existing
universal `PositionBinding` field.  A deployed computational statement should
use `bindingFailure_price_le_collision`: its collision probability/advantage
remains an explicit cryptographic premise rather than a Lean theorem here.
-/

import Compiler.Tower256CshakeMerkleController

namespace Minidregg.Compiler.Tower256CshakeMerkleBinding

open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Loom
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## The exact framed collision event -/

/-- The actual byte input used by `MerkleDomains.hashLeaf`. -/
def leafInput {Representation : Type*} (codec : LawfulCodec Representation)
    (value : Representation) : List UInt8 :=
  0 :: envelope (codec.encode value)

/-- The actual byte input used by `MerkleDomains.hashNode`. -/
def nodeInput (cshake : Cshake256) (left right : Digest) : List UInt8 :=
  1 :: envelope (cshake.digestCodec.encode left) ++
    envelope (cshake.digestCodec.encode right)

/-- One concrete same-customization collision in the Lean-selected XOF.  This
is an event/premise, not a theorem that cSHAKE is collision resistant. -/
structure FramedXofCollision (cshake : Cshake256)
    (customization leftInput rightInput : List UInt8) : Prop where
  inputsDifferent : leftInput ≠ rightInput
  digestsEqual :
    cshake.xofDigest customization leftInput =
      cshake.xofDigest customization rightInput

/-- A collision in the exact leaf framing of this Merkle suite. -/
def LeafCollision {Representation : Type*} {cshake : Cshake256}
    (domains : MerkleDomains cshake) (codec : LawfulCodec Representation) : Prop :=
  ∃ left right,
    FramedXofCollision cshake domains.leafCustomization
      (leafInput codec left) (leafInput codec right)

/-- A collision in the exact binary-node framing of this Merkle suite. -/
def NodeCollision {cshake : Cshake256}
    (domains : MerkleDomains cshake) : Prop :=
  ∃ left₁ right₁ left₂ right₂,
    FramedXofCollision cshake domains.nodeCustomization
      (nodeInput cshake left₁ right₁) (nodeInput cshake left₂ right₂)

/-- The exact collision event to which position-binding failure reduces. -/
def MerkleCollision {Representation : Type*} {cshake : Cshake256}
    (domains : MerkleDomains cshake) (codec : LawfulCodec Representation) : Prop :=
  LeafCollision domains codec ∨ NodeCollision domains

/-- The ideal collision-free premise.  It is useful for the universal logical
`PositionBinding` interface, but is not advertised as a computational cSHAKE
claim; deployment should price `MerkleCollision` as an adversarial event. -/
def MerkleCollisionFree {Representation : Type*} {cshake : Cshake256}
    (domains : MerkleDomains cshake) (codec : LawfulCodec Representation) : Prop :=
  ¬ MerkleCollision domains codec

@[simp] theorem hashLeaf_eq_xof {Representation : Type*} {cshake : Cshake256}
    (domains : MerkleDomains cshake) (codec : LawfulCodec Representation)
    (value : Representation) :
    domains.hashLeaf codec value =
      cshake.xofDigest domains.leafCustomization (leafInput codec value) :=
  rfl

@[simp] theorem hashNode_eq_xof {cshake : Cshake256}
    (domains : MerkleDomains cshake) (left right : Digest) :
    domains.hashNode left right =
      cshake.xofDigest domains.nodeCustomization
        (nodeInput cshake left right) :=
  rfl

/-! ## The framing really is self-delimiting -/

/-- Parse the zero-unary length header, returning the unconsumed suffix. -/
def parseLength : List UInt8 -> Option (Nat × List UInt8)
  | [] => none
  | byte :: rest =>
      if byte = 0 then
        (parseLength rest).map fun parsed => (parsed.1 + 1, parsed.2)
      else if byte = 1 then
        some (0, rest)
      else
        none

@[simp] theorem parseLength_encodeLength_append (length : Nat)
    (suffix : List UInt8) :
    parseLength (encodeLength length ++ suffix) = some (length, suffix) := by
  induction length generalizing suffix with
  | zero => simp [encodeLength, parseLength]
  | succ length ih =>
      rw [show encodeLength (Nat.succ length) = 0 :: encodeLength length by
        simp [encodeLength, List.replicate_succ]]
      simp [parseLength, ih]

/-- Parse one complete envelope and return its payload plus the remaining
bytes.  This parser is proof infrastructure only; it is not a native codec. -/
def parseEnvelope (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  match parseLength bytes with
  | none => none
  | some (length, rest) =>
      if length ≤ rest.length then
        some (rest.take length, rest.drop length)
      else
        none

@[simp] theorem parseEnvelope_envelope_append (payload suffix : List UInt8) :
    parseEnvelope (envelope payload ++ suffix) = some (payload, suffix) := by
  simp [parseEnvelope, envelope, List.append_assoc]

theorem envelope_injective : Function.Injective envelope := by
  intro left right equal
  have parsed := congrArg parseEnvelope equal
  have leftParsed : parseEnvelope (envelope left) = some (left, []) := by
    simpa using parseEnvelope_envelope_append left []
  have rightParsed : parseEnvelope (envelope right) = some (right, []) := by
    simpa using parseEnvelope_envelope_append right []
  rw [leftParsed, rightParsed] at parsed
  exact congrArg Prod.fst (Option.some.inj parsed)

/-- Two concatenated envelopes have a unique ordered pair of payloads. -/
theorem envelopePair_injective :
    Function.Injective
      (fun pair : List UInt8 × List UInt8 =>
        envelope pair.1 ++ envelope pair.2) := by
  intro left right equal
  have parsed := congrArg parseEnvelope equal
  rw [parseEnvelope_envelope_append left.1 (envelope left.2),
    parseEnvelope_envelope_append right.1 (envelope right.2)] at parsed
  have parsedEqual :
      (left.1, envelope left.2) = (right.1, envelope right.2) := by
    exact Option.some.inj parsed
  have components := Prod.mk.inj parsedEqual
  have firstEqual : left.1 = right.1 := components.1
  have secondEnvelopeEqual : envelope left.2 = envelope right.2 := components.2
  exact Prod.ext firstEqual (envelope_injective secondEnvelopeEqual)

/-- Lawfulness alone makes a codec's encoder injective: decode both sides. -/
theorem lawfulCodec_encode_injective {α : Type*} (codec : LawfulCodec α) :
    Function.Injective codec.encode := by
  intro left right equal
  have decoded := congrArg codec.decode equal
  rw [codec.decode_encode, codec.decode_encode] at decoded
  exact Option.some.inj decoded

theorem leafInput_injective {Representation : Type*}
    (codec : LawfulCodec Representation) :
    Function.Injective (leafInput codec) := by
  intro left right equal
  have enveloped : envelope (codec.encode left) = envelope (codec.encode right) :=
    List.cons.inj equal |>.2
  exact lawfulCodec_encode_injective codec (envelope_injective enveloped)

theorem nodeInput_injective (cshake : Cshake256) :
    Function.Injective
      (fun pair : Digest × Digest => nodeInput cshake pair.1 pair.2) := by
  intro left right equal
  have framed :
      envelope (cshake.digestCodec.encode left.1) ++
          envelope (cshake.digestCodec.encode left.2) =
        envelope (cshake.digestCodec.encode right.1) ++
          envelope (cshake.digestCodec.encode right.2) :=
    List.cons.inj equal |>.2
  have encoded :
      (cshake.digestCodec.encode left.1, cshake.digestCodec.encode left.2) =
        (cshake.digestCodec.encode right.1, cshake.digestCodec.encode right.2) :=
    envelopePair_injective framed
  apply Prod.ext
  · exact lawfulCodec_encode_injective cshake.digestCodec
      (congrArg Prod.fst encoded)
  · exact lawfulCodec_encode_injective cshake.digestCodec
      (congrArg Prod.snd encoded)

/-! ## Exact path length and the deterministic collision reduction -/

section Reduction

variable {Representation : Type}
variable {cshake : Cshake256} (domains : MerkleDomains cshake)

/-- Invert one nonempty recomputation step without losing the child digest. -/
theorem recompute_cons_some_iff {k : Nat}
    (leaf sibling : Digest) (address : Fin (k + 1) -> Bool)
    (rest : List Digest) (root : Digest) :
    recompute domains leaf address (sibling :: rest) = some root ↔
      ∃ child,
        recompute domains leaf (fun i => address i.succ) rest = some child ∧
        (match address 0 with
          | false => domains.hashNode child sibling
          | true => domains.hashNode sibling child) = root := by
  cases childResult : recompute domains leaf (fun i => address i.succ) rest with
  | none => simp [recompute, childResult]
  | some child =>
      cases bit : address 0 <;> simp [recompute, childResult, bit]

/-- `recompute = some root` is possible only for a path with exactly one
sibling per address bit.  Under- and over-long byte-decoded proofs are both
rejected by the executable verifier. -/
theorem recompute_some_path_length : ∀ {k : Nat}
    (leaf : Digest) (address : Fin k -> Bool) (proof : List Digest) (root : Digest),
    recompute domains leaf address proof = some root -> proof.length = k := by
  intro k
  induction k with
  | zero =>
      intro leaf address proof root accepted
      cases proof with
      | nil => rfl
      | cons sibling rest => simp [recompute] at accepted
  | succ k ih =>
      intro leaf address proof root accepted
      cases proof with
      | nil => simp [recompute] at accepted
      | cons sibling rest =>
          obtain ⟨child, childResult, _⟩ :=
            (recompute_cons_some_iff domains leaf sibling address rest root).mp accepted
          have restLength : rest.length = k :=
            ih leaf (fun i => address i.succ) rest child childResult
          simp [restLength]

/-- If two recomputations at the same address reach the same root, then their
leaf digests agree or the path supplies an exact framed node collision. -/
theorem recompute_equal_root_implies_leaf_eq_or_node_collision :
    ∀ {k : Nat} (leftLeaf rightLeaf : Digest) (address : Fin k -> Bool)
      (leftProof rightProof : List Digest) (root : Digest),
      recompute domains leftLeaf address leftProof = some root ->
      recompute domains rightLeaf address rightProof = some root ->
      leftLeaf = rightLeaf ∨ NodeCollision domains := by
  intro k
  induction k with
  | zero =>
      intro leftLeaf rightLeaf address leftProof rightProof root leftAccepted rightAccepted
      cases leftProof with
      | cons sibling rest => simp [recompute] at leftAccepted
      | nil =>
          cases rightProof with
          | cons sibling rest => simp [recompute] at rightAccepted
          | nil =>
              left
              simpa [recompute] using leftAccepted.trans rightAccepted.symm
  | succ k ih =>
      intro leftLeaf rightLeaf address leftProof rightProof root leftAccepted rightAccepted
      cases leftProof with
      | nil => simp [recompute] at leftAccepted
      | cons leftSibling leftRest =>
          cases rightProof with
          | nil => simp [recompute] at rightAccepted
          | cons rightSibling rightRest =>
              let tail : Fin k -> Bool := fun i => address i.succ
              obtain ⟨leftChild, leftChildResult, leftRoot⟩ :=
                (recompute_cons_some_iff domains leftLeaf leftSibling address
                  leftRest root).mp leftAccepted
              obtain ⟨rightChild, rightChildResult, rightRoot⟩ :=
                (recompute_cons_some_iff domains rightLeaf rightSibling address
                  rightRest root).mp rightAccepted
              cases bit : address 0 with
                      | false =>
                          simp only [bit] at leftRoot rightRoot
                          by_cases pairsEqual :
                              (leftChild, leftSibling) = (rightChild, rightSibling)
                          · have childrenEqual : leftChild = rightChild :=
                              congrArg Prod.fst pairsEqual
                            subst rightChild
                            exact ih leftLeaf rightLeaf tail leftRest rightRest leftChild
                              leftChildResult rightChildResult
                          · right
                            refine ⟨leftChild, leftSibling, rightChild, rightSibling, ?_⟩
                            refine
                              { inputsDifferent := ?_
                                digestsEqual := ?_ }
                            · intro inputsEqual
                              exact pairsEqual (nodeInput_injective cshake inputsEqual)
                            · simpa using leftRoot.trans rightRoot.symm
                      | true =>
                          simp only [bit] at leftRoot rightRoot
                          by_cases pairsEqual :
                              (leftSibling, leftChild) = (rightSibling, rightChild)
                          · have childrenEqual : leftChild = rightChild :=
                              congrArg Prod.snd pairsEqual
                            subst rightChild
                            exact ih leftLeaf rightLeaf tail leftRest rightRest leftChild
                              leftChildResult rightChildResult
                          · right
                            refine ⟨leftSibling, leftChild, rightSibling, rightChild, ?_⟩
                            refine
                              { inputsDifferent := ?_
                                digestsEqual := ?_ }
                            · intro inputsEqual
                              exact pairsEqual (nodeInput_injective cshake inputsEqual)
                            · simpa using leftRoot.trans rightRoot.symm

variable {Semantic : Type} {k : Nat}

/-- An accepted proof byte string decodes to a digest path of exactly depth
`k`.  This is the codec/path-length seam used by the binding reduction. -/
theorem accepted_proof_decodes_at_exact_depth
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    (root : Digest) (index : Fin (2 ^ k)) (value : Representation)
    (proofBytes : List UInt8)
    (accepted : (merkleCommitmentScheme domains port).verifyOpening
      root index value proofBytes = true) :
    ∃ proof,
      domains.proofCodec.decode proofBytes = some proof ∧
      proof.length = k ∧
      recompute domains (domains.hashLeaf port.representationCodec value)
        (binaryAddressBits k index) proof = some root := by
  simp only [merkleCommitmentScheme] at accepted
  cases decoded : domains.proofCodec.decode proofBytes with
  | none => simp [decoded] at accepted
  | some proof =>
      have recomputed :
          recompute domains (domains.hashLeaf port.representationCodec value)
            (binaryAddressBits k index) proof = some root := by
        simpa [decoded] using accepted
      exact ⟨proof, by simp,
        recompute_some_path_length domains _ _ _ _ recomputed, recomputed⟩

/-- The standard Merkle reduction, stated on the exact executable checker:
two accepted different values at one root and one canonical index expose a
concrete collision in the leaf frame or in one binary-node frame. -/
theorem accepted_different_values_imply_merkle_collision
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    (root : Digest) (index : Fin (2 ^ k))
    (left right : Representation) (leftProof rightProof : List UInt8)
    (leftAccepted : (merkleCommitmentScheme domains port).verifyOpening
      root index left leftProof = true)
    (rightAccepted : (merkleCommitmentScheme domains port).verifyOpening
      root index right rightProof = true)
    (different : left ≠ right) :
    MerkleCollision domains port.representationCodec := by
  obtain ⟨leftPath, _, _, leftRoot⟩ :=
    accepted_proof_decodes_at_exact_depth domains port root index left leftProof leftAccepted
  obtain ⟨rightPath, _, _, rightRoot⟩ :=
    accepted_proof_decodes_at_exact_depth domains port root index right rightProof rightAccepted
  rcases recompute_equal_root_implies_leaf_eq_or_node_collision domains
      (domains.hashLeaf port.representationCodec left)
      (domains.hashLeaf port.representationCodec right)
      (binaryAddressBits k index) leftPath rightPath root leftRoot rightRoot with
    leafHashesEqual | nodeCollision
  · left
    refine ⟨left, right, ?_⟩
    refine
      { inputsDifferent := ?_
        digestsEqual := ?_ }
    · intro inputsEqual
      exact different (leafInput_injective port.representationCodec inputsEqual)
    · simpa using leafHashesEqual
  · exact Or.inr nodeCollision

/-- Collision-freedom discharges the universal position-binding field.  No
claim that cSHAKE satisfies this premise is made here. -/
theorem positionBinding_of_merkleCollisionFree
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    (collisionFree : MerkleCollisionFree domains port.representationCodec) :
    (merkleCommitmentScheme domains port).PositionBinding := by
  intro root index left right leftProof rightProof leftAccepted rightAccepted
  by_cases equal : left = right
  · exact equal
  · exact False.elim <| collisionFree <|
      accepted_different_values_imply_merkle_collision domains port root index
        left right leftProof rightProof leftAccepted rightAccepted equal

/-! ## Explicit adversarial event and price transport -/

/-- One adversarial pair of openings submitted to the exact verifier. -/
structure OpeningPair (Representation Domain : Type) where
  root : Digest
  index : Domain
  left : Representation
  right : Representation
  leftProof : List UInt8
  rightProof : List UInt8

/-- The exact position-binding failure event for one submitted pair. -/
def BindingFailure
    {Semantic Representation Domain : Type}
    {port : ColumnPort Semantic Representation Domain}
    (scheme : CommitmentScheme port) (attempt : OpeningPair Representation Domain) : Prop :=
  scheme.verifyOpening attempt.root attempt.index attempt.left attempt.leftProof = true ∧
  scheme.verifyOpening attempt.root attempt.index attempt.right attempt.rightProof = true ∧
  attempt.left ≠ attempt.right

/-- A deliberately abstract probability/advantage accountant.  Instantiating
`price` with a game probability is a deployment responsibility; only event
monotonicity is needed by the reduction. -/
structure EventPricer (Outcome Price : Type*) [Preorder Price] where
  price : Set Outcome -> Price
  monotone : Monotone price

/-- The collision adversary's exact success event after consuming one failed
binding attempt.  It exposes both decoded depth-`k` paths, their common-root
equations, the different submitted values, and the resulting exact framed
collision.  Unlike bare global collision existence, this event remains tied
to the adversary's outcome and can therefore receive a meaningful price. -/
def ExtractedCollision
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    (attempt : OpeningPair Representation (Fin (2 ^ k))) : Prop :=
  ∃ leftPath rightPath,
    domains.proofCodec.decode attempt.leftProof = some leftPath ∧
    leftPath.length = k ∧
    recompute domains (domains.hashLeaf port.representationCodec attempt.left)
      (binaryAddressBits k attempt.index) leftPath = some attempt.root ∧
    domains.proofCodec.decode attempt.rightProof = some rightPath ∧
    rightPath.length = k ∧
    recompute domains (domains.hashLeaf port.representationCodec attempt.right)
      (binaryAddressBits k attempt.index) rightPath = some attempt.root ∧
    attempt.left ≠ attempt.right ∧
    MerkleCollision domains port.representationCodec

theorem bindingFailure_implies_extractedCollision
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    (attempt : OpeningPair Representation (Fin (2 ^ k)))
    (failure : BindingFailure (merkleCommitmentScheme domains port) attempt) :
    ExtractedCollision domains port attempt := by
  obtain ⟨leftPath, leftDecoded, leftLength, leftRoot⟩ :=
    accepted_proof_decodes_at_exact_depth domains port attempt.root attempt.index
      attempt.left attempt.leftProof failure.1
  obtain ⟨rightPath, rightDecoded, rightLength, rightRoot⟩ :=
    accepted_proof_decodes_at_exact_depth domains port attempt.root attempt.index
      attempt.right attempt.rightProof failure.2.1
  have collision := accepted_different_values_imply_merkle_collision domains port
    attempt.root attempt.index attempt.left attempt.right attempt.leftProof
    attempt.rightProof failure.1 failure.2.1 failure.2.2
  exact ⟨leftPath, rightPath, leftDecoded, leftLength, leftRoot,
    rightDecoded, rightLength, rightRoot, failure.2.2, collision⟩

theorem bindingFailure_event_subset_collisionEvent
    {Outcome : Type*}
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    (attempt : Outcome -> OpeningPair Representation (Fin (2 ^ k))) :
    {outcome | BindingFailure (merkleCommitmentScheme domains port) (attempt outcome)} ⊆
      {outcome | ExtractedCollision domains port (attempt outcome)} := by
  intro outcome failure
  exact bindingFailure_implies_extractedCollision domains port (attempt outcome) failure

/-- The binding-failure price is at most the price assigned to the exact
leaf-or-node framed collision event.  This is the cryptographic residual:
this theorem neither chooses nor bounds that collision price. -/
theorem bindingFailure_price_le_collision
    {Outcome Price : Type*} [Preorder Price]
    (pricer : EventPricer Outcome Price)
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    (attempt : Outcome -> OpeningPair Representation (Fin (2 ^ k))) :
    pricer.price
        {outcome | BindingFailure (merkleCommitmentScheme domains port) (attempt outcome)} ≤
      pricer.price {outcome | ExtractedCollision domains port (attempt outcome)} :=
  pricer.monotone <|
    bindingFailure_event_subset_collisionEvent domains port attempt

end Reduction

/-! ## Adapter for the existing backend security bundle -/

namespace Backend.SecurityPremises

variable {F : Type} [Field F]
variable {PCSAndSampledDecider CshakeRomTransport : Prop}
variable {k : Nat}

/-- Build the existing security-premise bundle from the named Merkle
collision-free reduction plus independently supplied PCS and ROM premises.
Nothing here proves cSHAKE collision resistance or the random-oracle model. -/
def ofMerkleCollisionFree
    (backend : Backend F)
    {role : ColumnRole} {slotId semanticTypeId domainId : Digest}
    {domainCodecPin : CodecPin}
    {domainCodec : LawfulCodec (Fin (2 ^ k))}
    (collisionFree : MerkleCollisionFree backend.merkle backend.tower.valueCodec)
    (pcsAndSampledDecider : PCSAndSampledDecider)
    (cshakeRomTransport : CshakeRomTransport) :
    backend.SecurityPremises PCSAndSampledDecider CshakeRomTransport
      (role := role) (slotId := slotId) (semanticTypeId := semanticTypeId)
      (domainId := domainId) (domainCodecPin := domainCodecPin)
      (domainCodec := domainCodec) where
  merklePositionBinding := by
    exact positionBinding_of_merkleCollisionFree backend.merkle
      (backend.towerPort role slotId semanticTypeId domainId
        domainCodecPin domainCodec) collisionFree
  pcsAndSampledDecider := pcsAndSampledDecider
  cshakeRomTransport := cshakeRomTransport

end Backend.SecurityPremises

/-- info: 'Minidregg.Compiler.Tower256CshakeMerkleBinding.parseEnvelope_envelope_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parseEnvelope_envelope_append
/-- info: 'Minidregg.Compiler.Tower256CshakeMerkleBinding.recompute_some_path_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recompute_some_path_length
/-- info: 'Minidregg.Compiler.Tower256CshakeMerkleBinding.accepted_different_values_imply_merkle_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_different_values_imply_merkle_collision
/-- info: 'Minidregg.Compiler.Tower256CshakeMerkleBinding.positionBinding_of_merkleCollisionFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positionBinding_of_merkleCollisionFree
/-- info: 'Minidregg.Compiler.Tower256CshakeMerkleBinding.bindingFailure_price_le_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bindingFailure_price_le_collision
/-- info: 'Minidregg.Compiler.Tower256CshakeMerkleBinding.Backend.SecurityPremises.ofMerkleCollisionFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Backend.SecurityPremises.ofMerkleCollisionFree

end Minidregg.Compiler.Tower256CshakeMerkleBinding
