/-
# Compiler.Tower256CshakeMerkleController -- one shared binary backend seam

This module closes the largest purely structural gap between the authenticated
column controller and a first Tower256/additive deployment:

* one Lean-selected cSHAKE256 function and its exact domain-separated framing
  are shared by the transcript and Merkle commitments;
* a perfect binary Merkle tree is defined over the canonical LSB-first Boolean
  cube, with an actual logarithmic authentication path and a proved honest
  opening equation;
* that tree is exported as the *same* `CommitmentScheme` consumed by
  `AuthenticatedColumnPlan` and, through its existing adapter, by Loom;
* a native cSHAKE call can return only bytes for the result already selected by
  Lean.  Native failure blocks, and a different digest cannot be accepted.

The cSHAKE function is a Lean field of the selected backend, not a claim about
`prover/src/hash_kernels.rs`.  The four-limb Rust Tower256 representation also
has no semantics here.  Position binding/Merkle collision resistance and the
Fiat--Shamir ROM transport remain explicit deployment premises; this file
proves functional tree/opening correctness, not those security games.
-/

import Compiler.AuthenticatedColumnPlan
import Loom.BinaryLookup

namespace Minidregg.Compiler.Tower256CshakeMerkleController

open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.NativeKernelPlan (WorkKind)
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Canonical framing and one Lean-selected cSHAKE256 primitive -/

/-- A self-delimiting unary length.  It is intentionally simple: the protocol
object needs an unambiguous Lean definition; a generated deployment codec may
replace its cost model without changing the ownership boundary. -/
def encodeLength (n : Nat) : List UInt8 :=
  List.replicate n 0 ++ [1]

/-- Length-delimit a byte string before concatenating it with another frame. -/
def envelope (bytes : List UInt8) : List UInt8 :=
  encodeLength bytes.length ++ bytes

/-- The selected cSHAKE256 data operation.  `xofDigest` is the Lean-owned
function used by every checker below.  `algorithmId` and `outputBytesExact`
pin the intended deployment profile but do not prove that native code realizes
the function or the random-oracle model. -/
structure Cshake256 where
  algorithmId : Digest
  digestCodecPin : CodecPin
  digestCodec : LawfulCodec Digest
  outputBytes : Nat
  outputBytesExact : outputBytes = 32
  xofDigest : (customization input : List UInt8) -> Digest

/-- Exact leaf/node domains for one Merkle suite.  Both use the same cSHAKE
function by construction. -/
structure MerkleDomains (cshake : Cshake256) where
  suiteId : Digest
  proofCodecPin : CodecPin
  proofCodec : LawfulCodec (List Digest)
  leafCustomization : List UInt8
  nodeCustomization : List UInt8
  customizationsDistinct : leafCustomization ≠ nodeCustomization

def MerkleDomains.hashLeaf
    {cshake : Cshake256} (domains : MerkleDomains cshake)
    {Representation : Type*} (codec : LawfulCodec Representation)
    (value : Representation) : Digest :=
  cshake.xofDigest domains.leafCustomization
    (0 :: envelope (codec.encode value))

def MerkleDomains.hashNode
    {cshake : Cshake256} (domains : MerkleDomains cshake)
    (left right : Digest) : Digest :=
  cshake.xofDigest domains.nodeCustomization
    (1 :: envelope (cshake.digestCodec.encode left) ++
      envelope (cshake.digestCodec.encode right))

/-! ## Perfect Merkle trees on the canonical additive Boolean cube -/

section Merkle

variable {Representation : Type*}
variable {cshake : Cshake256} (domains : MerkleDomains cshake)
variable (codec : LawfulCodec Representation)

/-- Root of a perfect tree whose coordinates are Boolean words.  The first
LSB-first address bit is the outer split; recursion fixes the remaining bits. -/
def cubeRoot : {k : Nat} -> ((Fin k -> Bool) -> Representation) -> Digest
  | 0, column => domains.hashLeaf codec (column fun i => i.elim0)
  | k + 1, column =>
      domains.hashNode
        (cubeRoot (fun tail => column (Fin.cases false tail)))
        (cubeRoot (fun tail => column (Fin.cases true tail)))

/-- Top-down sibling roots for one Boolean-cube coordinate. -/
def cubePath : {k : Nat} ->
    ((Fin k -> Bool) -> Representation) -> (Fin k -> Bool) -> List Digest
  | 0, _, _ => []
  | k + 1, column, address =>
      let tail : Fin k -> Bool := fun i => address i.succ
      match address 0 with
      | false =>
          cubeRoot domains codec (fun rest => column (Fin.cases true rest)) ::
            cubePath (fun rest => column (Fin.cases false rest)) tail
      | true =>
          cubeRoot domains codec (fun rest => column (Fin.cases false rest)) ::
            cubePath (fun rest => column (Fin.cases true rest)) tail

/-- Recompute a root from a leaf, its canonical address, and a top-down
authentication path.  Exact path length is enforced by returning `none` for
every under- or over-long list. -/
def recompute : {k : Nat} ->
    Digest -> (Fin k -> Bool) -> List Digest -> Option Digest
  | 0, leaf, _, proof => if proof = [] then some leaf else none
  | k + 1, leaf, address, proof =>
      match proof with
      | [] => none
      | sibling :: rest =>
          let tail : Fin k -> Bool := fun i => address i.succ
          match recompute leaf tail rest with
          | none => none
          | some child =>
              some (match address 0 with
                | false => domains.hashNode child sibling
                | true => domains.hashNode sibling child)

/-- Functional Merkle correctness: the logarithmic honest path reconstructs
the exact perfect-tree root.  No collision-resistance premise is used. -/
theorem recompute_cubePath : forall {k : Nat}
    (column : (Fin k -> Bool) -> Representation)
    (address : Fin k -> Bool),
    recompute domains
        (domains.hashLeaf codec (column address)) address
        (cubePath domains codec column address) =
      some (cubeRoot domains codec column) := by
  intro k
  induction k with
  | zero =>
      intro column address
      have haddress : address = (fun i => i.elim0) := Subsingleton.elim _ _
      subst address
      simp [cubePath, recompute, cubeRoot]
  | succ k ih =>
      intro column address
      cases hbit : address 0 with
      | false =>
          have haddress :
              (Fin.cases false (fun i => address i.succ)) = address := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using hbit.symm
            · simp
          have hrecursive := ih
            (fun rest => column (Fin.cases false rest))
            (fun i => address i.succ)
          simp only [cubePath, hbit, recompute]
          rw [show column address =
              column (Fin.cases false (fun i => address i.succ)) by
                rw [haddress]]
          rw [hrecursive]
          rfl
      | true =>
          have haddress :
              (Fin.cases true (fun i => address i.succ)) = address := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using hbit.symm
            · simp
          have hrecursive := ih
            (fun rest => column (Fin.cases true rest))
            (fun i => address i.succ)
          simp only [cubePath, hbit, recompute]
          rw [show column address =
              column (Fin.cases true (fun i => address i.succ)) by
                rw [haddress]]
          rw [hrecursive]
          rfl

end Merkle

/-! ## The exact authenticated-column commitment instance -/

variable {Semantic Representation : Type} {k : Nat}

/-- The real logarithmic Merkle scheme on `Fin (2^k)`.  Index conversion is
the same `binaryAddressBits`/`binaryCubeIndexEquiv` pair used by LogUp's
canonical-address theorem, eliminating a second address convention. -/
def merkleCommitmentScheme
    {cshake : Cshake256} (domains : MerkleDomains cshake)
    (port : ColumnPort Semantic Representation (Fin (2 ^ k))) :
    CommitmentScheme port where
  suiteId := domains.suiteId
  proofCodecPin := domains.proofCodecPin
  commit column :=
    cubeRoot domains port.representationCodec
      (fun address => column (binaryCubeIndexEquiv k address))
  openAt column index :=
    domains.proofCodec.encode
      (cubePath domains port.representationCodec
        (fun address => column (binaryCubeIndexEquiv k address))
        (binaryAddressBits k index))
  verifyOpening root index value proofBytes :=
    match domains.proofCodec.decode proofBytes with
    | none => false
    | some proof =>
        decide (recompute domains
          (domains.hashLeaf port.representationCodec value)
          (binaryAddressBits k index) proof = some root)
  verifyOpening_commit := by
    intro column index
    simp only [LawfulCodec.decode_encode, decide_eq_true_eq]
    rw [show column index =
        column (binaryCubeIndexEquiv k (binaryAddressBits k index)) by
          rw [binaryCubeIndexEquiv_decode]]
    exact recompute_cubePath domains port.representationCodec
      (fun address => column (binaryCubeIndexEquiv k address))
      (binaryAddressBits k index)

/-- Binding is deliberately supplied as a real premise.  Functional Merkle
correctness above does not manufacture collision resistance. -/
def bindingMerkleCommitmentScheme
    {cshake : Cshake256} (domains : MerkleDomains cshake)
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    (binding : (merkleCommitmentScheme domains port).PositionBinding) :
    BindingCommitmentScheme port where
  toCommitmentScheme := merkleCommitmentScheme domains port
  binding := binding

/-- The controller and Loom consume literally the same Merkle root function. -/
theorem bindingMerkle_toLoom_commit_exact
    {cshake : Cshake256} (domains : MerkleDomains cshake)
    (port : ColumnPort Semantic Representation (Fin (2 ^ k)))
    (binding : (merkleCommitmentScheme domains port).PositionBinding)
    (column : Fin (2 ^ k) -> Representation) :
    (bindingMerkleCommitmentScheme domains port binding).toLoom.commit column =
      (merkleCommitmentScheme domains port).commit column :=
  rfl

/-! ## One cSHAKE-framed global transcript -/

/-- Codecs and domain strings for the one global controller transcript.  The
same `cshake` object is shared with `MerkleDomains` by the enclosing backend. -/
structure TranscriptDomains (cshake : Cshake256) where
  frameCodec : LawfulCodec GlobalFrame
  labelCodec : LawfulCodec GlobalDrawLabel
  absorbDomain : List UInt8
  squeezeDomain : List UInt8
  drawFrameTag : UInt8
  absorb_squeeze_distinct : absorbDomain ≠ squeezeDomain

def TranscriptDomains.absorbFrame
    {cshake : Cshake256} (domains : TranscriptDomains cshake)
    (state : List UInt8) (frame : GlobalFrame) : List UInt8 :=
  state ++ envelope (domains.frameCodec.encode frame)

def TranscriptDomains.drawInput
    {cshake : Cshake256} (domains : TranscriptDomains cshake)
    (state : List UInt8) (label : GlobalDrawLabel) : List UInt8 :=
  envelope state ++ envelope (domains.labelCodec.encode label)

def TranscriptDomains.coin
    {cshake : Cshake256} (domains : TranscriptDomains cshake)
    (state : List UInt8) (label : GlobalDrawLabel) : Digest :=
  cshake.xofDigest domains.squeezeDomain (domains.drawInput state label)

def TranscriptDomains.afterDraw
    {cshake : Cshake256} (domains : TranscriptDomains cshake)
    (state : List UInt8) (label : GlobalDrawLabel) (coin : Digest) : List UInt8 :=
  state ++ envelope
    (domains.drawFrameTag :: envelope (domains.labelCodec.encode label) ++
      envelope (cshake.digestCodec.encode coin))

/-- A concrete cSHAKE-shaped portal with exact framing.  It is a transcript
controller, not a ROM theorem. -/
def TranscriptDomains.portal
    {cshake : Cshake256} (domains : TranscriptDomains cshake) :
    GlobalTranscriptPortal (List UInt8) where
  absorb := domains.absorbFrame
  squeeze state label :=
    let coin := domains.coin state label
    (coin, domains.afterDraw state label coin)
  xof := domains.coin
  squeeze_xof_law := by intro state label; rfl

/-! ## Tower256 pin and the shared backend -/

/-- Concrete first-order Tower256 profile obligations.  The codec is selected
by Lean and every encoded field value is exactly 32 bytes.  This still does
not identify an abstract Lean field element with Rust's four `u64` limbs. -/
structure Tower256Profile (F : Type) [Field F] where
  carrier : CarrierProfile
  profileId : Digest
  towerId : Digest
  basisId : Digest
  representationId : Digest
  carrierExact : carrier =
    .gf2Tower profileId towerId basisId representationId 256
  characteristic : CharP F 2
  cardinality : Nat.card F = 2 ^ 256
  valueCodecPin : CodecPin
  valueCodec : LawfulCodec F
  valueWidthExact : forall value, (valueCodec.encode value).length = 32

/-- One backend shares a literal cSHAKE object between its Merkle tree and
global transcript.  There is no opportunity to splice another hash function
while retaining this type. -/
structure Backend (F : Type) [Field F] where
  tower : Tower256Profile F
  cshake : Cshake256
  merkle : MerkleDomains cshake
  transcript : TranscriptDomains cshake

namespace Backend

variable {F : Type} [Field F]

/-- Build an identity-representation Tower256 column port.  Semantic and
representation codecs are the same selected 32-byte codec. -/
def towerPort (backend : Backend F) (role : ColumnRole)
    (slotId semanticTypeId domainId : Digest)
    (domainCodecPin : CodecPin) {Domain : Type}
    (domainCodec : LawfulCodec Domain) : ColumnPort F F Domain where
  slotId := slotId
  role := role
  semanticTypeId := semanticTypeId
  representationId := backend.tower.representationId
  carrier := backend.tower.carrier
  semanticCodecPin := backend.tower.valueCodecPin
  representationCodecPin := backend.tower.valueCodecPin
  domainId := domainId
  domainCodecPin := domainCodecPin
  semanticCodec := backend.tower.valueCodec
  representationCodec := backend.tower.valueCodec
  domainCodec := domainCodec
  represent := id

/-- The backend's exact perfect-tree commitment for a power-of-two additive
column domain. -/
def additiveMerkleScheme (backend : Backend F) (role : ColumnRole)
    (slotId semanticTypeId domainId : Digest)
    (domainCodecPin : CodecPin) (domainCodec : LawfulCodec (Fin (2 ^ k))) :
    CommitmentScheme
      (backend.towerPort role slotId semanticTypeId domainId
        domainCodecPin domainCodec) :=
  merkleCommitmentScheme backend.merkle
    (backend.towerPort role slotId semanticTypeId domainId
      domainCodecPin domainCodec)

/-- Explicit remaining security boundary for a deployed backend.  These are
not `True` placeholders: callers must supply the actual position-binding game,
the cSHAKE-to-ROM transport, and the PCS/sampled-decider theorem used by their
accepted clause. -/
structure SecurityPremises (backend : Backend F)
    (PCSAndSampledDecider CshakeRomTransport : Prop)
    {role : ColumnRole} {slotId semanticTypeId domainId : Digest}
    {domainCodecPin : CodecPin}
    {domainCodec : LawfulCodec (Fin (2 ^ k))} : Prop where
  merklePositionBinding :
    (backend.additiveMerkleScheme role slotId semanticTypeId domainId
      domainCodecPin domainCodec).PositionBinding
  pcsAndSampledDecider : PCSAndSampledDecider
  cshakeRomTransport : CshakeRomTransport

end Backend

/-! ## Opaque native cSHAKE data call -/

structure XofRequest where
  customization : List UInt8
  input : List UInt8
deriving DecidableEq, Repr

/-- Native code is asked only for the byte encoding of the digest already
selected by Lean's cSHAKE function. -/
def checkedXofCall (cshake : Cshake256)
    (requestCodecPin : CodecPin) (requestCodec : LawfulCodec XofRequest)
    (callSlotId carrierProfileId : Digest) (request : XofRequest) : NativeCall where
  Input := XofRequest
  Output := Digest
  outputDecidableEq := inferInstance
  callSlotId := callSlotId
  kind := .hash
  carrierProfileId := carrierProfileId
  inputCodecPin := requestCodecPin
  outputCodecPin := cshake.digestCodecPin
  inputCodec := requestCodec
  outputCodec := cshake.digestCodec
  input := request
  claimedOutput := cshake.xofDigest request.customization request.input
  leanCheck := fun candidateRequest candidateDigest =>
    decide (candidateDigest =
      cshake.xofDigest candidateRequest.customization candidateRequest.input)

/-- Any accepted native reply is the canonical encoding of Lean's selected
digest.  This theorem quantifies over arbitrary reply bytes and assumes no Rust
honesty, determinism, representation, or refinement relation. -/
theorem checkedXofCall_reply_exact (cshake : Cshake256)
    (requestCodecPin : CodecPin) (requestCodec : LawfulCodec XofRequest)
    (callSlotId carrierProfileId : Digest) (request : XofRequest)
    (bytes : List UInt8)
    (accepted : (checkedXofCall cshake requestCodecPin requestCodec
      callSlotId carrierProfileId request).acceptsReply bytes = true) :
    bytes = cshake.digestCodec.encode
      (cshake.xofDigest request.customization request.input) := by
  simp only [checkedXofCall, NativeCall.acceptsReply, Bool.and_eq_true,
    decide_eq_true_eq] at accepted
  exact accepted.1.1

/-- info: 'Minidregg.Compiler.Tower256CshakeMerkleController.recompute_cubePath' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recompute_cubePath
/-- info: 'Minidregg.Compiler.Tower256CshakeMerkleController.bindingMerkle_toLoom_commit_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bindingMerkle_toLoom_commit_exact
/-- info: 'Minidregg.Compiler.Tower256CshakeMerkleController.checkedXofCall_reply_exact' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms checkedXofCall_reply_exact

end Minidregg.Compiler.Tower256CshakeMerkleController
