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
Selvage's `BindingCommitment`.  `Tower256CshakeMerkleBinding` reduces that
property to concrete framed cSHAKE collisions; the probabilistic collision,
ROM, and proximity reductions remain outside this deterministic verifier.
There is no Rust proposition or Rust field semantics in this module.
-/

import Compiler.AdditiveFriReceiptClause
import Compiler.Tower256ConcreteBackend
import Compiler.Tower256CshakeMerkleBinding
import Selvage.AdditiveBasisBinding

namespace Minidregg.Compiler.Tower256AdditiveFriController

open Polynomial
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Selvage
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
    (pcs.positionBinding n)).toSelvage

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

/-! ### ⚑ The ordered-basis binding

`Selvage/AdditiveBaseFold.lean`'s `keystone_basis_ambiguity` is a proved negative:
one codeword on one domain is an honest LCH commitment to two DIFFERENT Boolean
tables under two ORDERINGS of the same `GF(2)`-basis. Same span, same evaluation
points, same Merkle leaves — so a transcript that binds the domain does not
determine the committed multilinear.

`TranscriptPins.statementBytes` above carries a docstring saying the statement
encoding "must" be included. That is a comment: no field and no theorem related
it to `clause.basis`, and the repository's only inhabitant
(`Tower256AdditiveFriRawDeployment.bootstrapPins`) sets it to nine constant ASCII
bytes. The binding is therefore made STRUCTURAL here instead — `basisPrefix` is
spliced into every sponge input by construction, so there is nothing for a
caller to forget.

⚑ **The encoding IS the binding, so it is named once and only once.** Every
element is framed POSITIONALLY: `basisFrame` carries the INDEX beside the value,
and the frames are laid down in index order inside their own envelopes. An
encoding that agreed on the span and differed on the order — a sorted list, an
XOR fold, a set of hashes — would reintroduce the same hole one level down, and
`basisPrefix_inj` is what forbids that: it recovers `basis index` at each index
separately. -/

/-- The canonical value codec for every field element in the transcript: the
same Lean-selected recursive Fan--Paar codec `queryPrefix` already uses for
challenges. Named once so the basis and the challenges cannot drift apart. -/
abbrev transcriptValueCodec : LawfulCodec Tower256 :=
  BinaryTower256Profile.profile.valueCodec

/-- One POSITIONAL frame `(index, value)`. Carrying the index inside the frame is
what makes the encoding order-sensitive rather than span-sensitive. -/
def basisFrame (index : Nat) (value : Tower256) : List UInt8 :=
  envelope (encodeLength index) ++ envelope (transcriptValueCodec.encode value)

/-- ⭐ **THE CANONICAL ORDERED-BASIS ENCODING.** Domain log, round count, affine
offset, then the `ell` basis elements as indexed frames in index order. This is
the object the sponge absorbs; `basisPrefix_inj` proves it determines every one
of those five things. -/
def basisPrefix (ell m : Nat) (basis : Nat → Tower256) (offset : Tower256) :
    List UInt8 :=
  envelope (encodeLength ell) ++
    envelope (encodeLength m) ++
      envelope (transcriptValueCodec.encode offset) ++
        (List.ofFn fun index : Fin ell =>
          envelope (basisFrame index (basis index))).flatten

/-- The single frame spliced into every sponge input, taken from the clause's
own first-order `basis`/`offset` fields (which `Clause.basisExact` and
`Clause.offsetExact` pin to `tower.beta` and `tower.offset`). -/
def basisBinding (clause : FriClause pcs m manifest) : List UInt8 :=
  envelope (basisPrefix ell m clause.basis clause.offset)

/-! #### The encoding is injective, positionally -/

theorem envelope_append_inj {left right leftRest rightRest : List UInt8}
    (equal : envelope left ++ leftRest = envelope right ++ rightRest) :
    left = right ∧ leftRest = rightRest := by
  have parsed := congrArg Tower256CshakeMerkleBinding.parseEnvelope equal
  rw [Tower256CshakeMerkleBinding.parseEnvelope_envelope_append,
    Tower256CshakeMerkleBinding.parseEnvelope_envelope_append] at parsed
  have paired := Option.some.inj parsed
  exact ⟨congrArg Prod.fst paired, congrArg Prod.snd paired⟩

theorem encodeLength_injective : Function.Injective encodeLength := by
  intro left right equal
  have lengths := congrArg List.length equal
  simpa [encodeLength] using lengths

theorem basisFrame_inj {leftIndex rightIndex : Nat}
    {leftValue rightValue : Tower256}
    (equal : basisFrame leftIndex leftValue = basisFrame rightIndex rightValue) :
    leftIndex = rightIndex ∧ leftValue = rightValue := by
  rw [basisFrame, basisFrame] at equal
  obtain ⟨indexEqual, valueEqual⟩ := envelope_append_inj equal
  exact ⟨encodeLength_injective indexEqual,
    Tower256CshakeMerkleBinding.lawfulCodec_encode_injective _
      (Tower256CshakeMerkleBinding.envelope_injective valueEqual)⟩

/-- A run of enveloped frames is recovered frame by frame, in order — the lemma
that makes the encoding positional rather than set-like. -/
theorem flattenFrames_append_inj : ∀ {count : Nat}
    {left right : Fin count → List UInt8} {leftRest rightRest : List UInt8},
    (List.ofFn fun index => envelope (left index)).flatten ++ leftRest
        = (List.ofFn fun index => envelope (right index)).flatten ++ rightRest →
      left = right ∧ leftRest = rightRest := by
  intro count
  induction count with
  | zero =>
      intro left right leftRest rightRest equal
      exact ⟨funext fun index => index.elim0, by simpa using equal⟩
  | succ count ih =>
      intro left right leftRest rightRest equal
      rw [List.ofFn_succ, List.ofFn_succ] at equal
      simp only [List.flatten_cons, List.append_assoc] at equal
      obtain ⟨headEqual, tailEqual⟩ := envelope_append_inj equal
      obtain ⟨tailFun, restEqual⟩ := ih tailEqual
      refine ⟨funext fun index => ?_, restEqual⟩
      refine Fin.cases ?_ ?_ index
      · exact headEqual
      · intro j; exact congrFun tailFun j

/-- ⭐ **THE ENCODING DETERMINES THE ORDERED BASIS.** Domain log, round count,
offset and every live basis element are recovered from the bytes — each index
separately, which is exactly what `keystone_basis_ambiguity` needs and what an
`additiveDomain` label cannot give (`Selvage.no_span_indexed_decoder`). -/
theorem basisPrefix_append_inj {leftEll leftM rightEll rightM : Nat}
    {leftBasis rightBasis : Nat → Tower256}
    {leftOffset rightOffset : Tower256} {leftRest rightRest : List UInt8}
    (equal : basisPrefix leftEll leftM leftBasis leftOffset ++ leftRest
        = basisPrefix rightEll rightM rightBasis rightOffset ++ rightRest) :
    leftEll = rightEll ∧ leftM = rightM ∧ leftOffset = rightOffset ∧
      (∀ index, index < leftEll → leftBasis index = rightBasis index) ∧
        leftRest = rightRest := by
  rw [basisPrefix, basisPrefix] at equal
  simp only [List.append_assoc] at equal
  obtain ⟨ellBytes, afterEll⟩ := envelope_append_inj equal
  have ellEqual : leftEll = rightEll := encodeLength_injective ellBytes
  subst ellEqual
  obtain ⟨roundBytes, afterRounds⟩ := envelope_append_inj afterEll
  obtain ⟨offsetBytes, afterOffset⟩ := envelope_append_inj afterRounds
  obtain ⟨frames, restEqual⟩ := flattenFrames_append_inj afterOffset
  refine ⟨rfl, encodeLength_injective roundBytes,
    Tower256CshakeMerkleBinding.lawfulCodec_encode_injective _ offsetBytes,
    fun index bounded => ?_, restEqual⟩
  exact (basisFrame_inj (congrFun frames ⟨index, bounded⟩)).2

theorem basisPrefix_inj {leftEll leftM rightEll rightM : Nat}
    {leftBasis rightBasis : Nat → Tower256}
    {leftOffset rightOffset : Tower256}
    (equal : basisPrefix leftEll leftM leftBasis leftOffset
        = basisPrefix rightEll rightM rightBasis rightOffset) :
    leftEll = rightEll ∧ leftM = rightM ∧ leftOffset = rightOffset ∧
      ∀ index, index < leftEll → leftBasis index = rightBasis index := by
  obtain ⟨ellEqual, roundEqual, offsetEqual, basisEqual, -⟩ :=
    basisPrefix_append_inj (leftRest := ([] : List UInt8))
      (rightRest := ([] : List UInt8)) (by simpa using equal)
  exact ⟨ellEqual, roundEqual, offsetEqual, basisEqual⟩

/-- ⭐ **TOOTH (byte layer): a reordering CHANGES the sponge input.** The
contrapositive of `basisPrefix_inj` — if two bases disagree at any live index
their transcripts disagree, so the reordered sibling cannot inherit the honest
commitment's challenges. -/
theorem basisPrefix_ne_of_basis_ne {ell m : Nat}
    {basis other : Nat → Tower256} {offset : Tower256}
    (index : Nat) (bounded : index < ell)
    (different : basis index ≠ other index) :
    basisPrefix ell m basis offset ≠ basisPrefix ell m other offset := fun equal =>
  different ((basisPrefix_inj equal).2.2.2 index bounded)

/-- The exact prefix supplied to challenge `j`: the public statement, ⚑ the
ORDERED basis binding, then roots `0 .. j`, each computed from a word which
depends only on challenges strictly before that level. -/
def challengeInput (clause : FriClause pcs m manifest) (pins : TranscriptPins)
    (receipt : Receipt ell m queryCount) (j : Fin m) : List UInt8 :=
  envelope pins.statementBytes ++
    basisBinding pcs clause ++
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

/-- The post-challenge transcript bound before query sampling: statement, ⚑ the
ORDERED basis binding, all level roots through `m`, and the canonical Tower256
challenge encodings. -/
def queryPrefix (clause : FriClause pcs m manifest) (pins : TranscriptPins)
    (receipt : Receipt ell m queryCount) : List UInt8 :=
  envelope pins.statementBytes ++
    basisBinding pcs clause ++
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

/-! ### ⚑ The ambiguity is CLOSED, not merely addressed -/

/-- ⭐ **THE TRANSCRIPT NOW DETERMINES THE ORDERED BASIS.** Two clauses whose
challenge inputs agree have the same affine offset and the same basis element at
every live index — including at the indices a reordering would permute. Before
the splice this statement was FALSE by `keystone_basis_ambiguity`: the sponge
input mentioned `basis` nowhere. -/
theorem challengeInput_determines_basis
    (clause other : FriClause pcs m manifest)
    (pins otherPins : TranscriptPins)
    (receipt otherReceipt : Receipt ell m queryCount) (j otherJ : Fin m)
    (sameInput : challengeInput pcs clause pins receipt j
      = challengeInput pcs other otherPins otherReceipt otherJ) :
    clause.tower.offset = other.tower.offset ∧
      ∀ index, index < ell → clause.tower.beta index = other.tower.beta index := by
  rw [challengeInput, challengeInput, basisBinding, basisBinding] at sameInput
  simp only [List.append_assoc] at sameInput
  obtain ⟨-, afterStatement⟩ := envelope_append_inj sameInput
  obtain ⟨prefixEqual, -⟩ := envelope_append_inj afterStatement
  obtain ⟨-, -, offsetEqual, basisEqual⟩ := basisPrefix_inj prefixEqual
  rw [clause.offsetExact, other.offsetExact, clause.basisExact,
    other.basisExact] at *
  exact ⟨offsetEqual, basisEqual⟩

/-- ⭐⭐ **THE CLOSURE THEOREM.** Two Boolean tables that are LCH-committed to the
SAME codeword under two clauses sharing a challenge input are EQUAL.

This is the statement `keystone_basis_ambiguity` refutes for the unrepaired
transcript, and it is the honest form of "the hazard is closed": the
counterexample is a pair of tables, one codeword, one domain — and the only way
it survives the splice is if the two orderings produce the same sponge input,
which `basisPrefix_inj` forbids. The algebra is
`Selvage.table_unique_of_basis_agree`; the bytes are `basisPrefix_inj`; this
theorem is the weld. -/
theorem transcript_determines_table
    (clause other : FriClause pcs m manifest)
    (pins otherPins : TranscriptPins)
    (receipt otherReceipt : Receipt ell m queryCount) (j otherJ : Fin m)
    (sameInput : challengeInput pcs clause pins receipt j
      = challengeInput pcs other otherPins otherReceipt otherJ)
    (arity : Nat) (arityLe : arity ≤ ell) (word : Polynomial Tower256)
    (table otherTable : (Fin arity → Bool) → Tower256)
    (committed : novelPack clause.tower.beta arity
      (booleanMobiusPolynomial arity table) = word)
    (otherCommitted : novelPack other.tower.beta arity
      (booleanMobiusPolynomial arity otherTable) = word) :
    table = otherTable :=
  table_unique_of_basis_agree clause.tower.beta other.tower.beta arity
    (fun index bounded =>
      (challengeInput_determines_basis pcs clause other pins otherPins receipt
        otherReceipt j otherJ sameInput).2 index (lt_of_lt_of_le bounded arityLe))
    table otherTable (by rw [committed, otherCommitted])

/-- ⭐ **THE FIX IS CONSUMED, NOT AN ISLAND.** The ordered basis the transcript
now binds is exactly the setup parameter of `Selvage.lchRingSwitchTarget` — the
`RingSwitchTarget` whose `Extractable` field `keystone_basis_ambiguity` was
making FALSE (`Selvage/RingSwitching.lean` §7 item 4, the BLOCKING prerequisite).
A clause therefore names one large-field scheme, and
`challengeInput_determines_basis` says two clauses sharing a transcript name
schemes agreeing at every live index. -/
noncomputable def clauseRingSwitchTarget (clause : FriClause pcs m manifest) :
    RingSwitchTarget Tower256 :=
  lchRingSwitchTarget clause.tower.beta

/-- The clause's large-field scheme really is extractable — the downstream
obligation discharged at the deployed object rather than at a toy. -/
theorem clauseRingSwitchTarget_extractable (clause : FriClause pcs m manifest) :
    (clauseRingSwitchTarget pcs clause).pcs.Extractable :=
  lchBasisBoundPcs_extractable clause.tower.beta

/-- And its commitment is the literal LCH packing under the bound basis, so the
handle the transcript pins and the handle the extractor reads are the same
object. -/
theorem clauseRingSwitchTarget_commit (clause : FriClause pcs m manifest)
    {arity : Nat} (table : (Fin arity → Bool) → Tower256) :
    (clauseRingSwitchTarget pcs clause).pcs.commit table
      = ⟨arity, clause.tower.beta,
          novelPack clause.tower.beta arity
            (booleanMobiusPolynomial arity table)⟩ :=
  rfl

/-! ### Teeth on the repaired transcript

The accept half is already in the tree and stays there:
`Tower256AdditiveFriRawDeployment.bootstrapReceipt_accepts` and
`honest_run_succeeds` are honest runs through this transcript, and they build
against the spliced definitions — a splice that refused honest work would take
them red. The refuse half is below, and the mutation is asserted to be real
before the verdict is read. -/

/-- Two orderings of one two-element basis. `toothBasis` is `(0, 1)`,
`toothBasisSwap` is `(1, 0)` — the Tower256 shadow of the keystone's `(1, x₁)`
versus `(x₁, 1)`. -/
def toothBasis : Nat → Tower256
  | 0 => 0
  | _ => 1

def toothBasisSwap : Nat → Tower256
  | 0 => 1
  | _ => 0

/-- **The mutation is real** — assert it before reading the verdict. The two
orderings are different functions at index `0`, and they are a permutation of
each other, so nothing that reads the basis as a SET can separate them. -/
theorem tooth_reordering_is_a_real_mutation :
    toothBasis 0 ≠ toothBasisSwap 0 ∧ toothBasis 0 = toothBasisSwap 1 ∧
      toothBasis 1 = toothBasisSwap 0 := by
  refine ⟨?_, rfl, rfl⟩
  show (0 : Tower256) ≠ 1
  exact zero_ne_one

/-- ⭐ **TOOTH: the repaired transcript REFUSES the reordered sibling.** Its
sponge input is a different byte string, so it draws different challenges and
different query seeds; it cannot be passed off as the honest commitment's
transcript. -/
theorem tooth_reordered_transcript_differs (m : Nat) :
    basisPrefix 2 m toothBasis 0 ≠ basisPrefix 2 m toothBasisSwap 0 :=
  basisPrefix_ne_of_basis_ne 0 (by omega) tooth_reordering_is_a_real_mutation.1

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
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.basisPrefix_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basisPrefix_inj
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.basisPrefix_ne_of_basis_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basisPrefix_ne_of_basis_ne
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.challengeInput_determines_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms challengeInput_determines_basis
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.transcript_determines_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transcript_determines_table
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.clauseRingSwitchTarget_extractable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms clauseRingSwitchTarget_extractable
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.clauseRingSwitchTarget_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms clauseRingSwitchTarget_commit
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.tooth_reordering_is_a_real_mutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_reordering_is_a_real_mutation
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.tooth_reordered_transcript_differs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_reordered_transcript_differs
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.accepts_additiveFriAdaptiveCoherentAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepts_additiveFriAdaptiveCoherentAccepts
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriController.run_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_success_integrity

end

end Minidregg.Compiler.Tower256AdditiveFriController
