/-
# Assurance.DeployedReceiptOpening -- Byte-level `op 151` world-root opening & `ReceiptContinuity` bridge

This module connects the wire-level `StreamCodec` encoding (`encodeNat`, `systemLeaf`,
`AuthTrie.climb`, and `ReceiptContinuity` opening/extension records) used by `op 151`
(`worldReceiptProof` / `RECEIPT_CONTINUITY`) and `native/resource-client/src/receipt_continuity.rs`
to `Kernel.ReceiptContinuity.opens_sound` and `Kernel.ReceiptContinuity.accepted_binds_chain`.

1. **Byte-level framing & `StreamCodec` identities**:
   - `StreamCodec.encodeNat` (base-255 little-endian digits terminated by `0xff` = `255`)
     underpins `DurableCheckpointCodec.systemLeaf`, `WorldRoot.nodeBytes`, and
     `WorldRoot.chainDigest`.
   - `WorldRoot.deployedIx .system` is the 256-bit path derived from
     `cSHAKE256(WorldRoot.worldCustomization, [3, 0])`.
   - `ReceiptContinuity.opens` holds iff `siblings.length ≤ 256` and `AuthTrie.climb` along
     `deployedIx .system` reconstructs the checkpoint's `worldRoot`.

2. **Roundtrip & canonicality of the opening witness codecs**:
   - `StreamCodec.nat`, `pointStream`, `rootWitnessStream`, `openingRecordStream`, and
     `continuityEnvelopeStream` are proven roundtrip and canonical via `StreamCodec.toLawful`:
     any wire byte slice accepted by `decode` re-encodes to the exact input byte slice,
     rejecting non-canonical natural encodings (such as `[0, 255]`) and trailing bytes.

3. **Wire-to-soundness bridge (`ValidOpening ∨ ConcreteCollision`)**:
   - Any wire byte slice whose decoded opening passes the deterministic `checkOpeningRecord`
     (or `ReceiptContinuity.verify`) establishes `ValidOpening ∨ ConcreteCollision` against
     the checkpoint's `worldRoot` (`wireOpening_sound`, `wireContinuity_verify_sound`).

4. **Computable positive & negative audit (`checkReceiptOpeningBridge`)**:
   - Exercises positive opening and continuity vectors at heights 0 and 2 alongside negative
     vectors (tampered sibling, tampered height, tampered chain, tampered continuity suffix,
     same-height root conflict, lower target height, and non-canonical wire encodings).
-/
import Compiler.DurableCheckpointCodec
import Compiler.ReceiptContinuityIO
import Kernel.ReceiptContinuity
import Kernel.WorldRoot
import Kernel.WorldRootCache
import Theory.AuthTrie
import Theory.StreamCodec
import Theory.AssertAxioms

namespace Minidregg.Assurance.DeployedReceiptOpening

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.ReceiptContinuityIO
open Minidregg.Kernel
open Minidregg.Kernel.WorldRoot
open Minidregg.Kernel.WorldRootCache
open Minidregg.Kernel.ReceiptContinuity

set_option autoImplicit false

/-! ## §1. Byte-level framing identities for `op 151` (`worldReceiptProof`) -/

/-- `StreamCodec.encodeNat` encodes a `Nat` as base-255 little-endian digits terminated by `255`
(`0xff`), matching `encode_nat_decimal` in `native/resource-client/src/receipt_continuity.rs`. -/
theorem encodeNat_def (n : Nat) :
    StreamCodec.encodeNat n = StreamCodec.natDigits n ++ [255] :=
  rfl

/-- `0` encodes on the wire as the single terminator byte `[255]` (`[0xff]`). -/
theorem encodeNat_zero : StreamCodec.encodeNat 0 = [255] :=
  rfl

/-- Concrete `StreamCodec.encodeNat` byte vectors matching
`encode_nat_decimal_matches_stream_codec_base255_terminator` in
`native/resource-client/src/receipt_continuity.rs`. -/
theorem encodeNat_vectors :
    StreamCodec.encodeNat 0 = [255] ∧
    StreamCodec.encodeNat 1 = [1, 255] ∧
    StreamCodec.encodeNat 254 = [254, 255] ∧
    StreamCodec.encodeNat 255 = [0, 1, 255] ∧
    StreamCodec.encodeNat 256 = [1, 1, 255] := by
  decide

/-- `WorldRoot.worldCustomization` is the UTF-8 byte list of `"DREGG.WORLD-ROOT/v3"`,
matching `WORLD_ROOT_CUSTOMIZATION` in `native/resource-client/src/receipt_continuity.rs`. -/
theorem worldCustomization_eq :
    WorldRoot.worldCustomization = "DREGG.WORLD-ROOT/v3".toUTF8.toList :=
  rfl

/-- `PersistedCodecTags.native_host_system_v1` is `"DREGG.NATIVE-HOST.SYSTEM/v2"`,
matching `SYSTEM_LEAF_CUSTOMIZATION` in `native/resource-client/src/receipt_continuity.rs`. -/
theorem systemLeafCustomization_eq :
    Minidregg.Compiler.PersistedCodecTags.native_host_system_v1 =
      "DREGG.NATIVE-HOST.SYSTEM/v2" :=
  rfl

/-- `WorldRoot.logCustomization` is the UTF-8 byte list of `"DREGG.LOG/v1"`,
matching `LOG_CHAIN_CUSTOMIZATION` in `native/resource-client/src/receipt_continuity.rs`. -/
theorem logCustomization_eq :
    WorldRoot.logCustomization = "DREGG.LOG/v1".toUTF8.toList :=
  rfl

/-- `digestStream` encodes a `Digest` by `StreamCodec.encodeNat` of its numeric value. -/
theorem digestStream_encode_eq (d : Digest) :
    digestStream.encode d = StreamCodec.encodeNat d.value :=
  rfl

/-- The `.system` key in `WorldRoot` has wire tag `[0]`. -/
theorem systemKeyBytes_eq : WorldRoot.keyBytes .system = [0] :=
  rfl

/-- The trie index seed for `.system` is `[3, 0]`, hashed under `WorldRoot.worldCustomization`. -/
theorem deployedIx_system_eq :
    WorldRoot.deployedIx .system =
      WorldRoot.bytesBits (cshake256Bytes WorldRoot.worldCustomization [3, 0]) :=
  rfl

/-- `DurableCheckpointCodec.systemLeaf` hashes the `StreamCodec` product encoding of
`(height, chain)` (`encodeNat height ++ encodeNat chain.value`). -/
theorem systemLeaf_stream_eq (height : Nat) (chain : Digest) :
    DurableCheckpointCodec.systemLeaf height chain =
      (Sp800185Cshake256.hash
        Minidregg.Compiler.PersistedCodecTags.native_host_system_v1.toUTF8.toList
        ((StreamCodec.product StreamCodec.nat digestStream).encode (height, chain))).digest :=
  rfl

/-- A `.system` leaf node in `WorldRoot` frames the leaf digest as `[1, 0] ++ encodeNat v.value`. -/
theorem systemLeafNodeBytes_eq (v : Digest) :
    WorldRoot.nodeBytes (.leaf .system v) = [1, 0] ++ digestStream.encode v :=
  rfl

/-- A branch node in `WorldRoot` frames its child digests as
`2 :: encodeNat l.value ++ encodeNat r.value`. -/
theorem branchNodeBytes_eq (l r : Digest) :
    WorldRoot.nodeBytes (.branch l r) =
      2 :: (StreamCodec.product digestStream digestStream).encode (l, r) :=
  rfl

/-- `WorldRoot.chainDigest` hashes `(acc, turn)` encoded by
`StreamCodec.product digestStream digestStream` under `WorldRoot.logCustomization`. -/
theorem chainDigest_stream_eq (acc turn : Digest) :
    WorldRoot.chainDigest acc turn =
      (Sp800185Cshake256.hash WorldRoot.logCustomization
        ((StreamCodec.product digestStream digestStream).encode (acc, turn))).digest :=
  rfl

/-- `AuthTrie.climb` (top-down recursion) equals a bottom-up `List.foldr` over `List.zip bits siblings`,
which is the exact `(0..siblings.len()).rev()` accumulator loop in
`compute_world_root_from_system_opening` (`native/resource-client/src/receipt_continuity.rs`). -/
theorem climb_eq_foldr_zip {K V D : Type} [DecidableEq K] [DecidableEq V] [DecidableEq D]
    (dig : AuthTrie.NodeIn K V D → D) (bits : List Bool) (siblings : List D) (below : D) :
    AuthTrie.climb dig bits siblings below =
      (List.zip bits siblings).foldr
        (fun bs acc => if bs.1 then dig (.branch bs.2 acc) else dig (.branch acc bs.2))
        below := by
  induction bits generalizing siblings with
  | nil =>
    cases siblings <;> rfl
  | cons b bits ih =>
    cases siblings with
    | nil => rfl
    | cons s siblings =>
      simp only [AuthTrie.climb, List.zip_cons_cons, List.foldr_cons, ih]

/-- `ReceiptContinuity.opens` holds if and only if the sibling path has length at most
`(WorldRoot.deployedIx .system).length` (`256`) and `AuthTrie.climb` along
`WorldRoot.deployedIx .system` reconstructs `point.worldRoot`, matching
`compute_world_root_from_system_opening` in `receipt_continuity.rs`. -/
theorem opens_iff_climb (point : Point) (chain : Digest) (siblings : List Digest) :
    ReceiptContinuity.opens point chain siblings = true ↔
      siblings.length ≤ (WorldRoot.deployedIx .system).length ∧
        AuthTrie.climb WorldRoot.worldDig
          ((WorldRoot.deployedIx .system).take siblings.length)
          siblings
          (WorldRoot.worldDig
            (.leaf .system (DurableCheckpointCodec.systemLeaf point.height chain))) =
          point.worldRoot := by
  unfold ReceiptContinuity.opens AuthTrie.verify AuthTrie.Terminal.input
  simp [Bool.and_eq_true, decide_eq_true_eq]

/-- Bottom-up `List.foldr` formulation of `ReceiptContinuity.opens`, matching the reverse loop
in `compute_world_root_from_system_opening` (`native/resource-client/src/receipt_continuity.rs`). -/
theorem opens_iff_foldr_zip (point : Point) (chain : Digest) (siblings : List Digest) :
    ReceiptContinuity.opens point chain siblings = true ↔
      siblings.length ≤ (WorldRoot.deployedIx .system).length ∧
        (List.zip ((WorldRoot.deployedIx .system).take siblings.length) siblings).foldr
          (fun bs acc =>
            if bs.1 then WorldRoot.worldDig (.branch bs.2 acc)
            else WorldRoot.worldDig (.branch acc bs.2))
          (WorldRoot.worldDig
            (.leaf .system (DurableCheckpointCodec.systemLeaf point.height chain))) =
          point.worldRoot := by
  rw [opens_iff_climb, climb_eq_foldr_zip]

/-! ## §2. `StreamCodec` / `LawfulCodec` definitions, roundtrip & canonicality -/

/-- A self-contained opening witness record pairing a checkpoint `Point` (`height`, `worldRoot`)
with its `chain` digest and Merkle sibling path. -/
structure OpeningRecord where
  point : ReceiptContinuity.Point
  chain : Digest
  siblings : List Digest
deriving DecidableEq, Repr

/-- Convert a `ReceiptContinuityIO.RootWitness` to an `OpeningRecord`. -/
def OpeningRecord.ofRootWitness (w : ReceiptContinuityIO.RootWitness) : OpeningRecord :=
  ⟨w.point, w.chain, w.siblings⟩

/-- Convert an `OpeningRecord` to a `ReceiptContinuityIO.RootWitness`. -/
def OpeningRecord.toRootWitness (r : OpeningRecord) : ReceiptContinuityIO.RootWitness :=
  ⟨r.point, r.chain, r.siblings⟩

/-- `StreamCodec` for `ReceiptContinuity.Point`. -/
def pointStream : StreamCodec ReceiptContinuity.Point :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat digestStream)
    (fun p => (p.height, p.worldRoot))
    (fun ⟨h, r⟩ => ⟨h, r⟩)
    (by intro p; rfl)

/-- `LawfulCodec` for `ReceiptContinuity.Point`. -/
def pointCodec : LawfulCodec ReceiptContinuity.Point :=
  pointStream.toLawful

/-- `StreamCodec` for `ReceiptContinuityIO.RootWitness`. -/
def rootWitnessStream : StreamCodec ReceiptContinuityIO.RootWitness :=
  StreamCodec.xmap
    (StreamCodec.product pointStream
      (StreamCodec.product digestStream (StreamCodec.list digestStream)))
    (fun w => (w.point, (w.chain, w.siblings)))
    (fun ⟨p, c, s⟩ => ⟨p, c, s⟩)
    (by intro w; rfl)

/-- `LawfulCodec` for `ReceiptContinuityIO.RootWitness`. -/
def rootWitnessCodec : LawfulCodec ReceiptContinuityIO.RootWitness :=
  rootWitnessStream.toLawful

/-- `StreamCodec` for `OpeningRecord`. -/
def openingRecordStream : StreamCodec OpeningRecord :=
  StreamCodec.xmap
    (StreamCodec.product pointStream
      (StreamCodec.product digestStream (StreamCodec.list digestStream)))
    (fun r => (r.point, (r.chain, r.siblings)))
    (fun ⟨p, c, s⟩ => ⟨p, c, s⟩)
    (by intro r; rfl)

/-- `LawfulCodec` for `OpeningRecord`. -/
def openingRecordCodec : LawfulCodec OpeningRecord :=
  openingRecordStream.toLawful

/-- `StreamCodec` for `ReceiptContinuity.Identity`. -/
def identityStream : StreamCodec ReceiptContinuity.Identity :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream digestStream))
    (fun id => (id.domain, (id.semantics, id.expectedSeed)))
    (fun ⟨d, s, e⟩ => ⟨d, s, e⟩)
    (by intro id; rfl)

/-- `StreamCodec` for `ReceiptContinuity.Query`. -/
def queryStream : StreamCodec ReceiptContinuity.Query :=
  StreamCodec.xmap
    (StreamCodec.product identityStream
      (StreamCodec.product (StreamCodec.option pointStream) pointStream))
    (fun q => (q.identity, (q.anchor, q.target)))
    (fun ⟨sysId, a, t⟩ => ⟨sysId, a, t⟩)
    (by intro q; rfl)

/-- `StreamCodec` for `ReceiptContinuity.Extension`. -/
def extensionStream : StreamCodec ReceiptContinuity.Extension :=
  StreamCodec.xmap
    (StreamCodec.product identityStream
      (StreamCodec.product pointStream
        (StreamCodec.product pointStream
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product (StreamCodec.list digestStream)
                (StreamCodec.product (StreamCodec.list digestStream)
                  (StreamCodec.product (StreamCodec.list digestStream)
                    StreamCodec.bool))))))))
    (fun e =>
      (e.identity,
        (e.startPoint,
          (e.endPoint,
            (e.startChain,
              (e.endChain,
                (e.fromSiblings, (e.toSiblings, (e.suffix, e.complete)))))))))
    (fun ⟨sysId, sp, ep, sc, ec, fs, ts, suf, comp⟩ =>
      ⟨sysId, sp, ep, sc, ec, fs, ts, suf, comp⟩)
    (by intro e; rfl)

/-- `StreamCodec` for a complete `(Query, Extension)` continuity verification envelope. -/
def continuityEnvelopeStream :
    StreamCodec (ReceiptContinuity.Query × ReceiptContinuity.Extension) :=
  StreamCodec.product queryStream extensionStream

/-- `LawfulCodec` for a complete `(Query, Extension)` continuity verification envelope. -/
def continuityEnvelopeCodec :
    LawfulCodec (ReceiptContinuity.Query × ReceiptContinuity.Extension) :=
  continuityEnvelopeStream.toLawful

/-- `StreamCodec.nat` roundtrips every `Nat` through `encodeNat` and `toLawful.decode`. -/
theorem encodeNat_roundtrip (n : Nat) :
    StreamCodec.nat.toLawful.decode (StreamCodec.encodeNat n) = some n :=
  StreamCodec.nat.toLawful.decode_encode n

/-- `StreamCodec.nat` is canonical: any byte slice accepted by `toLawful.decode` is the exact
`encodeNat` encoding of the decoded natural. -/
theorem encodeNat_canonical {bytes : List UInt8} {n : Nat}
    (h : StreamCodec.nat.toLawful.decode bytes = some n) :
    StreamCodec.encodeNat n = bytes :=
  StreamCodec.nat.toLawful_canonical bytes n h

/-- Non-canonical leading-zero base-255 natural `[0, 255]` is rejected by `decodeNatPrefix` and
`StreamCodec.nat.toLawful.decode`. -/
theorem noncanonical_zero_rejected :
    StreamCodec.decodeNatPrefix [0, 255] = none ∧
      StreamCodec.nat.toLawful.decode [0, 255] = none := by
  decide

/-- `rootWitnessCodec` roundtrips every `RootWitness`. -/
theorem rootWitnessCodec_roundtrip (w : ReceiptContinuityIO.RootWitness) :
    rootWitnessCodec.decode (rootWitnessCodec.encode w) = some w :=
  rootWitnessCodec.decode_encode w

/-- `rootWitnessCodec` is canonical on wire bytes. -/
theorem rootWitnessCodec_canonical {bytes : List UInt8} {w : ReceiptContinuityIO.RootWitness}
    (h : rootWitnessCodec.decode bytes = some w) :
    rootWitnessCodec.encode w = bytes :=
  rootWitnessStream.toLawful_canonical bytes w h

/-- `openingRecordCodec` roundtrips every `OpeningRecord`. -/
theorem openingRecordCodec_roundtrip (rec : OpeningRecord) :
    openingRecordCodec.decode (openingRecordCodec.encode rec) = some rec :=
  openingRecordCodec.decode_encode rec

/-- `openingRecordCodec` is canonical on wire bytes. -/
theorem openingRecordCodec_canonical {bytes : List UInt8} {rec : OpeningRecord}
    (h : openingRecordCodec.decode bytes = some rec) :
    openingRecordCodec.encode rec = bytes :=
  openingRecordStream.toLawful_canonical bytes rec h

/-- `continuityEnvelopeCodec` roundtrips every `(Query, Extension)` pair. -/
theorem continuityEnvelopeCodec_roundtrip
    (env : ReceiptContinuity.Query × ReceiptContinuity.Extension) :
    continuityEnvelopeCodec.decode (continuityEnvelopeCodec.encode env) = some env :=
  continuityEnvelopeCodec.decode_encode env

/-- `continuityEnvelopeCodec` is canonical on wire bytes. -/
theorem continuityEnvelopeCodec_canonical
    {bytes : List UInt8} {env : ReceiptContinuity.Query × ReceiptContinuity.Extension}
    (h : continuityEnvelopeCodec.decode bytes = some env) :
    continuityEnvelopeCodec.encode env = bytes :=
  continuityEnvelopeStream.toLawful_canonical bytes env h

/-! ## §3. Soundness Bridge to `Kernel.ReceiptContinuity.opens_sound` -/

/-- `ValidOpening point chain es` states that `DurableCheckpointCodec.systemLeaf point.height chain`
is the authentic value bound to `.system` in the checkpoint's world-root entry list `es`. -/
def ValidOpening (point : ReceiptContinuity.Point) (chain : Digest)
    (es : List (WorldRoot.Key × Digest)) : Prop :=
  some (DurableCheckpointCodec.systemLeaf point.height chain) =
    AuthTrie.lastVal es .system

/-- `ConcreteCollision` states that two distinct byte strings hash to the same digest under
`WorldRoot.deployedHash` (`cSHAKE256` with customization `WorldRoot.worldCustomization`). -/
def ConcreteCollision : Prop :=
  ∃ x y : List UInt8, x ≠ y ∧ WorldRoot.deployedHash x = WorldRoot.deployedHash y

/-- Total, finite, deterministic checker for a single `OpeningRecord`. -/
def checkOpeningRecord (rec : OpeningRecord) : Bool :=
  ReceiptContinuity.opens rec.point rec.chain rec.siblings

/-- `checkOpeningRecord` returns `true` iff `ReceiptContinuity.opens` returns `true`. -/
theorem checkOpeningRecord_eq_true_iff_opens (rec : OpeningRecord) :
    checkOpeningRecord rec = true ↔
      ReceiptContinuity.opens rec.point rec.chain rec.siblings = true :=
  Iff.rfl

/-- Any `OpeningRecord` accepted by `checkOpeningRecord` establishes
`ValidOpening ∨ ConcreteCollision` against any entry list `es` whose `deployedRoot` is
`rec.point.worldRoot`. -/
theorem checkOpeningRecord_sound {rec : OpeningRecord}
    {es : List (WorldRoot.Key × Digest)}
    (hroot : rec.point.worldRoot = WorldRoot.deployedRoot es)
    (hcheck : checkOpeningRecord rec = true) :
    ValidOpening rec.point rec.chain es ∨ ConcreteCollision :=
  ReceiptContinuity.opens_sound rec.point rec.chain rec.siblings es hroot hcheck

/-- **Byte-level `op 151` opening soundness bridge**:
If a wire byte slice `bytes` decodes via `openingRecordCodec` to `rec` and `checkOpeningRecord rec`
returns `true`, then `bytes` is the unique canonical encoding of `rec` AND
`ValidOpening rec.point rec.chain es ∨ ConcreteCollision` holds for the checkpoint's `worldRoot`. -/
theorem wireOpening_sound {bytes : List UInt8} {rec : OpeningRecord}
    {es : List (WorldRoot.Key × Digest)}
    (hdecode : openingRecordCodec.decode bytes = some rec)
    (hroot : rec.point.worldRoot = WorldRoot.deployedRoot es)
    (hcheck : checkOpeningRecord rec = true) :
    openingRecordCodec.encode rec = bytes ∧
      (ValidOpening rec.point rec.chain es ∨ ConcreteCollision) :=
  ⟨openingRecordCodec_canonical hdecode, checkOpeningRecord_sound hroot hcheck⟩

/-- **Byte-level `op 151` continuity verification soundness bridge**:
If a wire byte slice `bytes` decodes via `continuityEnvelopeCodec` to `(q, e)` and the
deterministic checker `ReceiptContinuity.verify q e` returns `.ok e.endPoint`, then:
1. `bytes` is the canonical wire encoding of `(q, e)`,
2. `ReceiptContinuity.Valid q e` holds,
3. `chainAfterDigests e.startChain e.suffix = e.endChain`, and
4. Against any start and end checkpoint entry lists `startEntries` and `endEntries` with
   `e.startPoint.worldRoot = WorldRoot.deployedRoot startEntries` and
   `e.endPoint.worldRoot = WorldRoot.deployedRoot endEntries`,
   `ValidOpening ∨ ConcreteCollision` holds at both endpoints. -/
theorem wireContinuity_verify_sound
    {bytes : List UInt8} {q : ReceiptContinuity.Query} {e : ReceiptContinuity.Extension}
    {startEntries endEntries : List (WorldRoot.Key × Digest)}
    (hdecode : continuityEnvelopeCodec.decode bytes = some (q, e))
    (hverify : ReceiptContinuity.verify q e = .ok e.endPoint)
    (hstartRoot : e.startPoint.worldRoot = WorldRoot.deployedRoot startEntries)
    (hendRoot : e.endPoint.worldRoot = WorldRoot.deployedRoot endEntries) :
    continuityEnvelopeCodec.encode (q, e) = bytes ∧
      ReceiptContinuity.Valid q e ∧
      e.startPoint = q.start ∧
      ReceiptContinuity.chainAfterDigests e.startChain e.suffix = e.endChain ∧
      (ValidOpening e.startPoint e.startChain startEntries ∨ ConcreteCollision) ∧
      (ValidOpening e.endPoint e.endChain endEntries ∨ ConcreteCollision) := by
  have hcanon := continuityEnvelopeCodec_canonical hdecode
  have hvalid := (ReceiptContinuity.verify_ok_iff q e).mp hverify
  obtain ⟨hstart, hchain, hopenStart, hopenEnd⟩ :=
    ReceiptContinuity.accepted_binds_chain q e hverify
  exact ⟨hcanon, hvalid, hstart, hchain,
    ReceiptContinuity.opens_sound e.startPoint e.startChain e.fromSiblings startEntries
      hstartRoot hopenStart,
    ReceiptContinuity.opens_sound e.endPoint e.endChain e.toSiblings endEntries
      hendRoot hopenEnd⟩

/-- When `q.anchor = some anchorPoint`, acceptance of a decoded `(q, e)` envelope binds
`e.startPoint = anchorPoint`, verifies the durable log chain `chainAfterDigests`, and establishes
`ValidOpening ∨ ConcreteCollision` at both the anchored and end checkpoints. -/
theorem wireContinuity_known_binds_chain
    {bytes : List UInt8} {q : ReceiptContinuity.Query} {e : ReceiptContinuity.Extension}
    {anchorPoint : ReceiptContinuity.Point}
    {anchorEntries endEntries : List (WorldRoot.Key × Digest)}
    (hdecode : continuityEnvelopeCodec.decode bytes = some (q, e))
    (hverify : ReceiptContinuity.verify q e = .ok e.endPoint)
    (hanchor : q.anchor = some anchorPoint)
    (hanchorRoot : anchorPoint.worldRoot = WorldRoot.deployedRoot anchorEntries)
    (hendRoot : e.endPoint.worldRoot = WorldRoot.deployedRoot endEntries) :
    continuityEnvelopeCodec.encode (q, e) = bytes ∧
      e.startPoint = anchorPoint ∧
      ReceiptContinuity.chainAfterDigests e.startChain e.suffix = e.endChain ∧
      (ValidOpening anchorPoint e.startChain anchorEntries ∨ ConcreteCollision) ∧
      (ValidOpening e.endPoint e.endChain endEntries ∨ ConcreteCollision) := by
  have hstartEq : q.start = anchorPoint := by
    unfold ReceiptContinuity.Query.start
    rw [hanchor]
    rfl
  obtain ⟨hstart0, _, _, _⟩ := ReceiptContinuity.accepted_binds_chain q e hverify
  have hsp : e.startPoint = anchorPoint := hstart0.trans hstartEq
  obtain ⟨hcanon, _, _, hchain, hopenStart, hopenEnd⟩ :=
    wireContinuity_verify_sound hdecode hverify
      (by rw [hsp]; exact hanchorRoot) hendRoot
  rw [hsp] at hopenStart
  exact ⟨hcanon, hsp, hchain, hopenStart, hopenEnd⟩

/-! ## §4. Computable Audit Fixtures & Positive/Negative Test Vectors -/

/-- Build an authentic `OpeningRecord` at `(height, chain)` with sample cell `(7, ⟨91⟩)`. -/
def makeAuditOpening (height : Nat) (chain : Digest) : OpeningRecord :=
  let roots := RootCache.ofEntries
    [(.system, DurableCheckpointCodec.systemLeaf height chain), (.cell 7, ⟨91⟩)]
  ⟨⟨height, roots.root⟩, chain, ReceiptContinuityIO.systemSiblings roots⟩

/-- Sample continuity identity. -/
def auditIdentity : ReceiptContinuity.Identity :=
  ⟨⟨1⟩, ⟨2⟩, ⟨3⟩⟩

/-- Authentic opening at height 0 with chain `⟨13⟩`. -/
def opening0 : OpeningRecord :=
  makeAuditOpening 0 ⟨13⟩

/-- Two-entry log suffix `[⟨17⟩, ⟨18⟩]`. -/
def auditSuffix : List Digest :=
  [⟨17⟩, ⟨18⟩]

/-- Authentic opening at height 2 after folding `auditSuffix` from `opening0.chain`. -/
def opening2 : OpeningRecord :=
  makeAuditOpening 2 (ReceiptContinuity.chainAfterDigests opening0.chain auditSuffix)

/-- Cross-language test vector matching `system_opening_reconstructs_world_root_and_rejects_tamper`
in `native/resource-client/src/receipt_continuity.rs`:
`height = 7`, `chain = chainAfterDigests ⟨0⟩ [⟨111⟩, ⟨222⟩]`,
`siblings = [⟨12345⟩, ⟨67890⟩, ⟨54321⟩]`. -/
def rustCompatOpening7 : OpeningRecord :=
  let chain := ReceiptContinuity.chainAfterDigests ⟨0⟩ [⟨111⟩, ⟨222⟩]
  let siblings : List Digest := [⟨12345⟩, ⟨67890⟩, ⟨54321⟩]
  let worldRoot :=
    AuthTrie.climb WorldRoot.worldDig
      ((WorldRoot.deployedIx .system).take siblings.length)
      siblings
      (WorldRoot.worldDig (.leaf .system (DurableCheckpointCodec.systemLeaf 7 chain)))
  ⟨⟨7, worldRoot⟩, chain, siblings⟩

/-- Authentic continuity query and extension from `opening0` (height 0) to `opening2` (height 2). -/
def query0to2 : ReceiptContinuity.Query :=
  ⟨auditIdentity, some opening0.point, opening2.point⟩

def ext0to2 : ReceiptContinuity.Extension :=
  ⟨auditIdentity, opening0.point, opening2.point, opening0.chain, opening2.chain,
    opening0.siblings, opening2.siblings, auditSuffix, true⟩

/-- Fresh bootstrap query and extension (no prior anchor) at `opening2`. -/
def queryBootstrap2 : ReceiptContinuity.Query :=
  ⟨auditIdentity, none, opening2.point⟩

def extBootstrap2 : ReceiptContinuity.Extension :=
  ⟨auditIdentity, opening2.point, opening2.point, opening2.chain, opening2.chain,
    opening2.siblings, opening2.siblings, [], true⟩

/-- Tamper helper: increment the first sibling digest in a path. -/
def tamperFirstSibling : List Digest → List Digest
  | [] => [⟨1⟩]
  | d :: ds => ⟨d.value + 1⟩ :: ds

/-- Negative vector 1: tampered sibling in `opening2`. -/
def opening2TamperedSibling : OpeningRecord :=
  { opening2 with siblings := tamperFirstSibling opening2.siblings }

/-- Negative vector 2: tampered height (`3` instead of `2`) against `opening2`'s `worldRoot`. -/
def opening2TamperedHeight : OpeningRecord :=
  { opening2 with point := { opening2.point with height := 3 } }

/-- Negative vector 3: tampered chain (`chain.value + 1`) against `opening2`'s `worldRoot`. -/
def opening2TamperedChain : OpeningRecord :=
  { opening2 with chain := ⟨opening2.chain.value + 1⟩ }

/-- Computable audit function exercising positive opening/continuity checks, wire codec
roundtrips, non-canonical wire rejections, and negative tampered-sibling / tampered-height /
tampered-chain vectors (including the `receipt_continuity.rs` cross-language height-7 vector). -/
def checkReceiptOpeningBridge : Bool :=
  let accepted (q : ReceiptContinuity.Query) (e : ReceiptContinuity.Extension) : Bool :=
    (ReceiptContinuity.verify q e).isOk
  -- Positive 1: checkpoint openings at height 0, height 2, and the Rust height-7 vector pass
  checkOpeningRecord opening0 &&
  checkOpeningRecord opening2 &&
  checkOpeningRecord rustCompatOpening7 &&
  -- Positive 2: wire codecs roundtrip opening records and continuity envelopes
  (openingRecordCodec.decode (openingRecordCodec.encode opening0) == some opening0) &&
  (openingRecordCodec.decode (openingRecordCodec.encode opening2) == some opening2) &&
  (openingRecordCodec.decode (openingRecordCodec.encode rustCompatOpening7) ==
    some rustCompatOpening7) &&
  (continuityEnvelopeCodec.decode (continuityEnvelopeCodec.encode (query0to2, ext0to2)) ==
    some (query0to2, ext0to2)) &&
  -- Positive 3: `ReceiptContinuity.verify` accepts both anchored and bootstrap queries
  accepted query0to2 ext0to2 &&
  accepted queryBootstrap2 extBootstrap2 &&
  -- Negative 1: tampered sibling rejected by `checkOpeningRecord` and `ReceiptContinuity.verify`
  !checkOpeningRecord opening2TamperedSibling &&
  !checkOpeningRecord { rustCompatOpening7 with siblings := [⟨12345⟩, ⟨67891⟩, ⟨54321⟩] } &&
  !accepted query0to2 { ext0to2 with toSiblings := opening2TamperedSibling.siblings } &&
  !accepted query0to2 { ext0to2 with fromSiblings := tamperFirstSibling opening0.siblings } &&
  !accepted query0to2 { ext0to2 with toSiblings := ⟨0⟩ :: opening2.siblings } &&
  -- Negative 2: tampered height rejected by `checkOpeningRecord` and `ReceiptContinuity.verify`
  !checkOpeningRecord opening2TamperedHeight &&
  !checkOpeningRecord { rustCompatOpening7 with point := { rustCompatOpening7.point with height := 8 } } &&
  !accepted { query0to2 with target := opening2TamperedHeight.point }
    { ext0to2 with endPoint := opening2TamperedHeight.point } &&
  -- Negative 3: tampered chain rejected by `checkOpeningRecord` and `ReceiptContinuity.verify`
  !checkOpeningRecord opening2TamperedChain &&
  !checkOpeningRecord { rustCompatOpening7 with chain := ⟨999⟩ } &&
  !accepted query0to2 { ext0to2 with endChain := opening2TamperedChain.chain } &&
  !accepted query0to2 { ext0to2 with startChain := ⟨opening0.chain.value + 1⟩ } &&
  -- Negative 4: tampered suffix / rollback / same-height conflict rejected
  !accepted query0to2 { ext0to2 with suffix := [⟨19⟩, ⟨18⟩] } &&
  !accepted { query0to2 with anchor := some opening2.point, target := opening0.point } ext0to2 &&
  !accepted ⟨auditIdentity, some opening2.point, { opening2.point with worldRoot := ⟨0⟩ }⟩ ext0to2 &&
  -- Negative 5: non-canonical natural encoding `[0, 255]` and trailing garbage rejected on wire
  (StreamCodec.nat.toLawful.decode [0, 255] == none) &&
  (openingRecordCodec.decode (openingRecordCodec.encode opening0 ++ [0]) == none)

#guard checkOpeningRecord opening0 = true
#guard checkOpeningRecord opening2 = true
#guard checkOpeningRecord rustCompatOpening7 = true
#guard (openingRecordCodec.decode (openingRecordCodec.encode opening0) == some opening0) = true
#guard (openingRecordCodec.decode (openingRecordCodec.encode opening2) == some opening2) = true
#guard (openingRecordCodec.decode (openingRecordCodec.encode rustCompatOpening7) ==
  some rustCompatOpening7) = true
#guard (continuityEnvelopeCodec.decode (continuityEnvelopeCodec.encode (query0to2, ext0to2)) ==
  some (query0to2, ext0to2)) = true
#guard (ReceiptContinuity.verify query0to2 ext0to2).isOk = true
#guard (ReceiptContinuity.verify queryBootstrap2 extBootstrap2).isOk = true
#guard checkOpeningRecord opening2TamperedSibling = false
#guard checkOpeningRecord opening2TamperedHeight = false
#guard checkOpeningRecord opening2TamperedChain = false
#guard checkReceiptOpeningBridge = true

/-! ## §5. Axiom Audit -/

#assert_axioms encodeNat_vectors
#assert_axioms climb_eq_foldr_zip
#assert_axioms opens_iff_climb
#assert_axioms opens_iff_foldr_zip
#assert_axioms encodeNat_roundtrip
#assert_axioms encodeNat_canonical
#assert_axioms noncanonical_zero_rejected
#assert_axioms rootWitnessCodec_roundtrip
#assert_axioms rootWitnessCodec_canonical
#assert_axioms openingRecordCodec_roundtrip
#assert_axioms openingRecordCodec_canonical
#assert_axioms continuityEnvelopeCodec_roundtrip
#assert_axioms continuityEnvelopeCodec_canonical
#assert_axioms checkOpeningRecord_eq_true_iff_opens
#assert_axioms checkOpeningRecord_sound
#assert_axioms wireOpening_sound
#assert_axioms wireContinuity_verify_sound
#assert_axioms wireContinuity_known_binds_chain

/-- info: 'Minidregg.Assurance.DeployedReceiptOpening.wireOpening_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wireOpening_sound
/-- info: 'Minidregg.Assurance.DeployedReceiptOpening.wireContinuity_verify_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wireContinuity_verify_sound
/-- info: 'Minidregg.Assurance.DeployedReceiptOpening.wireContinuity_known_binds_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wireContinuity_known_binds_chain

end Minidregg.Assurance.DeployedReceiptOpening
