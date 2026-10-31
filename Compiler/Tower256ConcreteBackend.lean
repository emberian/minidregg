/-
# Compiler.Tower256ConcreteBackend -- one shared concrete binary backend

This module owns the single concrete `Backend (binaryTower 8)` intended for
Tower256 LogUp and additive PCS constructions.  It combines:

* the exact recursive Fan--Paar semantic field profile;
* the Lean-owned SP 800-185 cSHAKE256 computation;
* compact, prefix-decodable codecs for Merkle paths and transcript values, built on the
  candidate-independent codec nucleus `Theory.StreamCodec` (re-exported by `public import`;
  its declarations share this module's namespace);
* fixed readable leaf/node/absorb/draw customization strings;
* stable first-order algorithm, suite, codec, and value-type pins.

Consumers should depend on `backend`, `towerExact`, and `cshakeExact` instead
of rebuilding local copies.  Per-column IDs and proof-suite binding premises
remain consumer data.  This file proves functional codec and projection facts,
not collision resistance, a random-oracle theorem, PCS soundness, or any Rust
semantics.
-/

module

public import Compiler.BinaryTower256Profile
public import Compiler.Sp800185Cshake256
public import Theory.StreamCodec
public import Theory.Bignum
public import Theory.AssertAxioms
meta import Compiler.BinaryTower256Profile
meta import Compiler.Sp800185Cshake256
meta import Theory.StreamCodec
meta import Theory.Bignum
meta import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Compiler.Tower256ConcreteBackend

open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.NativeKernelPlan (WorkKind)
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

def merklePathStream : StreamCodec (List Digest) :=
  StreamCodec.list digestStream

def merklePathCodec : LawfulCodec (List Digest) :=
  merklePathStream.toLawful

def drawRoleStream : StreamCodec DrawRole :=
  withTagCursor
  { encode := fun
      | .roundChallenge => [0]
      | .queryChallenge => [1]
    decodePrefix := fun
      | 0 :: suffix => some (.roundChallenge, suffix)
      | 1 :: suffix => some (.queryChallenge, suffix)
      | _ => none
    decodePrefix_encode := by intro value suffix; cases value <;> rfl }
    rfl (by one_octet_tag)

def columnRoleStream : StreamCodec ColumnRole :=
  withTagCursor
  { encode := fun
      | .semanticTrace => [0]
      | .lookupAddress => [1]
      | .lookupWeight => [2]
      | .lookupTable => [3]
      | .accumulator => [4]
      | .checkpoint => [5]
      | .auxiliary => [6]
    decodePrefix := fun
      | 0 :: suffix => some (.semanticTrace, suffix)
      | 1 :: suffix => some (.lookupAddress, suffix)
      | 2 :: suffix => some (.lookupWeight, suffix)
      | 3 :: suffix => some (.lookupTable, suffix)
      | 4 :: suffix => some (.accumulator, suffix)
      | 5 :: suffix => some (.checkpoint, suffix)
      | 6 :: suffix => some (.auxiliary, suffix)
      | _ => none
    decodePrefix_encode := by intro value suffix; cases value <;> rfl }
    rfl (by one_octet_tag)

def reprEqRoleStream : StreamCodec ReprEqRole :=
  withTagCursor
  { encode := fun
      | .representationEquality => [0]
      | .sameOpening => [1]
    decodePrefix := fun
      | 0 :: suffix => some (.representationEquality, suffix)
      | 1 :: suffix => some (.sameOpening, suffix)
      | _ => none
    decodePrefix_encode := by intro value suffix; cases value <;> rfl }
    rfl (by one_octet_tag)

def workKindStream : StreamCodec WorkKind :=
  withTagCursor
  { encode := fun
      | .arithmetic => [0]
      | .hash => [1]
      | .transform => [2]
    decodePrefix := fun
      | 0 :: suffix => some (.arithmetic, suffix)
      | 1 :: suffix => some (.hash, suffix)
      | 2 :: suffix => some (.transform, suffix)
      | _ => none
    decodePrefix_encode := by intro value suffix; cases value <;> rfl }
    rfl (by one_octet_tag)

abbrev RootSlotWire :=
  Digest × ColumnRole × Digest × Digest × Digest × Digest × Digest ×
    Digest × Digest × Digest

def rootSlotWireStream : StreamCodec RootSlotWire :=
  StreamCodec.product digestStream
    (StreamCodec.product columnRoleStream
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product digestStream
                (StreamCodec.product digestStream
                  (StreamCodec.product digestStream digestStream))))))))

def rootSlotStream : StreamCodec RootSlot :=
  StreamCodec.xmap rootSlotWireStream
    (fun slot => (slot.slotId, slot.role, slot.semanticTypeId,
      slot.representationId, slot.carrierProfileId, slot.semanticCodecId,
      slot.representationCodecId, slot.domainId, slot.domainCodecId,
      slot.commitmentSuiteId))
    (fun (slotId, role, semanticTypeId, representationId, carrierProfileId,
        semanticCodecId, representationCodecId, domainId, domainCodecId,
        commitmentSuiteId) =>
      ⟨slotId, role, semanticTypeId, representationId, carrierProfileId,
       semanticCodecId, representationCodecId, domainId, domainCodecId,
       commitmentSuiteId⟩)
    (by intro slot; cases slot; rfl)

def rootRecordStream : StreamCodec RootRecord :=
  StreamCodec.xmap (StreamCodec.product rootSlotStream digestStream)
    (fun record => (record.slot, record.root))
    (fun (slot, root) => ⟨slot, root⟩)
    (by intro record; cases record; rfl)

abbrev NativeRecordWire :=
  Digest × WorkKind × Digest × Digest × Digest × List UInt8 × List UInt8

def nativeRecordWireStream : StreamCodec NativeRecordWire :=
  StreamCodec.product digestStream
    (StreamCodec.product workKindStream
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product digestStream
            (StreamCodec.product bytesStream bytesStream)))))

def nativeRecordStream : StreamCodec NativeRecord :=
  StreamCodec.xmap nativeRecordWireStream
    (fun record => (record.callSlotId, record.kind, record.carrierProfileId,
      record.inputCodecId, record.outputCodecId, record.inputBytes,
      record.outputBytes))
    (fun (callSlotId, kind, carrierProfileId, inputCodecId, outputCodecId,
        inputBytes, outputBytes) =>
      ⟨callSlotId, kind, carrierProfileId, inputCodecId, outputCodecId,
       inputBytes, outputBytes⟩)
    (by intro record; cases record; rfl)

abbrev OpeningRecordWire :=
  Digest × RootRecord × List UInt8 × List UInt8 × List UInt8 ×
    Digest × List UInt8

def openingRecordWireStream : StreamCodec OpeningRecordWire :=
  StreamCodec.product digestStream
    (StreamCodec.product rootRecordStream
      (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream
            (StreamCodec.product digestStream bytesStream)))))

def openingRecordStream : StreamCodec OpeningRecord :=
  StreamCodec.xmap openingRecordWireStream
    (fun record => (record.openingSlotId, record.root, record.indexBytes,
      record.semanticValueBytes, record.representationValueBytes,
      record.proofCodecId, record.proofBytes))
    (fun (openingSlotId, root, indexBytes, semanticValueBytes,
        representationValueBytes, proofCodecId, proofBytes) =>
      ⟨openingSlotId, root, indexBytes, semanticValueBytes,
       representationValueBytes, proofCodecId, proofBytes⟩)
    (by intro record; cases record; rfl)

abbrev ReprEqRecordWire := Digest × ReprEqRole × Digest × Digest

def reprEqRecordWireStream : StreamCodec ReprEqRecordWire :=
  StreamCodec.product digestStream
    (StreamCodec.product reprEqRoleStream
      (StreamCodec.product digestStream digestStream))

def reprEqRecordStream : StreamCodec ReprEqRecord :=
  StreamCodec.xmap reprEqRecordWireStream
    (fun record => (record.bridgeId, record.role, record.sourceOpeningSlotId,
      record.targetOpeningSlotId))
    (fun (bridgeId, role, sourceOpeningSlotId, targetOpeningSlotId) =>
      ⟨bridgeId, role, sourceOpeningSlotId, targetOpeningSlotId⟩)
    (by intro record; cases record; rfl)

def drawLabelStream : StreamCodec GlobalDrawLabel :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product drawRoleStream StreamCodec.nat))
    (fun label => (label.transcriptDomain, label.role, label.ordinal))
    (fun (transcriptDomain, role, ordinal) =>
      ⟨transcriptDomain, role, ordinal⟩)
    (by intro label; cases label; rfl)

def globalDrawLabelCodec : LawfulCodec GlobalDrawLabel :=
  drawLabelStream.toLawful

abbrev GlobalFrameWire :=
  Sum (Digest × List UInt8)
    (Sum RootRecord
      (Sum NativeRecord (Sum OpeningRecord ReprEqRecord)))

def globalFrameWireStream : StreamCodec GlobalFrameWire :=
  StreamCodec.sum (StreamCodec.product digestStream bytesStream)
    (StreamCodec.sum rootRecordStream
      (StreamCodec.sum nativeRecordStream
        (StreamCodec.sum openingRecordStream reprEqRecordStream)))

def globalFrameStream : StreamCodec GlobalFrame :=
  StreamCodec.xmap globalFrameWireStream
    (fun frame => match frame with
      | .publicContext domain bytes => .inl (domain, bytes)
      | .root record => .inr (.inl record)
      | .nativeReply record => .inr (.inr (.inl record))
      | .opening record => .inr (.inr (.inr (.inl record)))
      | .representationEdge record => .inr (.inr (.inr (.inr record))))
    (fun wire => match wire with
      | .inl (domain, bytes) => .publicContext domain bytes
      | .inr (.inl record) => .root record
      | .inr (.inr (.inl record)) => .nativeReply record
      | .inr (.inr (.inr (.inl record))) => .opening record
      | .inr (.inr (.inr (.inr record))) => .representationEdge record)
    (by intro frame; cases frame <;> rfl)

def globalFrameCodec : LawfulCodec GlobalFrame :=
  globalFrameStream.toLawful

/-! ## Stable IDs and domain strings -/

def id (value : Nat) : Digest := ⟨value⟩

def cshakeAlgorithmId : Digest := id 8400
def digestCodecPin : CodecPin := ⟨id 8401, id 8501, 1⟩
def merklePathCodecPin : CodecPin := ⟨id 8402, id 8502, 1⟩
def globalFrameCodecPin : CodecPin := ⟨id 8403, id 8503, 1⟩
def globalDrawLabelCodecPin : CodecPin := ⟨id 8404, id 8504, 1⟩
def merkleSuiteId : Digest := id 8600

def utf8 (value : String) : List UInt8 := value.toUTF8.toList

/-- The leading byte is an explicit suite-local domain tag; the suffix stays
human-readable in traces and manifests. -/
def leafCustomization : List UInt8 :=
  0x01 :: utf8 "MINIDREGG/TOWER256/MERKLE/LEAF/V1"

def nodeCustomization : List UInt8 :=
  0x02 :: utf8 "MINIDREGG/TOWER256/MERKLE/NODE/V1"

def absorbDomain : List UInt8 :=
  0x03 :: utf8 "MINIDREGG/TOWER256/TRANSCRIPT/ABSORB/V1"

def squeezeDomain : List UInt8 :=
  0x04 :: utf8 "MINIDREGG/TOWER256/TRANSCRIPT/DRAW/V1"

def drawFrameTag : UInt8 := 0xd1

theorem customizationDomains_nodup :
    [leafCustomization, nodeCustomization, absorbDomain, squeezeDomain].Nodup := by
  simp [leafCustomization, nodeCustomization, absorbDomain, squeezeDomain]

theorem leaf_node_distinct : leafCustomization ≠ nodeCustomization := by
  simp [leafCustomization, nodeCustomization]

theorem absorb_squeeze_distinct : absorbDomain ≠ squeezeDomain := by
  simp [absorbDomain, squeezeDomain]

/-! ## The unique shared backend -/

noncomputable def cshake : Cshake256 :=
  Sp800185Cshake256.controller cshakeAlgorithmId digestCodecPin

noncomputable def merkleDomains : MerkleDomains cshake where
  suiteId := merkleSuiteId
  proofCodecPin := merklePathCodecPin
  proofCodec := merklePathCodec
  leafCustomization := leafCustomization
  nodeCustomization := nodeCustomization
  customizationsDistinct := leaf_node_distinct

noncomputable def transcriptDomains : TranscriptDomains cshake where
  frameCodec := globalFrameCodec
  labelCodec := globalDrawLabelCodec
  absorbDomain := absorbDomain
  squeezeDomain := squeezeDomain
  drawFrameTag := drawFrameTag
  absorb_squeeze_distinct := absorb_squeeze_distinct

noncomputable def backend : Backend BinaryTower256Profile.Tower256 where
  tower := BinaryTower256Profile.profile
  cshake := cshake
  merkle := merkleDomains
  transcript := transcriptDomains

theorem towerExact : backend.tower = BinaryTower256Profile.profile := rfl

theorem cshakeExact : backend.cshake =
    Sp800185Cshake256.controller cshakeAlgorithmId digestCodecPin := rfl

theorem cshakeAlgorithmExact : backend.cshake.algorithmId = cshakeAlgorithmId := rfl

theorem digestCodecPinExact :
    backend.cshake.digestCodecPin = digestCodecPin := rfl

theorem merkleSuiteExact : backend.merkle.suiteId = merkleSuiteId := rfl

theorem merkleCodecPinExact :
    backend.merkle.proofCodecPin = merklePathCodecPin := rfl

theorem merkleCodecExact : backend.merkle.proofCodec = merklePathCodec := rfl

theorem merkleDomainsExact :
    backend.merkle.leafCustomization = leafCustomization ∧
    backend.merkle.nodeCustomization = nodeCustomization := ⟨rfl, rfl⟩

theorem transcriptCodecsExact :
    backend.transcript.frameCodec = globalFrameCodec ∧
    backend.transcript.labelCodec = globalDrawLabelCodec := ⟨rfl, rfl⟩

theorem transcriptDomainsExact :
    backend.transcript.absorbDomain = absorbDomain ∧
    backend.transcript.squeezeDomain = squeezeDomain ∧
    backend.transcript.drawFrameTag = drawFrameTag := ⟨rfl, rfl, rfl⟩

theorem cshakeOutputExact (customization input : List UInt8) :
    backend.cshake.digestCodec.encode
        (backend.cshake.xofDigest customization input) =
      (Sp800185Cshake256.hash customization input).bytes :=
  Sp800185Cshake256.controller_digest_encode_exact
    cshakeAlgorithmId digestCodecPin customization input

/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.decodeNatPrefix_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms StreamCodec.decodeNatPrefix_encode
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.merklePathCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merklePathCodec
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.globalFrameCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms globalFrameCodec
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.globalDrawLabelCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms globalDrawLabelCodec
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.towerExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms towerExact
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.cshakeExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cshakeExact
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.customizationDomains_nodup' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms customizationDomains_nodup
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.cshakeOutputExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cshakeOutputExact

end Minidregg.Compiler.Tower256ConcreteBackend
