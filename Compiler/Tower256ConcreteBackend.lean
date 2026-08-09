/-
# Compiler.Tower256ConcreteBackend -- one shared concrete binary backend

This module owns the single concrete `Backend (binaryTower 8)` intended for
Tower256 LogUp and additive PCS constructions.  It combines:

* the exact recursive Fan--Paar semantic field profile;
* the Lean-owned SP 800-185 cSHAKE256 computation;
* compact, prefix-decodable codecs for Merkle paths and transcript values;
* fixed readable leaf/node/absorb/draw customization strings;
* stable first-order algorithm, suite, codec, and value-type pins.

Consumers should depend on `backend`, `towerExact`, and `cshakeExact` instead
of rebuilding local copies.  Per-column IDs and proof-suite binding premises
remain consumer data.  This file proves functional codec and projection facts,
not collision resistance, a random-oracle theorem, PCS soundness, or any Rust
semantics.
-/

import Compiler.BinaryTower256Profile
import Compiler.Sp800185Cshake256

namespace Minidregg.Compiler.Tower256ConcreteBackend

open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.NativeKernelPlan (WorkKind)
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Compact streaming-codec nucleus -/

/-- A prefix codec consumes exactly one value and returns the unconsumed
suffix.  The append law makes sequential and list composition mechanical. -/
structure StreamCodec (alpha : Type) where
  encode : alpha -> List UInt8
  decodePrefix : List UInt8 -> Option (alpha × List UInt8)
  decodePrefix_encode : forall value suffix,
    decodePrefix (encode value ++ suffix) = some (value, suffix)

namespace StreamCodec

variable {alpha beta : Type}

/-- A prefix codec becomes a lawful top-level codec by requiring full input
consumption. -/
def toLawful (codec : StreamCodec alpha) : LawfulCodec alpha where
  encode := codec.encode
  decode bytes := do
    let (value, suffix) ← codec.decodePrefix bytes
    if suffix = [] then some value else none
  decode_encode := by
    intro value
    have hdecode := codec.decodePrefix_encode value []
    simp only [List.append_nil] at hdecode
    simp [hdecode]

/-- Change only the value view of a stream codec. -/
def xmap (codec : StreamCodec alpha) (toWire : beta -> alpha)
    (fromWire : alpha -> beta) (roundtrip : forall value, fromWire (toWire value) = value) :
    StreamCodec beta where
  encode value := codec.encode (toWire value)
  decodePrefix bytes := do
    let (wire, suffix) ← codec.decodePrefix bytes
    some (fromWire wire, suffix)
  decodePrefix_encode := by
    intro value suffix
    simp [codec.decodePrefix_encode, roundtrip]

/-- Sequential product; no delimiter is needed because both sides are prefix
decodable. -/
def product (left : StreamCodec alpha) (right : StreamCodec beta) :
    StreamCodec (alpha × beta) where
  encode value := left.encode value.1 ++ right.encode value.2
  decodePrefix bytes := do
    let (first, afterFirst) ← left.decodePrefix bytes
    let (second, suffix) ← right.decodePrefix afterFirst
    some ((first, second), suffix)
  decodePrefix_encode := by
    intro value suffix
    simp [List.append_assoc, left.decodePrefix_encode,
      right.decodePrefix_encode]

/-- Prefix-free binary sum. -/
def sum (left : StreamCodec alpha) (right : StreamCodec beta) :
    StreamCodec (Sum alpha beta) where
  encode
    | .inl value => 0 :: left.encode value
    | .inr value => 1 :: right.encode value
  decodePrefix
    | 0 :: bytes => do
        let (value, suffix) ← left.decodePrefix bytes
        some (.inl value, suffix)
    | 1 :: bytes => do
        let (value, suffix) ← right.decodePrefix bytes
        some (.inr value, suffix)
    | _ => none
  decodePrefix_encode := by
    intro value suffix
    cases value with
    | inl value => simp [left.decodePrefix_encode]
    | inr value => simp [right.decodePrefix_encode]

def byte : StreamCodec UInt8 where
  encode value := [value]
  decodePrefix
    | [] => none
    | value :: suffix => some (value, suffix)
  decodePrefix_encode := by intro value suffix; rfl

/-! ### Compact naturals and finite sequences

Naturals are base-255 little-endian digits followed by byte `255`.  Payload
digits therefore cannot be mistaken for the terminator, and size is
logarithmic rather than unary. -/

def natDigits (value : Nat) : List UInt8 :=
  (Nat.digits 255 value).map UInt8.ofNat

def encodeNat (value : Nat) : List UInt8 := natDigits value ++ [255]

def decodeNatPrefix : List UInt8 -> Option (Nat × List UInt8)
  | [] => none
  | byte :: bytes =>
      if byte = 255 then some (0, bytes)
      else do
        let (higher, suffix) ← decodeNatPrefix bytes
        some (byte.toNat + 255 * higher, suffix)

private theorem decodeNatPrefix_digits (digits : List Nat)
    (ranged : ∀ digit ∈ digits, digit < 255) (suffix : List UInt8) :
    decodeNatPrefix (digits.map UInt8.ofNat ++ 255 :: suffix) =
      some (Nat.ofDigits 255 digits, suffix) := by
  induction digits with
  | nil => simp [decodeNatPrefix, Nat.ofDigits]
  | cons digit digits ih =>
      have hdigit : digit < 255 := ranged digit (by simp)
      have hdigit256 : digit < 256 := lt_trans hdigit (by decide)
      have htail : ∀ candidate ∈ digits, candidate < 255 := by
        intro candidate member
        exact ranged candidate (by simp [member])
      have hne : UInt8.ofNat digit ≠ 255 := by
        intro equal
        have := congrArg UInt8.toNat equal
        have h255 : UInt8.toNat (255 : UInt8) = 255 :=
          UInt8.toNat_ofNat_of_lt (by decide)
        simp only [UInt8.toNat_ofNat'] at this
        rw [Nat.mod_eq_of_lt hdigit256, h255] at this
        omega
      simp only [List.map_cons, List.cons_append, decodeNatPrefix, hne, if_false]
      rw [ih htail]
      simp [Nat.ofDigits, UInt8.toNat_ofNat',
        Nat.mod_eq_of_lt hdigit256]

theorem decodeNatPrefix_encode (value : Nat) (suffix : List UInt8) :
    decodeNatPrefix (encodeNat value ++ suffix) = some (value, suffix) := by
  unfold encodeNat natDigits
  rw [List.append_assoc]
  simpa [Nat.ofDigits_digits] using
    decodeNatPrefix_digits (Nat.digits 255 value)
      (fun digit member => Nat.digits_lt_base (by decide) member) suffix

def nat : StreamCodec Nat where
  encode := encodeNat
  decodePrefix := decodeNatPrefix
  decodePrefix_encode := decodeNatPrefix_encode

def encodeMany (codec : StreamCodec alpha) : List alpha -> List UInt8
  | [] => []
  | value :: values => codec.encode value ++ encodeMany codec values

def decodeMany (codec : StreamCodec alpha) : Nat -> List UInt8 ->
    Option (List alpha × List UInt8)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
      let (value, afterValue) ← codec.decodePrefix bytes
      let (values, suffix) ← decodeMany codec count afterValue
      some (value :: values, suffix)

theorem decodeMany_encodeMany (codec : StreamCodec alpha)
    (values : List alpha) (suffix : List UInt8) :
    decodeMany codec values.length (encodeMany codec values ++ suffix) =
      some (values, suffix) := by
  induction values with
  | nil => simp [encodeMany, decodeMany]
  | cons value values ih =>
      simp [encodeMany, decodeMany, List.append_assoc,
        codec.decodePrefix_encode, ih]

def list (codec : StreamCodec alpha) : StreamCodec (List alpha) where
  encode values := nat.encode values.length ++ encodeMany codec values
  decodePrefix bytes := do
    let (count, afterCount) ← nat.decodePrefix bytes
    decodeMany codec count afterCount
  decodePrefix_encode := by
    intro values suffix
    simp [List.append_assoc, nat.decodePrefix_encode,
      decodeMany_encodeMany]

end StreamCodec

/-! ## Primitive and controller-record codecs -/

def digestStream : StreamCodec Digest :=
  StreamCodec.xmap StreamCodec.nat (fun digest => digest.value)
    Digest.mk (by intro digest; cases digest; rfl)

def bytesStream : StreamCodec (List UInt8) :=
  StreamCodec.list StreamCodec.byte

def merklePathStream : StreamCodec (List Digest) :=
  StreamCodec.list digestStream

def merklePathCodec : LawfulCodec (List Digest) :=
  merklePathStream.toLawful

def drawRoleStream : StreamCodec DrawRole where
  encode
    | .roundChallenge => [0]
    | .queryChallenge => [1]
  decodePrefix
    | 0 :: suffix => some (.roundChallenge, suffix)
    | 1 :: suffix => some (.queryChallenge, suffix)
    | _ => none
  decodePrefix_encode := by intro value suffix; cases value <;> rfl

def columnRoleStream : StreamCodec ColumnRole where
  encode
    | .semanticTrace => [0]
    | .lookupAddress => [1]
    | .lookupWeight => [2]
    | .lookupTable => [3]
    | .accumulator => [4]
    | .checkpoint => [5]
    | .auxiliary => [6]
  decodePrefix
    | 0 :: suffix => some (.semanticTrace, suffix)
    | 1 :: suffix => some (.lookupAddress, suffix)
    | 2 :: suffix => some (.lookupWeight, suffix)
    | 3 :: suffix => some (.lookupTable, suffix)
    | 4 :: suffix => some (.accumulator, suffix)
    | 5 :: suffix => some (.checkpoint, suffix)
    | 6 :: suffix => some (.auxiliary, suffix)
    | _ => none
  decodePrefix_encode := by intro value suffix; cases value <;> rfl

def reprEqRoleStream : StreamCodec ReprEqRole where
  encode
    | .representationEquality => [0]
    | .sameOpening => [1]
  decodePrefix
    | 0 :: suffix => some (.representationEquality, suffix)
    | 1 :: suffix => some (.sameOpening, suffix)
    | _ => none
  decodePrefix_encode := by intro value suffix; cases value <;> rfl

def workKindStream : StreamCodec WorkKind where
  encode
    | .arithmetic => [0]
    | .hash => [1]
    | .transform => [2]
  decodePrefix
    | 0 :: suffix => some (.arithmetic, suffix)
    | 1 :: suffix => some (.hash, suffix)
    | 2 :: suffix => some (.transform, suffix)
    | _ => none
  decodePrefix_encode := by intro value suffix; cases value <;> rfl

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

#print axioms StreamCodec.decodeNatPrefix_encode
#print axioms merklePathCodec
#print axioms globalFrameCodec
#print axioms globalDrawLabelCodec
#print axioms towerExact
#print axioms cshakeExact
#print axioms customizationDomains_nodup
#print axioms cshakeOutputExact

end Minidregg.Compiler.Tower256ConcreteBackend
