/-
# Compiler.Tower256FriNativeDeployment -- the Tower256 additive-FRI prover as a native work item

`docs/TOWER256-FRI-PROVER-WORK.md` §1 specifies what native code computes for the succinct
controller and what Lean keeps. This module registers that work in an artifact, as
`EvmStage0NativeDeployment` does for Stage 0:

* work `9104` on the Tower256 carrier, request codec `9011` (`requestStream`, Lean-owned, a
  `LawfulCodec` by `toLawful`) and response codec `9013` (the succinct receipt,
  `Tower256SuccinctReceiptCodec.receiptStream` at the request's shape), kernel tag
  `tower256AdditiveFriProve`;
* `artifact`: `MinidreggV1Artifact.bundle` extended by that pack. Its catalog is
  `[9101, 9104]`. **This is a new artifact identity**; the v1 bundle itself is unchanged
  (`docs/TOWER256-FRI-PROVER-WORK.md` §5 records it);
* `acceptResponse`: a reply has authority only through `checkBytes`, so
  `acceptResponse_iff` is `checkBytes_iff` at the request's statement: accepted bytes decode to
  a receipt that satisfies `SuccinctAccepts` at the deployed commitment scheme.

No Rust kernel exists yet; `NativeGlueGen` names the dispatch function
`tower256_additive_fri_prove_bytes`, and nothing in the v1 generated surface emits it, because
this catalog is not the v1 catalog.
-/
import Compiler.Tower256SuccinctReceiptCodec
import Compiler.ComposableDeploymentManifest

namespace Minidregg.Compiler.Tower256FriNativeDeployment

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Compiler.SemanticArtifactBundle
open Minidregg.Compiler.ComposableDeploymentManifest
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec bytesStream)
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8)
open Minidregg.Compiler.Tower256SuccinctCheck
open Minidregg.Compiler.Tower256SuccinctReceiptCodec
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate)

set_option autoImplicit false

/-! ## The request -/

/-- What Lean sends: the statement bytes, the shape, the basis and offset, the degree schedule
(one bound per level `0..m`) and the input word's coefficients. -/
structure ProveRequest where
  statementBytes : List UInt8
  ell : Nat
  m : Nat
  queryCount : Nat
  beta : List C8
  offset : C8
  degree : List Nat
  inputWord : List C8
deriving DecidableEq

abbrev RequestWire :=
  List UInt8 × Nat × Nat × Nat × List C8 × C8 × List Nat × List C8

def requestStream : StreamCodec ProveRequest :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.list c8Stream) (StreamCodec.product c8Stream
          (StreamCodec.product (StreamCodec.list StreamCodec.nat)
            (StreamCodec.list c8Stream))))))))
    (fun r => (r.statementBytes, r.ell, r.m, r.queryCount, r.beta, r.offset, r.degree,
      r.inputWord))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2.1,
      w.2.2.2.2.2.2.2⟩)
    (by intro r; rfl)
    (by intro w; rfl)

/-- **The request codec**, lawful. -/
def requestCodecLawful : LawfulCodec ProveRequest := requestStream.toLawful

theorem request_decode_encode (r : ProveRequest) :
    requestCodecLawful.decode (requestCodecLawful.encode r) = some r :=
  requestCodecLawful.decode_encode r

/-! ## The work profile -/

def requestCodec : ByteCodecProfile where
  registry := .nativeAbi
  codecId := 9011
  valueTypeId := 9012
  version := 1
  shape := .tower256FriProveRequestStream

def responseCodec : ByteCodecProfile where
  registry := .nativeAbi
  codecId := 9013
  valueTypeId := 9014
  version := 1
  shape := .tower256SuccinctReceiptStream

/-- Work `9104`: the Tower256 additive-FRI honest prover on the Tower256 carrier. -/
def workProfile : WorkProfile where
  workId := 9104
  carrierProfileId := MinidreggV1Artifact.gf2Tower256Carrier.id.value
  requestCodec := requestCodec
  responseCodec := responseCodec
  kernel := .tower256AdditiveFriProve

theorem work_profile_pins_exact :
    workProfile.workId = 9104 ∧
    workProfile.carrierProfileId = MinidreggV1Artifact.gf2Tower256Carrier.id.value ∧
    workProfile.requestCodec.codecId = 9011 ∧ workProfile.responseCodec.codecId = 9013 ∧
    workProfile.kernel = .tower256AdditiveFriProve :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The artifact -/

def pack : ImplementedControllerPack.{0, 0, 0, 0} where
  nativeAbiCodecs := [requestCodec, responseCodec]
  nativeWorkCatalog := [workProfile]

/-- The v1 bundle extended by the FRI pack: catalog order `[9101, 9104]`. -/
def artifact : ArtifactBundle :=
  pack.extendArtifact MinidreggV1Artifact.bundle

theorem artifact_nativeWorkCatalog :
    artifact.nativeWorkCatalog = [MinidreggV1Artifact.tower256DotProductWork, workProfile] := by
  rfl

theorem artifact_nativeAbiCodecs :
    artifact.nativeAbiCodecs =
      [MinidreggV1Artifact.tower256DotProductRequestCodec, requestCodec, responseCodec] := by
  rfl

/-- The catalog pins `9104` exactly. -/
theorem work_9104_pinned :
    ∀ work ∈ artifact.nativeWorkCatalog, work.workId = 9104 → work = workProfile := by
  rw [artifact_nativeWorkCatalog]
  decide

/-- **Falsifier at the catalog**: nothing answers to an unregistered work id; in particular
Stage 0's `9103` is not in this artifact. -/
theorem work_9103_absent : ∀ work ∈ artifact.nativeWorkCatalog, work.workId ≠ 9103 := by
  rw [artifact_nativeWorkCatalog]
  decide

/-- The extension changes the catalog: the v1 bundle does not contain the FRI work. -/
theorem v1_lacks_work : workProfile ∉ MinidreggV1Artifact.bundle.nativeWorkCatalog := by
  decide

theorem artifact_manifest : artifact.manifest = MinidreggV1Artifact.bundle.manifest := by
  rfl

theorem artifact_nativeCatalogWellFormed :
    NativeCatalogWellFormed artifact.manifest artifact.nativeAbiCodecs
      artifact.nativeWorkCatalog := by
  rw [artifact_manifest, artifact_nativeAbiCodecs, artifact_nativeWorkCatalog]
  constructor
  · decide
  · decide
  · intro codec member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro codec member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro work member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨MinidreggV1Artifact.gf2Tower256Carrier, by decide⟩
  · intro work member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · show lookupNativeAbiCodec _ 9001 = some MinidreggV1Artifact.tower256DotProductRequestCodec
      decide
    · show lookupNativeAbiCodec _ 9011 = some requestCodec
      decide
  · intro work member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · show MinidreggV1Artifact.bundle.manifest.lookupCodec
          MinidreggV1Artifact.tower256ValueCodec.codecId = some MinidreggV1Artifact.tower256ValueCodec
      decide
    · show lookupNativeAbiCodec _ 9013 = some responseCodec
      decide

/-! ## The reply's only route to authority -/

/-- Decode the reply as a receipt at the statement's shape and decide it. -/
def acceptResponse {ell m queryCount : Nat} (s : CStatement ell m)
    (pins : Tower256AdditiveFriController.TranscriptPins) (bytes : List UInt8) : Bool :=
  checkBytes (queryCount := queryCount) s pins bytes

theorem acceptResponse_iff {ell m queryCount : Nat} (s : CStatement ell m)
    (pins : Tower256AdditiveFriController.TranscriptPins) (bytes : List UInt8) :
    acceptResponse (queryCount := queryCount) s pins bytes = true ↔
      ∃ r, (receiptCodec ell m queryCount).decode bytes = some r ∧
        Tower256AdditiveFriSuccinctController.SuccinctAccepts
          (Tower256AdditiveFriRawDeployment.rawPcs ell) s.denote pins (r.denote s) :=
  checkBytes_iff s pins bytes

/-! ## Teeth -/

/-- The honest one-fold receipt's statement as a request. -/
def honestRequest : ProveRequest where
  statementBytes := Tower256AdditiveFriRawDeployment.bootstrapPins.statementBytes
  ell := 2
  m := 1
  queryCount := 2
  beta := [Coordinate.one 8, Tower256SuccinctHonestRun.gen]
  offset := Coordinate.zero 8
  degree := [2, 2]
  inputWord := []

#guard requestCodecLawful.decode (requestCodecLawful.encode honestRequest) ==
  (some honestRequest : Option ProveRequest)
#guard requestCodecLawful.decode (requestCodecLawful.encode honestRequest ++ [0]) ==
  (none : Option ProveRequest)

/-- info: 'Minidregg.Compiler.Tower256FriNativeDeployment.artifact_nativeCatalogWellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms artifact_nativeCatalogWellFormed
/-- info: 'Minidregg.Compiler.Tower256FriNativeDeployment.acceptResponse_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms acceptResponse_iff

end Minidregg.Compiler.Tower256FriNativeDeployment
