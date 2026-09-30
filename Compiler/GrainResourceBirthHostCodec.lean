/-
Canonical source coordinates for the native grain-backed birth draft. This is
input data, never an authority verdict or a proposed post-state. The receiver
recomputes the command, checks both old grain cells, and admits signatures.
-/
import Compiler.GrainResourceBirthController
import Compiler.CanonicalResourcePageMaterializer

namespace Minidregg.Compiler.GrainResourceBirthHostCodec

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel

set_option autoImplicit false

abbrev Source := GrainResourceBirthController.Source
abbrev SourceWire := List UInt8 × List Nat × List Int

def sourceWireStream : StreamCodec SourceWire :=
  StreamCodec.product bytesStream
    (StreamCodec.product (StreamCodec.list StreamCodec.nat)
      (StreamCodec.list IntStream.intStream))

def sourceFrame : List UInt8 :=
  "DREGG/GRAIN-RESOURCE-BIRTH/HOST-SOURCE/v1".toUTF8.toList

def toWire (source : Source) : SourceWire :=
  ((ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode source.birth,
    [source.authorityRoot.value, source.toolTask, source.toolCapability.value,
      source.toolObserveCapability.value, source.toolRoot.value,
      source.parentTask, source.parentCapability.value,
      source.parentObserveCapability.value, source.parentRoot.value],
    source.toolBefore.values ++ source.parentBefore.values)

def fromWire : SourceWire → Option Source
  | (birthBytes, [authorityRoot, toolTask, toolCapability, toolObserveCapability,
      toolRoot, parentTask, parentCapability, parentObserveCapability, parentRoot],
      [toolGeneration, toolStatus, toolRemaining, toolReserved,
        parentGeneration, parentStatus, parentRemaining, parentReserved]) => do
      let birth ← (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).decode birthBytes
      some {
        birth := birth, authorityRoot := ⟨authorityRoot⟩,
        toolTask := toolTask, toolCapability := ⟨toolCapability⟩,
        toolObserveCapability := ⟨toolObserveCapability⟩, toolRoot := ⟨toolRoot⟩,
        toolBefore := ⟨toolGeneration, toolStatus, toolRemaining, toolReserved⟩,
        parentTask := parentTask, parentCapability := ⟨parentCapability⟩,
        parentObserveCapability := ⟨parentObserveCapability⟩,
        parentRoot := ⟨parentRoot⟩,
        parentBefore := ⟨parentGeneration, parentStatus, parentRemaining, parentReserved⟩ }
  | _ => none

theorem fromWire_toWire (source : Source) : fromWire (toWire source) = some source := by
  cases source with
  | mk birth authorityRoot toolTask toolCapability toolObserveCapability toolRoot toolBefore
      parentTask parentCapability parentObserveCapability parentRoot parentBefore =>
      have decoded := (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).decode_encode birth
      cases toolBefore
      cases parentBefore
      simp [fromWire, toWire, Kernel.AgentGrain.State.values,
        decoded]

def rawCodec : LawfulCodec Source where
  encode source := sourceFrame ++ sourceWireStream.encode (toWire source)
  decode bytes := if bytes.take sourceFrame.length = sourceFrame then do
    let wire ← sourceWireStream.toLawful.decode (bytes.drop sourceFrame.length)
    fromWire wire
    else none
  decode_encode := by
    intro source
    simp
    have decoded : sourceWireStream.toLawful.decode
        (sourceWireStream.encode (toWire source)) = some (toWire source) :=
      sourceWireStream.toLawful.decode_encode _
    rw [decoded]
    exact fromWire_toWire source

def sourceCodec : LawfulCodec Source := ResourceBirthCodec.strictCodec rawCodec

theorem sourceCodec_canonical {bytes : List UInt8} {source : Source}
    (decoded : sourceCodec.decode bytes = some source) :
    sourceCodec.encode source = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCodec decoded

/-- The signing plan retains the finalized canonical source and exactly the
derived command bytes used for its headers. Detached assembly has no access
to operator configuration; the receiver rechecks this command against its
currently pinned tariff before a fresh installation. -/
structure Finalized where
  sourceBytes : List UInt8
  commandBytes : List UInt8
  deriving DecidableEq, Repr

def finalizedStream : StreamCodec Finalized :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun value => (value.sourceBytes, value.commandBytes))
    (fun pair => ⟨pair.1, pair.2⟩)
    (by intro value; cases value; rfl)

def finalizedFrame : List UInt8 :=
  "DREGG/GRAIN-RESOURCE-BIRTH/FINALIZED-DRAFT/v1".toUTF8.toList

def finalizedRawCodec : LawfulCodec Finalized where
  encode value := finalizedFrame ++ finalizedStream.encode value
  decode bytes := if bytes.take finalizedFrame.length = finalizedFrame then
    finalizedStream.toLawful.decode (bytes.drop finalizedFrame.length) else none
  decode_encode := by
    intro value
    have decoded := finalizedStream.toLawful.decode_encode value
    change finalizedStream.toLawful.decode (finalizedStream.encode value) = some value at decoded
    simp [decoded]

def finalizedCodec : LawfulCodec Finalized :=
  ResourceBirthCodec.strictCodec finalizedRawCodec

theorem finalizedCodec_canonical {bytes : List UInt8} {value : Finalized}
    (decoded : finalizedCodec.decode bytes = some value) :
    finalizedCodec.encode value = bytes :=
  ResourceBirthCodec.strictCodec_canonical finalizedRawCodec decoded

end Minidregg.Compiler.GrainResourceBirthHostCodec
