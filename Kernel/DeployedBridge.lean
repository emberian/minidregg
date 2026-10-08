/-
# Kernel.DeployedBridge -- the deployed `Bridge`: the real cell codec, one wire per kind (T3b)

SURPASS §2(b), stage 0, lane T3b.  T3 defined `Represents` over an abstract
`Bridge` and only named the deployed registry.  This module assembles the
deployed one, so `Represents` is stated over the real codecs:

* `deployedR` -- `CanonicalCellRegistry.Kind` with `CanonicalCellRegistry.layout`.
* `decodeCell` -- the bytes a deployed `DataWrite.canonicalPostBytes` and a
  deployed snapshot's `canonicalBytes` hold: a `ResourceBirthCodec.LifecycleImage`
  under its strict codec.  `fresh` (`[]`) is the absent slot; `live cell` is
  the cell at its registry kind with its logical store; `retired` reads as the
  absent slot AND is the codec's retirement (`retiresCell`): written over a
  present cell it is the World's retire (`TurnOfIntent.Delta.retire`).  Every
  undecodable string is refused (`none`, which `ofIntent` names as
  `Refusal.undecodable c`).
* `wireOf` -- one `StoreCodec.Wire` per kind.  Eight kinds have their deployed
  wire; the three single-address kinds (`resourceBook`, `policySource`,
  `nockProgram`) get a wire here, built from their deployed value streams.  The
  wire fixes the canonical address order of the derived leg (`Codec.ofWires`).
* `bridge := ⟨Codec.ofWires decodeCell wireOf, digestKey, digestKey_injective⟩`.

Proved: `bridge_decode_total_on_registry` (every cell of every registered kind,
and the absent slot, decodes to itself from its canonical bytes),
`decodeCell_canonical` (whatever decodes is the canonical encoding of what it
decoded to, or the retired image), `decodeCell_retired` (a retired image reads
absent and retires), and `deployed_cells_iff`: `Represents`' `cells` field over
this bridge says exactly that every deployed cell's bytes ARE the canonical
encoding of the world's cell, or the retired image over an absent one.  ROM kinds: `policySource_romOnly`, `nockProgram_romOnly` (every store of
those kinds is a legal birth image).
-/
import Kernel.TurnOfIntent
import Compiler.CanonicalCellRegistry
import Theory.AssertAxioms

namespace Minidregg.Kernel.DeployedBridge

open Minidregg.Theory.Store
open Minidregg.Kernel.World
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Compiler.StoreCodec (Wire unitStream)
open Minidregg.Compiler.ResourceBirthCodec (LifecycleImage)

set_option autoImplicit false

/-- The deployed registry as a world registry. -/
def deployedR : Registry where
  Kind := CanonicalCellRegistry.Kind
  layout := CanonicalCellRegistry.layout

/-! ## One wire per kind -/

/-- The Book kind's one namespace. -/
def bookFieldStream : StreamCodec Theory.CanonicalResourceKernel.Field :=
  StreamCodec.xmap unitStream (fun _ => ()) (fun _ => .book) (by intro f; cases f; rfl)

/-- The resource Book: one RAM address holding the Book. -/
def bookWire : Wire Theory.CanonicalResourceKernel.layout where
  name := "dregg/resource-book-address/v1"
  namespaces := [.book]
  namespaces_complete := by intro f; cases f; simp
  namespaceStream := bookFieldStream
  keyStream := fun _ => unitStream
  valueStream := fun _ => CanonicalResourcePageMaterializer.bookStream
  keyCodecId := fun _ => "unit"
  valueCodecId := fun _ => "dregg/book/v2"

/-- The policy source: one ROM address holding the record. -/
def policySourceWire : Wire PolicySourceCell.layout where
  name := "dregg/policy-source-address/v1"
  namespaces := [()]
  namespaces_complete := by intro u; cases u; simp
  namespaceStream := unitStream
  keyStream := fun _ => unitStream
  valueStream := fun _ => PolicySourceCell.recordStream
  keyCodecId := fun _ => "unit"
  valueCodecId := fun _ => "dregg/policy-record/v1"

/-- The Nock program: one ROM address holding the program. -/
def nockProgramWire : Wire NockProgramCodec.layout where
  name := "dregg/nock-program-address/v1"
  namespaces := [()]
  namespaces_complete := by intro u; cases u; simp
  namespaceStream := unitStream
  keyStream := fun _ => unitStream
  valueStream := fun _ => NockProgramCodec.programStream
  keyCodecId := fun _ => "unit"
  valueCodecId := fun _ => "dregg/nock-program/v1"

/-- A kernel activity cell: one RAM address holding its payload. -/
def objectiveActivityWire : Wire Kernel.ObjectiveActivityCell.layout where
  name := "dregg/objective-activity-address/v1"
  namespaces := [()]
  namespaces_complete := by intro u; cases u; simp
  namespaceStream := unitStream
  keyStream := fun _ => unitStream
  valueStream := fun _ => Kernel.ObjectiveActivityCell.payloadStream
  keyCodecId := fun _ => "unit"
  valueCodecId := fun _ => "dregg/objective-activity-cell/v1"

/-- A seat-kernel cell: one RAM address holding its payload. -/
def seatWire : Wire Kernel.SeatCell.layout where
  name := "dregg/seat-address/v1"
  namespaces := [()]
  namespaces_complete := by intro u; cases u; simp
  namespaceStream := unitStream
  keyStream := fun _ => unitStream
  valueStream := fun _ => Kernel.SeatCell.payloadStream
  keyCodecId := fun _ => "unit"
  valueCodecId := fun _ => "dregg/seat-cell/v1"

/-- **One wire per registered kind.** -/
def wireOf : (k : deployedR.Kind) → Wire (deployedR.layout k)
  | .content => HyperdocumentCell.contentWire
  | .eventHistory => HyperdocumentCell.eventWire
  | .authority => CredentialAuthorityCell.wire
  | .declaredObject => DeclaredEffectCell.wire
  | .resourceBook => bookWire
  | .accountMetadata => DeclaredEffectCell.wire
  | .declaredProgram => DeclaredEffectCell.wire
  | .policySource => policySourceWire
  | .pay => Kernel.PayCell.wire
  | .stream => StreamCell.headWire
  | .streamEntry => StreamCell.entryWire
  | .nockProgram => nockProgramWire
  | .clock => Kernel.ClockCell.wire
  | .system => Kernel.SystemCell.wire
  | .worldKind => WorldKindCell.definitionWire
  | .worldInstance => WorldKindCell.instanceWire
  | .objectiveActivity => objectiveActivityWire
  | .seat => seatWire

/-! ## The cell decoder -/

/-- The packed cell of a world cell. -/
def packOf (cell : Cell deployedR) : Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry :=
  ⟨cell.kind, Theory.CellState.materialize (CanonicalCellRegistry.registry.materializer cell.kind)
    cell.store⟩

/-- The world cell of a packed cell. -/
def unpack (cell : Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry) : Cell deployedR :=
  ⟨cell.kind, cell.payload.logical⟩

@[simp] theorem unpack_packOf (cell : Cell deployedR) : unpack (packOf cell) = cell := rfl

@[simp] theorem packOf_unpack (cell : Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry) :
    packOf (unpack cell) = cell := by
  rcases cell with ⟨kind, payload⟩
  unfold packOf unpack
  congr 1

/-- The canonical bytes of a world slot: the lifecycle image. -/
def encodeCell : Option (Cell deployedR) → List UInt8
  | none => LifecycleImage.bytes CanonicalCellRegistry.registry .fresh
  | some cell => LifecycleImage.bytes CanonicalCellRegistry.registry (.live (packOf cell))

/-- **The deployed decoder.** -/
def decodeCell (bytes : List UInt8) : Option (Option (Cell deployedR)) :=
  match (LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
  | some .fresh => some none
  | some (.live cell) => some (some (unpack cell))
  | some .retired => some none
  | none => none

/-- **The deployed retirement**: the registry's retired lifecycle image. -/
def retiresCell (bytes : List UInt8) : Bool :=
  match (LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
  | some .retired => true
  | _ => false

theorem retiresCell_decode (bytes : List UInt8) (retires : retiresCell bytes = true) :
    decodeCell bytes = some none := by
  unfold retiresCell at retires
  unfold decodeCell
  split at retires
  · rename_i decoded; rw [decoded]
  · cases retires

/-- **`bridge_decode_total_on_registry`.**  Every cell of every registered
kind, and the absent slot, decodes to itself from its canonical bytes. -/
theorem bridge_decode_total_on_registry (slot : Option (Cell deployedR)) :
    decodeCell (encodeCell slot) = some slot := by
  cases slot with
  | none =>
      unfold decodeCell encodeCell
      rw [show LifecycleImage.bytes CanonicalCellRegistry.registry .fresh =
        (LifecycleImage.codec CanonicalCellRegistry.registry).encode .fresh from rfl,
        LifecycleImage.decode_encode]
  | some cell =>
      show decodeCell
        ((LifecycleImage.codec CanonicalCellRegistry.registry).encode (.live (packOf cell))) = _
      unfold decodeCell
      rw [LifecycleImage.decode_encode]
      rfl

/-- **Canonicity**: whatever decodes is the canonical encoding of its reading. -/
theorem decodeCell_canonical {bytes : List UInt8} {slot : Option (Cell deployedR)}
    (h : decodeCell bytes = some slot) :
    encodeCell slot = bytes ∨ (slot = none ∧ retiresCell bytes = true) := by
  unfold decodeCell at h
  cases hd : (LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
  | none => rw [hd] at h; cases h
  | some image =>
      rw [hd] at h
      have canonical := LifecycleImage.decode_canonical CanonicalCellRegistry.registry hd
      cases image with
      | fresh =>
          cases h
          exact .inl canonical
      | retired =>
          cases h
          exact .inr ⟨rfl, by simp [retiresCell, hd]⟩
      | live cell =>
          cases h
          simp only [encodeCell, packOf_unpack]
          exact .inl canonical

/-- A retired image reads as the absent slot, and is the retirement. -/
theorem decodeCell_retired :
    decodeCell (LifecycleImage.bytes CanonicalCellRegistry.registry .retired) = some none ∧
      retiresCell (LifecycleImage.bytes CanonicalCellRegistry.registry .retired) = true := by
  rw [show LifecycleImage.bytes CanonicalCellRegistry.registry .retired =
    (LifecycleImage.codec CanonicalCellRegistry.registry).encode .retired from rfl]
  unfold decodeCell retiresCell
  rw [LifecycleImage.decode_encode]
  exact ⟨rfl, rfl⟩

/-! ## The bridge -/

/-- The deployed cell codec: the decoder and the canonical address order of
each kind's wire. -/
def codec : Codec deployedR := Codec.ofWires decodeCell retiresCell retiresCell_decode wireOf

/-- **The deployed `Bridge`**: the real cell codec and the injective nullifier
key. -/
def bridge : Bridge deployedR Theory.TypedAuthorization.Digest :=
  ⟨codec, digestKey, digestKey_injective⟩

/-- **`Represents`' cells field over the deployed bridge** is exactly: every
deployed cell's bytes are the canonical encoding of the world's cell, or the
retired image over an absent one. -/
theorem deployed_cells_iff (bytes : Nat → List UInt8) (cells : Nat → Option (Cell deployedR)) :
    (∀ c, bridge.codec.decode (bytes c) = some (cells c)) ↔
      ∀ c, bytes c = encodeCell (cells c) ∨ (cells c = none ∧ retiresCell (bytes c) = true) := by
  constructor
  · intro h c
    rcases decodeCell_canonical (h c) with canonical | retired
    · exact .inl canonical.symm
    · exact .inr retired
  · intro h c
    show decodeCell (bytes c) = _
    rcases h c with canonical | ⟨absent, retired⟩
    · rw [canonical]
      exact bridge_decode_total_on_registry _
    · rw [absent]
      exact retiresCell_decode _ retired

/-- Reading the activity payload after the deployed lifecycle decoder agrees with
reading the protected store. This includes fresh and retired images and all
other registry kinds; no injectivity assumption about cell roots is needed. -/
theorem decodeCell_payload {bytes : List UInt8} {slot : Option (Cell deployedR)}
    (decoded : decodeCell bytes = some slot) :
    (match (LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
      | some (.live ⟨.objectiveActivity, payload⟩) => ObjectiveActivityCell.payloadAt payload.logical
      | _ => none) =
    slot.bind (fun cell => (cell.storeAt .objectiveActivity).bind ObjectiveActivityCell.payloadAt) := by
  unfold decodeCell at decoded
  cases hd : (LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
  | none => simp [hd] at decoded
  | some image =>
    cases image with
    | fresh => simp [hd] at decoded; subst slot; rfl
    | retired => simp [hd] at decoded; subst slot; rfl
    | live cell =>
      simp only [hd, Option.some.injEq] at decoded
      subst slot
      rcases cell with ⟨kind, state⟩
      cases kind <;> simp [unpack, Cell.storeAt]

#assert_axioms decodeCell_payload

/-! ## ROM kinds: every store is a legal birth image -/

theorem policySource_romOnly (s : Store (deployedR.layout .policySource)) : RomOnly s :=
  fun _ _ => rfl

theorem nockProgram_romOnly (s : Store (deployedR.layout .nockProgram)) : RomOnly s :=
  fun _ _ => rfl

/-- The world cell of a policy source holding `record`. -/
def sourceCell (record : CanonicalPolicyAdmission.PolicyRecord) : Cell deployedR :=
  ⟨.policySource, PolicySourceCell.stateOfOption (some record)⟩

/-- The source cell a deployed birth or install writes
(`CanonicalCellRegistry.policySourceCell`) is the packed form of `sourceCell`. -/
theorem packOf_sourceCell (record : CanonicalPolicyAdmission.PolicyRecord) :
    packOf (sourceCell record) = CanonicalCellRegistry.policySourceCell record := rfl

/-- And its canonical bytes decode to it. -/
theorem decodeCell_policySource (record : CanonicalPolicyAdmission.PolicyRecord) :
    decodeCell (LifecycleImage.bytes CanonicalCellRegistry.registry
        (.live (CanonicalCellRegistry.policySourceCell record))) =
      some (some (sourceCell record)) := by
  rw [← packOf_sourceCell]
  exact bridge_decode_total_on_registry (some (sourceCell record))

#assert_axioms unpack_packOf
#assert_axioms packOf_unpack
#assert_axioms bridge_decode_total_on_registry
#assert_axioms decodeCell_canonical
#assert_axioms decodeCell_retired
#assert_axioms retiresCell_decode
#assert_axioms deployed_cells_iff
#assert_axioms policySource_romOnly
#assert_axioms nockProgram_romOnly
#assert_axioms packOf_sourceCell
#assert_axioms decodeCell_policySource

/-- info: 'Minidregg.Kernel.DeployedBridge.bridge_decode_total_on_registry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bridge_decode_total_on_registry
/-- info: 'Minidregg.Kernel.DeployedBridge.deployed_cells_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_cells_iff

end Minidregg.Kernel.DeployedBridge
