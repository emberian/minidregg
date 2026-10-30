/-
# Kernel.PlatformCellLayout — the deployment's platform cell

One store cell per deployment, at an identifier derived from the deployment domain
(`physicalId`), holding the current platform record (GENESIS-COUPLING L1):

| namespace    | key    | value                         | discipline |
|--------------|--------|-------------------------------|------------|
| `record`     | `Unit` | `Platform` (the current one)  | RAM        |
| `controller` | `Unit` | `SubjectId`, fixed at genesis | RAM        |

The record carries what a birth prices against and what today sits in
`Config.runtimeParameters`: the creation tariff, the grain-birth tariff, the completion
custodian key and the factory template's owner budget and lifetime, under a version.
It is written only by the platform-install family (`Kernel.PlatformCell.Admits`: the
controller's signed install of a valid record of a higher version). The cell holds the
current record only: admission reads the current record alone
(`PlatformCell.decideInstall`), so the history is the log's, not the cell's.

`controller` is the deployment's factory controller, written at genesis from
`NativeHostGenesis.Config.factoryController` and never again (`installPatch` writes the
record alone): the running Host keeps no genesis config, so the one subject an install may
come from is read from the cell it changes.

Wire: `DREGG/PLATFORM/v1`.
-/
module

public import Compiler.StoreCodec
public import Theory.ResourceBirth
public import Theory.AxiomPin

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

namespace Minidregg.Kernel.PlatformCellLayout

open Minidregg.Compiler
open Minidregg.Compiler.StoreCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Store
open Minidregg.Theory.CellState (Materializer Materialized materialize)
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Theory.ResourceBirth (CreationTariff)

set_option autoImplicit false

/-- Registry tag 21 (after 20 seat); schema 91020. -/
def registryTag : UInt8 := 21
def schemaId : Nat := 91020
def wireVersion : Nat := 1

/-- Permission micro-units charged to a previously reserved tool grain for a composite
birth (`NativeHost.GrainBirthTariffPin` is this structure). -/
structure GrainBirthTariffPin where
  base : Nat
  perBirth : Nat
  deriving DecidableEq, Repr

/-- The platform record. -/
structure Platform where
  version : Nat
  creation : CreationTariff
  grainBirth : Option GrainBirthTariffPin
  completionCustodianKey : Option (List UInt8)
  ownerBudget : Nat
  lifetime : Nat
  deriving DecidableEq, Repr

/-- Record validity, the checks `NativeHost.Config.factoryPins` makes of the same fields
today: a grain-birth base is positive (`grainBirthTariffValue`), a custodian key is 32
bytes, and the window is positive. The creation tariff carries no validity today (base 0 is
a lawful free world) and gains none here. -/
def Platform.valid (p : Platform) : Bool :=
  (match p.grainBirth with | some g => decide (0 < g.base) | none => true) &&
  (match p.completionCustodianKey with | some k => decide (k.length = 32) | none => true) &&
  decide (0 < p.lifetime)

/-! ## The store -/

inductive Namespace
  | record | controller
  deriving DecidableEq, Repr

@[reducible] def Namespace.Key : Namespace → Type
  | .record => Unit
  | .controller => Unit

@[reducible] def Namespace.Value : Namespace → Type
  | .record => Platform
  | .controller => SubjectId

instance Namespace.keyDecEq : (space : Namespace) → DecidableEq (Namespace.Key space)
  | .record => inferInstanceAs (DecidableEq Unit)
  | .controller => inferInstanceAs (DecidableEq Unit)

instance Namespace.valueDecEq : (space : Namespace) → DecidableEq (Namespace.Value space)
  | .record => inferInstanceAs (DecidableEq Platform)
  | .controller => inferInstanceAs (DecidableEq SubjectId)

def Namespace.discipline : Namespace → Discipline
  | .record => .ram
  | .controller => .ram

abbrev layout : Layout.{0, 0, 0} where
  Namespace := Namespace
  Key := Namespace.Key
  Value := Namespace.Value
  discipline := Namespace.discipline

abbrev PlatformStore := Store layout

def recordAddress : Address layout := ⟨.record, ()⟩

def recordOf (store : PlatformStore) : Option Platform := store recordAddress

def controllerAddress : Address layout := ⟨.controller, ()⟩

def controllerOf (store : PlatformStore) : Option SubjectId := store controllerAddress

/-- A platform cell holds a valid record and its controller. The identity half of the law
is the registry's (`CanonicalCellRegistry.LogicalLaw`). -/
def lawful (store : PlatformStore) : Bool :=
  (match recordOf store with
   | some p => p.valid
   | none => false) &&
  (controllerOf store).isSome

def Law (store : PlatformStore) : Prop := lawful store = true

instance (store : PlatformStore) : Decidable (Law store) := by
  unfold Law
  infer_instance

/-- The install patch: one guarded write of the whole record, from the exact current one. -/
def installPatch (current next : Platform) : Patch layout :=
  [.write .record () current next]

/-! ## Wire `DREGG/PLATFORM/v1` -/

abbrev PlatformWire :=
  Nat × (Nat × Nat × Nat × Nat × Nat × Nat) × Option (Nat × Nat) × Option (List UInt8) × Nat × Nat

def platformWireStream : StreamCodec PlatformWire :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))
      (StreamCodec.product (StreamCodec.option (StreamCodec.product StreamCodec.nat StreamCodec.nat))
        (StreamCodec.product (StreamCodec.option bytesStream)
          (StreamCodec.product StreamCodec.nat StreamCodec.nat))))

def Platform.toWire (p : Platform) : PlatformWire :=
  (p.version, (p.creation.base, p.creation.perBirth, p.creation.perGrant,
    p.creation.perInitialPayloadByte, p.creation.collector, p.creation.asset),
    p.grainBirth.map (fun g => (g.base, g.perBirth)), p.completionCustodianKey,
    p.ownerBudget, p.lifetime)

def Platform.ofWire (w : PlatformWire) : Platform :=
  let (version, (base, perBirth, perGrant, perByte, collector, asset), grain, key, budget, life) := w
  ⟨version, ⟨base, perBirth, perGrant, perByte, collector, asset⟩,
    grain.map (fun (b, p) => ⟨b, p⟩), key, budget, life⟩

theorem Platform.ofWire_toWire (p : Platform) : Platform.ofWire p.toWire = p := by
  rcases p with ⟨v, ⟨a, b, c, d, e, f⟩, g, k, o, l⟩
  rcases g with _ | ⟨gb, gp⟩ <;> rfl

def platformStream : StreamCodec Platform :=
  StreamCodec.xmap platformWireStream Platform.toWire Platform.ofWire Platform.ofWire_toWire

def subjectStream : StreamCodec SubjectId :=
  StreamCodec.xmap StreamCodec.nat SubjectId.value SubjectId.mk (by intro s; cases s; rfl)

/-- The namespace tag's list codec; `namespaceStream` is it on the cursor. -/
def namespaceListStream : StreamCodec Namespace where
  encode
    | .record => [0]
    | .controller => [1]
  decodePrefix
    | 0 :: suffix => some (.record, suffix)
    | 1 :: suffix => some (.controller, suffix)
    | _ => none
  decodePrefix_encode := by intro space suffix; cases space <;> rfl

def namespaceStream : StreamCodec Namespace :=
  withTagCursor namespaceListStream rfl (by unfold namespaceListStream; one_octet_tag)

def keyStream : (space : Namespace) → StreamCodec (Namespace.Key space)
  | .record => unitStream
  | .controller => unitStream

def valueStream : (space : Namespace) → StreamCodec (Namespace.Value space)
  | .record => platformStream
  | .controller => subjectStream

def wireName : String := "DREGG/PLATFORM/v3"

def wire : Wire layout where
  name := wireName
  namespaces := [.record, .controller]
  namespaces_complete := by intro space; cases space <;> simp
  namespaceStream := namespaceStream
  keyStream := keyStream
  valueStream := valueStream
  keyCodecId
    | .record => "unit"
    | .controller => "unit"
  valueCodecId
    | .record => "DREGG/PLATFORM/RECORD/v3"
    | .controller => "nat/subject-id/v1"

def materializer : Materializer layout Digest := StoreCodec.materializer wire

abbrev Cell := Materialized materializer

theorem cell_roundtrip (store : PlatformStore) :
    StoreCodec.decode wire (StoreCodec.encode wire store) = some store :=
  StoreCodec.decode_encode wire store

theorem cell_canonical {bytes : List UInt8} {store : PlatformStore}
    (accepted : StoreCodec.decode wire bytes = some store) : StoreCodec.encode wire store = bytes :=
  StoreCodec.decode_reencodes wire accepted

/-! ## Identity and genesis -/

def idCustomization : List UInt8 := "DREGG.PLATFORM.CELL.ID/v1".toUTF8.toList

/-- The platform cell's physical identifier in deployment `domain`. -/
def physicalId (domain : Digest) : Nat :=
  (Sp800185Cshake256.hash idCustomization (digestStream.encode domain)).digest.value

/-- The cell born at genesis: the genesis record and the deployment's controller. -/
def genesisStore (controller : SubjectId) (p : Platform) : PlatformStore :=
  ((0 : PlatformStore).set recordAddress (some p)).set controllerAddress (some controller)

@[simp] theorem recordOf_genesisStore (controller : SubjectId) (p : Platform) :
    recordOf (genesisStore controller p) = some p := by
  simp [recordOf, genesisStore, recordAddress, controllerAddress, Store.set]

@[simp] theorem controllerOf_genesisStore (controller : SubjectId) (p : Platform) :
    controllerOf (genesisStore controller p) = some controller := by
  simp [controllerOf, genesisStore, controllerAddress, Store.set]

theorem law_iff (store : PlatformStore) :
    Law store ↔ (∃ p, recordOf store = some p ∧ p.valid = true) ∧ (controllerOf store).isSome := by
  unfold Law lawful
  cases recordOf store <;> simp

/-- Satisfiable pole: the genesis cell of a valid record is lawful. -/
theorem genesisStore_law (controller : SubjectId) (p : Platform) (valid : p.valid = true) :
    Law (genesisStore controller p) :=
  (law_iff _).mpr ⟨⟨p, recordOf_genesisStore controller p, valid⟩, by simp⟩

/-- Refuting pole: an empty platform cell is not lawful. -/
theorem empty_unlawful : ¬ Law (0 : PlatformStore) := by
  rw [law_iff]; rintro ⟨⟨p, found, _⟩, _⟩; cases found

/-- Refuting pole: a cell holding an invalid record (a zero-length window) is not lawful. -/
theorem invalid_unlawful (controller : SubjectId) (p : Platform) (invalid : p.valid = false) :
    ¬ Law (genesisStore controller p) := by
  rw [law_iff]; rintro ⟨⟨q, found, valid⟩, _⟩
  rw [recordOf_genesisStore] at found; cases found; simp_all

/-- An install leaves the controller where genesis put it: `installPatch` writes the record
alone. -/
theorem installPatch_record_only (current next : Platform) (op : Op layout)
    (member : op ∈ installPatch current next) : op.address = recordAddress := by
  simp [installPatch] at member; subst member; rfl

/-- An install moves the record to `next` and leaves the controller untouched. -/
theorem controllerOf_installPatch (store : PlatformStore) (current next : Platform) :
    controllerOf (Patch.run store (installPatch current next)) = controllerOf store := by
  simp [installPatch, Patch.run, Op.apply, controllerOf, recordAddress, controllerAddress, Store.set]

theorem recordOf_installPatch (store : PlatformStore) (current next : Platform) :
    recordOf (Patch.run store (installPatch current next)) = some next := by
  simp [installPatch, Patch.run, Op.apply, recordOf, recordAddress, Store.set]

/-- **The cell's writers.** A platform cell is born at genesis holding the deployment's
controller and is written afterwards only by installs: the kind is kernelOnly with the one
writer `.platformInstall` (`CanonicalCellRegistry.platform_only_install`), whose one write is
`installPatch` (`PlatformInstallReceiver.intent_writes_platform_cell`). Any install is allowed
here, admitted or not, so the invariant below holds of every cell those writers can make. -/
inductive Reachable (controller : SubjectId) : PlatformStore → Prop
  | genesis (p : Platform) : Reachable controller (genesisStore controller p)
  | install {store : PlatformStore} (current next : Platform) (prior : Reachable controller store) :
      Reachable controller (Patch.run store (installPatch current next))

/-- **The controller stays genesis's** on every cell its writers can make. -/
theorem Reachable.controller_stays {controller : SubjectId} {store : PlatformStore}
    (reach : Reachable controller store) : controllerOf store = some controller := by
  induction reach with
  | genesis p => exact controllerOf_genesisStore controller p
  | install current next _ stays => rw [controllerOf_installPatch]; exact stays

#assert_axioms Platform.ofWire_toWire
#assert_axioms cell_roundtrip
#assert_axioms recordOf_genesisStore
#assert_axioms controllerOf_genesisStore
#assert_axioms law_iff
#assert_axioms genesisStore_law
#assert_axioms empty_unlawful
#assert_axioms invalid_unlawful
#assert_axioms installPatch_record_only
#assert_axioms controllerOf_installPatch
#assert_axioms recordOf_installPatch
#assert_axioms Reachable.controller_stays

end Minidregg.Kernel.PlatformCellLayout
