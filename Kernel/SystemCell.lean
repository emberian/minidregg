/-
# Kernel.SystemCell — the deployment's certified height and its tail bound

One store cell per deployment, at an identifier derived from the deployment
domain (`physicalId`), holding one value:

| namespace | key    | value                                         | discipline |
|-----------|--------|-----------------------------------------------|------------|
| `system`  | `Unit` | `System {certifiedHeight, certifiedDigest, tailBound}` | RAM |

* `certifiedHeight` is the height of the last certified head: the number of
  accepted records the last checkpoint vouches for.  Genesis writes 0.
* `certifiedDigest` is that head's log-chain value (C1's log root at that
  height).  Genesis writes the zero digest: height 0 is vouched for by the
  seed identity itself, which pins this cell.
* `tailBound` is `L`, the operator's tariff line: how many heights a node may
  run past its last certified head.  Genesis writes it from the genesis source;
  no receiver changes it.

**The system law** (`law`) is Mina's backpressure moved off the market onto the
node's own checkpoint chain (COMPUTE.md §5.2, §6):

    leSlotsOff head/height certified/height L

over the state `slots`.  It is judged on every non-certify record by the
kernel's durable admission (`Kernel.TailBound`), never by a user law.

The cell is written only by a certify record (`Kernel.CertifyReceiver`), whose
post value is exactly `certifyNext` of the current head and chain
(`TailBound.certified_written_only_by_checkpoint`).

Wire: the store codec with layout name `DREGG/SYSTEM/v1`.
-/
import Compiler.StoreCodec
import Pred.Core

namespace Minidregg.Kernel.SystemCell

open Minidregg.Compiler
open Minidregg.Compiler.StoreCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Store
open Minidregg.Theory.CellState (Materializer Materialized materialize)
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

inductive Namespace
  | system
  deriving DecidableEq, Repr

/-- The deployment's certified head and its tail bound. -/
structure System where
  certifiedHeight : Nat
  certifiedDigest : Digest
  tailBound : Nat
  deriving DecidableEq, Repr

def Namespace.Key : Namespace → Type
  | .system => Unit

def Namespace.Value : Namespace → Type
  | .system => System

instance Namespace.keyDecEq : (space : Namespace) → DecidableEq (Namespace.Key space)
  | .system => inferInstanceAs (DecidableEq Unit)

instance Namespace.valueDecEq : (space : Namespace) → DecidableEq (Namespace.Value space)
  | .system => inferInstanceAs (DecidableEq System)

def Namespace.discipline : Namespace → Discipline
  | .system => .ram

abbrev layout : Layout.{0, 0, 0} where
  Namespace := Namespace
  Key := Namespace.Key
  Value := Namespace.Value
  discipline := Namespace.discipline

abbrev SystemStore := Store layout

def systemAddress : Address layout := ⟨.system, ()⟩

def systemOf (store : SystemStore) : Option System := store systemAddress

/-- A system cell always holds a value.  The identity half of the law is the
registry's (`CanonicalCellRegistry.LogicalLaw`). -/
def Law (store : SystemStore) : Prop := (systemOf store).isSome = true

instance (store : SystemStore) : Decidable (Law store) := by
  unfold Law
  infer_instance

/-! ## Certification -/

/-- The value a certify record installs: the head `height` and its chain value
`chain`; the tail bound is carried unchanged. -/
def certifyNext (current : System) (height : Nat) (chain : Digest) : System :=
  { current with certifiedHeight := height, certifiedDigest := chain }

/-- The certify patch: one guarded write of the whole value, from the exact
current value. -/
def certifyPatch (current next : System) : Patch layout :=
  [.write .system () current next]

/-! ## The system law -/

def headSlot : String := "head/height"
def certifiedSlot : String := "certified/height"

/-- The slots the system law reads: the height of the record being admitted
and the certified height. -/
def slots (system : System) (head : Nat) : List (String × Int) :=
  [(headSlot, Int.ofNat head), (certifiedSlot, Int.ofNat system.certifiedHeight)]

def state (system : System) (head : Nat) : Minidregg.Pred.State := ⟨slots system head⟩

/-- **The system law**: `head/height ≤ certified/height + L`. -/
def law (system : System) : Minidregg.Pred.Pred :=
  .leSlotsOff headSlot certifiedSlot (Int.ofNat system.tailBound)

/-- Whether the system law admits a record at `head`. -/
def admitsHead (system : System) (head : Nat) : Bool :=
  Minidregg.Pred.eval (law system) (state system head) (state system head)

theorem admitsHead_iff (system : System) (head : Nat) :
    admitsHead system head = true ↔ head ≤ system.certifiedHeight + system.tailBound := by
  simp only [admitsHead, law, state, slots, Minidregg.Pred.eval, Minidregg.Pred.evalWith,
    Minidregg.Pred.State.get, headSlot, certifiedSlot]
  simp [List.find?]
  omega

/-! ## Wire `DREGG/SYSTEM/v1` -/

def systemStream : StreamCodec System :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream StreamCodec.nat))
    (fun system => (system.certifiedHeight, system.certifiedDigest, system.tailBound))
    (fun (height, digest, bound) => ⟨height, digest, bound⟩)
    (by intro system; cases system; rfl)

def namespaceStream : StreamCodec Namespace where
  encode
    | .system => [0]
  decodePrefix
    | 0 :: suffix => some (.system, suffix)
    | _ => none
  decodePrefix_encode := by intro space suffix; cases space; rfl

def keyStream : (space : Namespace) → StreamCodec (Namespace.Key space)
  | .system => unitStream

def valueStream : (space : Namespace) → StreamCodec (Namespace.Value space)
  | .system => systemStream

def wireName : String := "DREGG/SYSTEM/v1"

def wire : Wire layout where
  name := wireName
  namespaces := [.system]
  namespaces_complete := by intro space; cases space; simp
  namespaceStream := namespaceStream
  keyStream := keyStream
  valueStream := valueStream
  keyCodecId
    | .system => "unit"
  valueCodecId
    | .system => "DREGG/SYSTEM/CERTIFIED-HEIGHT-DIGEST-TAIL-BOUND/v1"

def materializer : Materializer layout Digest := StoreCodec.materializer wire

abbrev Cell := Materialized materializer

theorem cell_roundtrip (store : SystemStore) :
    StoreCodec.decode wire (StoreCodec.encode wire store) = some store :=
  StoreCodec.decode_encode wire store

/-! ## Identity and genesis -/

def idCustomization : List UInt8 := "DREGG.SYSTEM.CELL.ID/v1".toUTF8.toList

/-- The system cell's physical identifier in deployment `domain`. -/
def physicalId (domain : Digest) : Nat :=
  (Sp800185Cshake256.hash idCustomization (digestStream.encode domain)).digest.value

/-- Genesis: nothing certified beyond the seed, under the operator's bound. -/
def genesisSystem (tailBound : Nat) : System := ⟨0, ⟨0⟩, tailBound⟩

def genesisStore (tailBound : Nat) : SystemStore :=
  (0 : SystemStore).set systemAddress (some (genesisSystem tailBound))

theorem genesis_law (tailBound : Nat) : Law (genesisStore tailBound) := by
  simp [Law, systemOf, genesisStore, systemAddress, Store.set]; rfl

theorem genesis_system (tailBound : Nat) :
    systemOf (genesisStore tailBound) = some (genesisSystem tailBound) := by
  simp [systemOf, genesisStore, systemAddress, Store.set]; rfl

/-- Refuting pole of the law: an empty system cell is not lawful. -/
theorem empty_unlawful : ¬ Law (0 : SystemStore) := by decide +kernel

/-- The default `L`: four checkpoints of 64 heights. -/
def defaultTailBound : Nat := 64 * 4

/-- info: 'Minidregg.Kernel.SystemCell.admitsHead_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitsHead_iff
/-- info: 'Minidregg.Kernel.SystemCell.cell_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cell_roundtrip
/-- info: 'Minidregg.Kernel.SystemCell.genesis_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms genesis_law
/-- info: 'Minidregg.Kernel.SystemCell.genesis_system' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms genesis_system
/-- info: 'Minidregg.Kernel.SystemCell.empty_unlawful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_unlawful

end Minidregg.Kernel.SystemCell
