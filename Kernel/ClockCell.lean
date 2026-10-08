/-
# Kernel.ClockCell — the deployment's one clock

One store cell per deployment, at an identifier derived from the deployment
domain (`physicalId`), holding the clock and its fixed step bound:

| namespace | key    | value                 | discipline |
|-----------|--------|-----------------------|------------|
| `clock`   | `Unit` | `Clock {now, slot}`   | RAM        |
| `maxStepSeconds` | `Unit` | positive `Nat` | RAM |

* `now` is unix seconds: the time the last accepted tick asserted.
* `slot` is the last chain slot an observer asserted (0 until a chain observer
  ticks; the host wall-clock ticker carries the current slot forward unchanged).

This is the ONE clock of a deployment.  It is written only by
`ClockTickReceiver`, whose admission requires a genesis-fixed per-tick step
bound and `advances`: `now` strictly increases
and `slot` never decreases (`ClockTickReceiver.clock_monotone`).  Any
authorised observer ticks it: the host wall-clock ticker under the operator's
capability (v1), or PAY's chain observer.  The pay cell does not keep a second
clock.

Every resource-invocation law reads it: `slots` projects `clock/now`,
`clock/day` (`now / 86400`) and `clock/slot` into the law's state
(`DeclaredResourceController.now_slot_exact`).

Wire: `DREGG/CLOCK/v2`, with immutable `maxStepSeconds : Nat` at its own namespace.
The old clock cell shape refuses; re-genesis seeds `now` from explicit params.
-/
import Compiler.StoreCodec
import Theory.AxiomPin

namespace Minidregg.Kernel.ClockCell

open Minidregg.Compiler
open Minidregg.Compiler.StoreCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Store
open Minidregg.Theory.CellState (Materializer Materialized materialize)
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

inductive Namespace
  | clock | maxStepSeconds
  deriving DecidableEq, Repr

/-- The deployment clock: unix seconds and the last observed chain slot. -/
structure Clock where
  now : Nat
  slot : Nat
  deriving DecidableEq, Repr

def Namespace.Key : Namespace → Type
  | .clock => Unit
  | .maxStepSeconds => Unit

def Namespace.Value : Namespace → Type
  | .clock => Clock
  | .maxStepSeconds => Nat

instance Namespace.keyDecEq : (space : Namespace) → DecidableEq (Namespace.Key space)
  | .clock => inferInstanceAs (DecidableEq Unit)
  | .maxStepSeconds => inferInstanceAs (DecidableEq Unit)

instance Namespace.valueDecEq : (space : Namespace) → DecidableEq (Namespace.Value space)
  | .clock => inferInstanceAs (DecidableEq Clock)
  | .maxStepSeconds => inferInstanceAs (DecidableEq Nat)

def Namespace.discipline : Namespace → Discipline
  | .clock => .ram
  | .maxStepSeconds => .ram

abbrev layout : Layout.{0, 0, 0} where
  Namespace := Namespace
  Key := Namespace.Key
  Value := Namespace.Value
  discipline := Namespace.discipline

abbrev ClockStore := Store layout

def clockAddress : Address layout := ⟨.clock, ()⟩

def maxStepAddress : Address layout := ⟨.maxStepSeconds, ()⟩

def maxStepOf (store : ClockStore) : Option Nat := store maxStepAddress

def clockOf (store : ClockStore) : Option Clock := store clockAddress

/-- A clock cell always holds a clock.  The identity half of the law is the
registry's (`CanonicalCellRegistry.LogicalLaw`). -/
def Law (store : ClockStore) : Prop := (clockOf store).isSome = true

instance (store : ClockStore) : Decidable (Law store) := by
  unfold Law
  infer_instance

/-! ## The one rule of time -/

/-- A tick `next` may follow the clock `current` exactly when time strictly
advances and the chain slot does not go back. -/
def advances (current next : Clock) : Bool :=
  decide (current.now < next.now) && decide (current.slot ≤ next.slot)

theorem advances_iff (current next : Clock) :
    advances current next = true ↔ current.now < next.now ∧ current.slot ≤ next.slot := by
  simp [advances]

/-- The tick patch: one guarded write of the whole clock value, from the exact
current value. -/
def tickPatch (current next : Clock) : Patch layout :=
  [.write .clock () current next]

/-! ## Projection into a law's state -/

def secondsPerDay : Nat := 86400

/-- The slots every resource-invocation law sees.  `clock/now` comes first so
the projection is the first match of its name. -/
def slots (clock : Clock) : List (String × Int) :=
  [("clock/now", Int.ofNat clock.now),
   ("clock/day", Int.ofNat (clock.now / secondsPerDay)),
   ("clock/slot", Int.ofNat clock.slot)]

/-! ## Wire `DREGG/CLOCK/v1` -/

def clockStream : StreamCodec Clock :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat StreamCodec.nat)
    (fun clock => (clock.now, clock.slot))
    (fun (now, slot) => ⟨now, slot⟩)
    (by intro clock; cases clock; rfl)

def namespaceStream : StreamCodec Namespace where
  encode
    | .clock => [0]
    | .maxStepSeconds => [1]
  decodePrefix
    | 0 :: suffix => some (.clock, suffix)
    | 1 :: suffix => some (.maxStepSeconds, suffix)
    | _ => none
  decodePrefix_encode := by intro space suffix; cases space <;> rfl

def keyStream : (space : Namespace) → StreamCodec (Namespace.Key space)
  | .clock => unitStream
  | .maxStepSeconds => unitStream

def valueStream : (space : Namespace) → StreamCodec (Namespace.Value space)
  | .clock => clockStream
  | .maxStepSeconds => StreamCodec.nat

def wireName : String := "DREGG/CLOCK/v2"

def wire : Wire layout where
  name := wireName
  namespaces := [.clock, .maxStepSeconds]
  namespaces_complete := by intro space; cases space <;> simp
  namespaceStream := namespaceStream
  keyStream := keyStream
  valueStream := valueStream
  keyCodecId
    | .clock => "unit"
    | .maxStepSeconds => "unit"
  valueCodecId
    | .clock => "DREGG/CLOCK/NOW-SLOT/v1"
    | .maxStepSeconds => "positive-nat/max-step-seconds/v1"

def materializer : Materializer layout Digest := StoreCodec.materializer wire

abbrev Cell := Materialized materializer

theorem cell_roundtrip (store : ClockStore) :
    StoreCodec.decode wire (StoreCodec.encode wire store) = some store :=
  StoreCodec.decode_encode wire store

theorem cell_canonical {bytes : List UInt8} {store : ClockStore}
    (accepted : StoreCodec.decode wire bytes = some store) : StoreCodec.encode wire store = bytes :=
  StoreCodec.decode_reencodes wire accepted

/-! ## Identity and genesis -/

def idCustomization : List UInt8 := "DREGG.CLOCK.CELL.ID/v1".toUTF8.toList

/-- The clock cell's physical identifier in deployment `domain`. -/
def physicalId (domain : Digest) : Nat :=
  (Sp800185Cshake256.hash idCustomization (digestStream.encode domain)).digest.value

/-- Zero clock for the pure rule poles; deployed genesis uses explicit params. -/
def genesisClock : Clock := ⟨0, 0⟩

def genesisStore (genesisNow maxStepSeconds : Nat) : ClockStore :=
  ((0 : ClockStore).set clockAddress (some ⟨genesisNow, 0⟩)).set maxStepAddress (some maxStepSeconds)

theorem genesis_law (genesisNow maxStepSeconds : Nat) :
    Law (genesisStore genesisNow maxStepSeconds) := by
  simp [Law, clockOf, genesisStore, maxStepAddress, clockAddress, Store.set] <;> rfl

theorem genesis_clock (genesisNow maxStepSeconds : Nat) :
    clockOf (genesisStore genesisNow maxStepSeconds) = some ⟨genesisNow, 0⟩ := by
  simp [clockOf, genesisStore, maxStepAddress, clockAddress, Store.set] <;> rfl

/-- Refuting pole of the law: an empty clock cell is not lawful. -/
theorem empty_unlawful : ¬ Law (0 : ClockStore) := by decide +kernel

/-- Satisfiable pole of the rule: the first tick after genesis advances. -/
theorem genesis_tick_advances : advances genesisClock ⟨100, 0⟩ = true := by decide

/-- Refuting pole: a tick at the current time does not advance. -/
theorem same_now_not_advancing : advances ⟨100, 0⟩ ⟨100, 0⟩ = false := by decide

/-- Refuting pole: a tick that takes the chain slot back does not advance. -/
theorem slot_back_not_advancing : advances ⟨100, 7⟩ ⟨200, 6⟩ = false := by decide

/-- info: 'Minidregg.Kernel.ClockCell.advances_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms advances_iff
/-- info: 'Minidregg.Kernel.ClockCell.cell_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cell_roundtrip
/-- info: 'Minidregg.Kernel.ClockCell.genesis_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms genesis_law
/-- info: 'Minidregg.Kernel.ClockCell.genesis_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms genesis_clock
/-- info: 'Minidregg.Kernel.ClockCell.empty_unlawful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_unlawful
/-- info: 'Minidregg.Kernel.ClockCell.genesis_tick_advances' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms genesis_tick_advances
/-- info: 'Minidregg.Kernel.ClockCell.same_now_not_advancing' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms same_now_not_advancing
/-- info: 'Minidregg.Kernel.ClockCell.slot_back_not_advancing' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms slot_back_not_advancing

end Minidregg.Kernel.ClockCell
