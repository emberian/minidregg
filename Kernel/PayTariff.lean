/-
# Kernel.PayTariff — the payment rail's tariff, as data

The rail converts an observed token transfer into Book credit at a rate the
operator sets without code: a versioned value in the pay cell (`PayCell`),
written by the operator's control capability (`PayBookReceiver`).  The
precedents are `ProviderMetering.Tariff` (an operator-controlled tariff
identity, not a price feed) and `ResourceBirth.CreationTariff` (a genesis pin).

`creditFor` caps what one observation can mint: the cap bounds the observer,
not the payer (`creditFor_le_cap`).

A tariff is `valid` only when it names a real token: a positive version, a
32-byte mint and token program that are not the all-zero key (the Solana
System Program, which is no mint), positive rate and cap, and a positive node
membership rate.

Version 2 (`DREGG/PAY/TARIFF/v2`, PAY §11) adds self-enrollment:
`nodeHourRate` (Book credit per hour of node membership; a node week is
`168 · nodeHourRate`), `enrolIndex` (the book index whose observations go to
the enrollment receiver; `none` = self-enrollment off) and `journalFloor`
(atomic units below which an enrollment-index transfer is not admitted at
all, so dust cannot buy a journal row).  A v1 tariff's bytes refuse to decode.  The genesis
default (`genesisDefault`) is deliberately invalid until the operator sets a
tariff; while it is invalid, no deposit index is assigned
(`PayAssignmentReceiver.assignment_requires_valid_tariff`).
-/
import Compiler.ResourceBirthCodec
import Kernel.AssertAxioms

namespace Minidregg.Kernel.PayTariff

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram (LawfulCodec)

set_option autoImplicit false

/-- Decisions of the pay receivers are `Except` values; their concrete poles
are decided by the kernel, which needs equality of `Except` to be decidable. -/
instance exceptDecidableEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok left, .ok right =>
      if same : left = right then isTrue (same ▸ rfl)
      else isFalse (fun equal => same (by cases equal; rfl))
  | .error left, .error right =>
      if same : left = right then isTrue (same ▸ rfl)
      else isFalse (fun equal => same (by cases equal; rfl))
  | .ok _, .error _ => isFalse (fun equal => by cases equal)
  | .error _, .ok _ => isFalse (fun equal => by cases equal)

/-- A 32-byte chain key (address, mint or program), as raw bytes. -/
abbrev Address32 := List UInt8

/-- The all-zero key.  On Solana it is the System Program, never a mint. -/
def zeroKey : Address32 := List.replicate 32 0

structure Tariff where
  version : Nat
  /-- The Book asset credited (asset 0 = the deployment's fee asset). -/
  asset : Nat
  mint : Address32
  tokenProgram : Address32
  decimals : Nat
  creditPerAtomic : Nat
  /-- Atomic units one observation may credit at most. -/
  maxPerObservation : Nat
  /-- Heartbeat rate limit, in chain slots. -/
  minTickSlots : Nat
  /-- Book credit per hour of node membership (PAY §11.8: 5 952 380). -/
  nodeHourRate : Nat
  /-- The self-enrollment book index; `none` turns self-enrollment off. -/
  enrolIndex : Option Nat
  /-- Enrollment-index transfers below this many atomic units are refused. -/
  journalFloor : Nat
  deriving DecidableEq, Repr

def Tariff.valid (t : Tariff) : Prop :=
  0 < t.version ∧ t.mint.length = 32 ∧ t.tokenProgram.length = 32 ∧
    t.mint ≠ zeroKey ∧ t.tokenProgram ≠ zeroKey ∧
    0 < t.creditPerAtomic ∧ 0 < t.maxPerObservation ∧ 0 < t.nodeHourRate

instance (t : Tariff) : Decidable t.valid := by
  unfold Tariff.valid
  infer_instance

/-- The credit one observation of `amount` atomic units mints. -/
def Tariff.creditFor (t : Tariff) (amount : Nat) : Nat :=
  min amount t.maxPerObservation * t.creditPerAtomic

/-- The observation cap: no single observation mints more than the cap. -/
theorem creditFor_le_cap (t : Tariff) (amount : Nat) :
    t.creditFor amount ≤ t.maxPerObservation * t.creditPerAtomic :=
  Nat.mul_le_mul_right _ (Nat.min_le_right _ _)

/-- Satisfiable pole: under a valid tariff every positive transfer mints
positive credit. -/
theorem creditFor_pos (t : Tariff) (valid : t.valid) (amount : Nat) (positive : 0 < amount) :
    0 < t.creditFor amount :=
  Nat.mul_pos (Nat.lt_min.mpr ⟨positive, valid.2.2.2.2.2.2.1⟩) valid.2.2.2.2.2.1

/-- Refuting pole: an empty transfer mints nothing, whatever the tariff. -/
theorem creditFor_zero (t : Tariff) : t.creditFor 0 = 0 := by
  simp [Tariff.creditFor]

/-- Below the cap the rate is exact: `amount * creditPerAtomic`. -/
theorem creditFor_under_cap (t : Tariff) (amount : Nat) (under : amount ≤ t.maxPerObservation) :
    t.creditFor amount = amount * t.creditPerAtomic := by
  simp [Tariff.creditFor, Nat.min_eq_left under]

/-- One node week, in credit: `168 · nodeHourRate`. -/
def Tariff.weekCredit (t : Tariff) : Nat := 168 * t.nodeHourRate

/-! ## Codec `DREGG/PAY/TARIFF/v2` -/

def tariffStream : StreamCodec Tariff :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product StreamCodec.nat
                    (StreamCodec.product StreamCodec.nat
                      (StreamCodec.product (StreamCodec.option StreamCodec.nat)
                        StreamCodec.nat))))))))))
    (fun t => (t.version, t.asset, t.mint, t.tokenProgram, t.decimals, t.creditPerAtomic,
      t.maxPerObservation, t.minTickSlots, t.nodeHourRate, t.enrolIndex, t.journalFloor))
    (fun (version, asset, mint, program, decimals, rate, cap, tick, node, enrol, floor) =>
      ⟨version, asset, mint, program, decimals, rate, cap, tick, node, enrol, floor⟩)
    (by intro t; cases t; rfl)

/-- A frame-prefixed codec that refuses every non-canonical byte string. -/
def framedRaw {α : Type} (frame : List UInt8) (stream : StreamCodec α) : LawfulCodec α :=
  { encode := fun value => frame ++ stream.encode value
    decode := fun bytes => if bytes.take frame.length = frame then
        stream.toLawful.decode (bytes.drop frame.length) else none
    decode_encode := by
      intro value
      have exact := stream.toLawful.decode_encode value
      change stream.toLawful.decode (stream.encode value) = some value at exact
      simp [exact] }

def framed {α : Type} (frame : List UInt8) (stream : StreamCodec α) : LawfulCodec α :=
  Minidregg.Compiler.ResourceBirthCodec.strictCodec (framedRaw frame stream)

theorem framed_canonical {α : Type} (frame : List UInt8) (stream : StreamCodec α)
    {bytes : List UInt8} {value : α} (accepted : (framed frame stream).decode bytes = some value) :
    (framed frame stream).encode value = bytes :=
  Minidregg.Compiler.ResourceBirthCodec.strictCodec_canonical (framedRaw frame stream) accepted

def tariffFrame : List UInt8 := "DREGG/PAY/TARIFF/v2".toUTF8.toList

def tariffCodec : LawfulCodec Tariff := framed tariffFrame tariffStream

theorem tariff_roundtrip (t : Tariff) : tariffCodec.decode (tariffCodec.encode t) = some t :=
  tariffCodec.decode_encode t

theorem tariff_canonical {bytes : List UInt8} {t : Tariff}
    (accepted : tariffCodec.decode bytes = some t) : tariffCodec.encode t = bytes :=
  framed_canonical tariffFrame tariffStream accepted

/-! ## The genesis placeholder -/

/-- Installed at genesis: asset 0, 6 decimals, rate 1, cap 10⁴ tokens,
heartbeat 1500 slots, node rate 5 952 380 credit/hour (PAY §11.8),
self-enrollment off, journal floor 1 token, and a zeroed mint and program.
Invalid until the operator sets the real token (`genesisDefault_invalid`). -/
def genesisDefault : Tariff where
  version := 0
  asset := 0
  mint := zeroKey
  tokenProgram := zeroKey
  decimals := 6
  creditPerAtomic := 1
  maxPerObservation := 10000000000
  minTickSlots := 1500
  nodeHourRate := 5952380
  enrolIndex := none
  journalFloor := 1000000

theorem genesisDefault_invalid : ¬ genesisDefault.valid := by decide

/-- A version-1 tariff naming a (fixture) mint and program: the tariff the
probes and the concrete theorem poles set.  Self-enrollment is off. -/
def exampleTariff : Tariff :=
  ⟨1, 0, List.replicate 32 7, List.replicate 32 9, 6, 1, 10000000000, 1500, 5952380, none,
    1000000⟩

/-- Refuting pole of the node rate: a tariff with a zero node rate is invalid. -/
theorem zero_node_rate_invalid : ¬ { exampleTariff with nodeHourRate := 0 }.valid := by decide

/-- A tariff with a named (non-zero) mint and program is valid: the
satisfiable pole of `Tariff.valid`. -/
theorem named_tariff_valid : exampleTariff.valid := by decide

#assert_axioms creditFor_le_cap
#assert_axioms creditFor_pos
#assert_axioms creditFor_zero
#assert_axioms creditFor_under_cap
#assert_axioms tariff_roundtrip
#assert_axioms tariff_canonical
#assert_axioms genesisDefault_invalid
#assert_axioms named_tariff_valid
#assert_axioms zero_node_rate_invalid

end Minidregg.Kernel.PayTariff
