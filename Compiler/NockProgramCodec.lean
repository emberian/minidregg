/-
# Compiler.NockProgramCodec — the Nock program cell: a jam, its ABI, its identity

A friend's Nock program is a kernel object: one immutable cell holding the
MINIMAL jam bytes of the program noun and the `Abi` the kernel reads to build
the program's sample and decode its writes (NOCK §2.1, §2.3).

* **Code.** `jam` must be exactly `Noun.jam` of the noun it cues to
  (`Noun.canonical`), so a noun has one byte string here (`admissible_jam_unique`,
  from `Theory.Noun.canonical_unique`). hoonc's word-padded file (trailing zero
  bytes) is refused `nonCanonical`. Compiled, `canonical` runs N-MUG's
  `@[csimp]` jam/cue (mug-keyed tables), each proved equal to its specification.
* **Identity.** `codeDigest` is cSHAKE256 over the jam. `programId` is
  cSHAKE256 over the whole `DREGG/NOCK/PROGRAM/v1` record (jam and ABI), and the
  cell id is `physicalId domain programId`. The ABI is in the identity because it
  decides what the kernel feeds the program: with the id over the jam alone, the
  first writer's ABI would be the only one any friend could ever use for that
  code. Two cells with the same jam and different ABIs are two programs.
* **Libraries.** `Abi.libraries` names other program cells by `programId`
  (NOCK N16: the hoon stdlib context rides once, not in every program). Their
  presence is checked against the store at birth (`CanonicalCellRegistry`).
* **Immutability.** The single address is ROM: after birth no patch changes it
  (`program_immutable`), and the registry's final-post law pins its bytes.
-/
import Compiler.PolicyRecordCodec
import Theory.ResourceBirth
import Theory.Noun

namespace Minidregg.Compiler.NockProgramCodec

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.PolicyRecordCodec (stringStream)
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def wireVersion : Nat := 1
def abiVersion : Nat := 1
/-- Tag 11 / schema 91010 are the pay cell's on `p2-pay`; this kind takes the next. -/
def registryTag : UInt8 := 12
def schemaId : Nat := 91011

/-! ## The ABI -/

/-- How a projected slot value (an `Int`) becomes a sample atom. `nat` is the
atom itself and refuses negatives (what every Hoon `@` sample expects); `int` is
`Theory.Noun`'s zigzag `Int.toNoun`. -/
inductive SlotType where
  | nat
  | int
  deriving DecidableEq, Repr

/-- One sample entry: the program sees `[key value]`, where `value` is the
participant slot `slot` of the command's `target`-th target (0-based, the
command's signed target order, K-JOINT's `joint/index/{target}/…`). -/
structure SampleSlot where
  target : Nat
  slot : String
  key : String
  type : SlotType
  deriving DecidableEq, Repr

/-- One write the program may emit: `[key value]` in its output list is a write
of object field `field` on the command's `target`-th target. -/
structure OutputSlot where
  key : String
  target : Nat
  field : Nat
  type : SlotType
  deriving DecidableEq, Repr

structure Abi where
  version : Nat
  /-- The arm slammed: 2 for a bare gate (hoonc's trap kicked to its gate). -/
  arm : Nat
  sample : List SampleSlot
  outputs : List OutputSlot
  /-- Program cells (by `programId`) this program is run against. -/
  libraries : List Digest
  /-- The fuel bound a run is held to (Lean `Theory.Nock.steps`). -/
  fuel : Nat
  deriving DecidableEq, Repr

structure Program where
  jam : List UInt8
  abi : Abi
  deriving DecidableEq, Repr

/-! ## Codecs `DREGG/NOCK/ABI/v1`, `DREGG/NOCK/PROGRAM/v1` -/

def slotTypeStream : StreamCodec SlotType :=
  StreamCodec.xmap StreamCodec.nat (fun | .nat => 0 | .int => 1)
    (fun n => if n = 1 then .int else .nat) (by intro value; cases value <;> rfl)

def sampleSlotStream : StreamCodec SampleSlot :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product stringStream (StreamCodec.product stringStream slotTypeStream)))
    (fun s => (s.target, s.slot, s.key, s.type)) (fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2⟩)
    (by intro value; cases value; rfl)

def outputSlotStream : StreamCodec OutputSlot :=
  StreamCodec.xmap
    (StreamCodec.product stringStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat slotTypeStream)))
    (fun s => (s.key, s.target, s.field, s.type)) (fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2⟩)
    (by intro value; cases value; rfl)

def abiStream : StreamCodec Abi :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.list sampleSlotStream)
          (StreamCodec.product (StreamCodec.list outputSlotStream)
            (StreamCodec.product (StreamCodec.list digestStream) StreamCodec.nat)))))
    (fun a => (a.version, a.arm, a.sample, a.outputs, a.libraries, a.fuel))
    (fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def programStream : StreamCodec Program :=
  StreamCodec.xmap (StreamCodec.product bytesStream abiStream)
    (fun p => (p.jam, p.abi)) (fun v => ⟨v.1, v.2⟩) (by intro value; cases value; rfl)

/-- A frame-tagged stream codec that accepts only its own re-encoding. -/
def framedDecode {α : Type} (frame : List UInt8) (stream : StreamCodec α)
    (bytes : List UInt8) : Option α :=
  if bytes.take frame.length = frame then
    match stream.toLawful.decode (bytes.drop frame.length) with
    | some value => if frame ++ stream.encode value = bytes then some value else none
    | none => none
  else none

theorem framedDecode_encode {α : Type} (frame : List UInt8) (stream : StreamCodec α)
    (value : α) : framedDecode frame stream (frame ++ stream.encode value) = some value := by
  have decoded := stream.toLawful.decode_encode value
  change stream.toLawful.decode (stream.encode value) = some value at decoded
  simp [framedDecode, decoded]

theorem framedDecode_canonical {α : Type} {frame : List UInt8} {stream : StreamCodec α}
    {bytes : List UInt8} {value : α} (accepted : framedDecode frame stream bytes = some value) :
    frame ++ stream.encode value = bytes := by
  unfold framedDecode at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · cases accepted; assumption
      · cases accepted
    · cases accepted
  · cases accepted

def framed {α : Type} (frame : List UInt8) (stream : StreamCodec α) : LawfulCodec α where
  encode value := frame ++ stream.encode value
  decode := framedDecode frame stream
  decode_encode := framedDecode_encode frame stream

/-- `DREGG/NOCK/ABI/v1` -/
def abiFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 78, 79, 67, 75, 47, 65, 66, 73, 47, 118, 49]
/-- `DREGG/NOCK/PROGRAM/v1` -/
def programFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 78, 79, 67, 75, 47, 80, 82, 79, 71, 82, 65, 77, 47, 118, 49]

def abiCodec : LawfulCodec Abi := framed abiFrame abiStream
def programCodec : LawfulCodec Program := framed programFrame programStream

theorem abi_roundtrip (abi : Abi) : abiCodec.decode (abiCodec.encode abi) = some abi :=
  abiCodec.decode_encode abi

theorem abi_canonical {bytes : List UInt8} {abi : Abi}
    (accepted : abiCodec.decode bytes = some abi) : abiCodec.encode abi = bytes :=
  framedDecode_canonical accepted

theorem program_roundtrip (program : Program) :
    programCodec.decode (programCodec.encode program) = some program :=
  programCodec.decode_encode program

theorem program_canonical {bytes : List UInt8} {program : Program}
    (accepted : programCodec.decode bytes = some program) :
    programCodec.encode program = bytes :=
  framedDecode_canonical accepted

theorem programCodec_injective : Function.Injective programCodec.encode := by
  intro left right same
  have decoded := congrArg programCodec.decode same
  rw [program_roundtrip, program_roundtrip] at decoded
  exact Option.some.inj decoded

/-! ## Identity -/

/-- `DREGG.NOCK.CODE/v1` -/
def codeCustomization : List UInt8 :=
  [68, 82, 69, 71, 71, 46, 78, 79, 67, 75, 46, 67, 79, 68, 69, 47, 118, 49]
/-- `DREGG.NOCK.PROGRAM/v1` -/
def programCustomization : List UInt8 :=
  [68, 82, 69, 71, 71, 46, 78, 79, 67, 75, 46, 80, 82, 79, 71, 82, 65, 77, 47, 118, 49]
/-- `DREGG.NOCK.PROGRAM.STATE/v1` -/
def rootCustomization : List UInt8 :=
  [68, 82, 69, 71, 71, 46, 78, 79, 67, 75, 46, 80, 82, 79, 71, 82, 65, 77, 46, 83, 84, 65, 84,
    69, 47, 118, 49]
/-- `DREGG.NOCK.PROGRAM.ID/v1` -/
def idCustomization : List UInt8 :=
  [68, 82, 69, 71, 71, 46, 78, 79, 67, 75, 46, 80, 82, 79, 71, 82, 65, 77, 46, 73, 68, 47, 118, 49]

theorem customizations_distinct :
    [codeCustomization, programCustomization, rootCustomization, idCustomization].Nodup := by
  decide

/-- cSHAKE256 over the minimal jam bytes: what the program IS. -/
def codeDigest (jam : List UInt8) : Digest :=
  (Sp800185Cshake256.hash codeCustomization jam).digest

/-- cSHAKE256 over the program record (jam and ABI): what a run claim names. -/
def programId (program : Program) : Digest :=
  (Sp800185Cshake256.hash programCustomization (programCodec.encode program)).digest

/-- The cell a program lives in, in one deployment. -/
def physicalId (domain id : Digest) : Nat :=
  (Sp800185Cshake256.hash idCustomization
    ((StreamCodec.product digestStream digestStream).encode (domain, id))).digest.value

/-! ## Admissibility at birth -/

/-- Why a program is not admitted. Order is the check order. -/
inductive Refusal where
  | noCue
  | nonCanonical
  | abiVersion
  | fuelZero
  | armZero
  | abiShape
  | missingLibrary
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .noCue => "noCue"
  | .nonCanonical => "nonCanonical"
  | .abiVersion => "abiVersion"
  | .fuelZero => "fuelZero"
  | .armZero => "armZero"
  | .abiShape => "abiShape"
  | .missingLibrary => "missingLibrary"

/-- The key prefix reserved for the target entries of the sample. -/
def targetPrefix : String := "target/"

/-- Keys are unambiguous: sample keys and output keys are each distinct, no
sample key can be mistaken for a target entry, libraries are distinct. -/
def AbiShape (abi : Abi) : Prop :=
  (abi.sample.map SampleSlot.key).Nodup ∧ (abi.outputs.map OutputSlot.key).Nodup ∧
    abi.libraries.Nodup ∧ ∀ slot ∈ abi.sample, targetPrefix.isPrefixOf slot.key = false

instance abiShapeDecidable (abi : Abi) : Decidable (AbiShape abi) := by
  unfold AbiShape; infer_instance

def Admissible (program : Program) : Prop :=
  Noun.canonical program.jam = true ∧ program.abi.version = abiVersion ∧
    0 < program.abi.fuel ∧ 0 < program.abi.arm ∧ AbiShape program.abi

instance admissibleDecidable (program : Program) : Decidable (Admissible program) := by
  unfold Admissible; infer_instance

/-- The store-free birth check, in refusal order. -/
def check (program : Program) : Except Refusal Unit :=
  if (Noun.cue program.jam).isNone then .error .noCue
  else if Noun.canonical program.jam = false then .error .nonCanonical
  else if program.abi.version ≠ abiVersion then .error .abiVersion
  else if program.abi.fuel = 0 then .error .fuelZero
  else if program.abi.arm = 0 then .error .armZero
  else if ¬ AbiShape program.abi then .error .abiShape
  else .ok ()

theorem check_ok_iff (program : Program) : check program = .ok () ↔ Admissible program := by
  unfold check Admissible
  constructor
  · intro accepted
    split at accepted; · cases accepted
    split at accepted; · cases accepted
    split at accepted; · cases accepted
    split at accepted; · cases accepted
    split at accepted; · cases accepted
    split at accepted; · cases accepted
    rename_i _ canonical version fuel arm shape
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa using canonical
    · simpa using version
    · omega
    · omega
    · simpa using shape
  · rintro ⟨canonical, version, fuel, arm, shape⟩
    have cues : (Noun.cue program.jam).isNone = false := by
      obtain ⟨n, hn⟩ := Noun.canonical_iff.mp canonical
      rw [← hn, Noun.cue_jam]; rfl
    simp [cues, canonical, version, Nat.pos_iff_ne_zero.mp fuel, Nat.pos_iff_ne_zero.mp arm, shape]

theorem noCue_refused (program : Program) (bad : Noun.cue program.jam = none) :
    check program = .error .noCue := by
  simp [check, bad]

theorem nonCanonical_refused (program : Program) (cues : (Noun.cue program.jam).isSome)
    (bad : Noun.canonical program.jam = false) : check program = .error .nonCanonical := by
  have : (Noun.cue program.jam).isNone = false := by
    cases h : Noun.cue program.jam <;> simp_all
  simp [check, this, bad]

theorem fuelZero_refused (program : Program) (canonical : Noun.canonical program.jam = true)
    (version : program.abi.version = abiVersion) (zero : program.abi.fuel = 0) :
    check program = .error .fuelZero := by
  have cues : (Noun.cue program.jam).isNone = false := by
    obtain ⟨n, hn⟩ := Noun.canonical_iff.mp canonical
    rw [← hn, Noun.cue_jam]; rfl
  simp [check, cues, canonical, version, zero]

/-- A trailing zero byte (hoonc's word padding) is never admitted: the padded
bytes cue to the same noun as the minimal ones, so at most one of them is
canonical. -/
theorem padded_refused (jam : List UInt8) (canonical : Noun.canonical jam = true)
    (cuePadded : Noun.cue (jam ++ [0]) = Noun.cue jam) :
    Noun.canonical (jam ++ [0]) = false := by
  cases h : Noun.canonical (jam ++ [0])
  · rfl
  · have same := Noun.canonical_unique h canonical cuePadded
    have := congrArg List.length same
    simp at this

/-- An admitted program's bytes are a function of its noun: `programId` and
`codeDigest` are functions of the program (NOCK §2.10), never of an encoding
choice. -/
theorem admissible_jam_unique {left right : Program} (hl : Admissible left)
    (hr : Admissible right) (same : Noun.cue left.jam = Noun.cue right.jam) :
    left.jam = right.jam :=
  Noun.canonical_unique hl.1 hr.1 same

theorem admissible_jam_eq {program : Program} (admitted : Admissible program) {n : Noun}
    (cued : Noun.cue program.jam = some n) : program.jam = Noun.jam n := by
  obtain ⟨m, hm⟩ := Noun.canonical_iff.mp admitted.1
  rw [← hm, Noun.cue_jam] at cued
  cases cued
  exact hm.symm

/-! ## The cell: one ROM address -/

abbrev layout : Store.Layout.{0, 0, 0} where
  Namespace := Unit
  Key := fun _ => Unit
  Value := fun _ => Program
  discipline := fun _ => .rom

def programAddress : Address layout := ⟨(), ()⟩

def stateOfOption : Option Program → Store layout
  | none => 0
  | some program => (0 : Store layout).set programAddress (some program)

def programAt (state : Store layout) : Option Program := state programAddress

@[simp] theorem programAt_stateOfOption (program : Option Program) :
    programAt (stateOfOption program) = program := by
  cases program <;> simp [programAt, stateOfOption]

theorem state_ext (state : Store layout) : state = stateOfOption (programAt state) := by
  apply DFinsupp.ext
  rintro ⟨⟨⟩, ⟨⟩⟩
  cases present : state programAddress with
  | none => simp [programAt, stateOfOption, present]
  | some program => simp [programAt, stateOfOption, present]

/-- No valid patch changes a program cell: the namespace is ROM. -/
theorem program_immutable (state : Store layout) (patch : Patch layout)
    (valid : Patch.ValidFrom state patch) :
    programAt (Patch.run state patch) = programAt state :=
  Patch.rom_preserved state patch programAddress valid rfl

def payloadStream := StreamCodec.product StreamCodec.nat (StreamCodec.option programStream)

/-- `DREGG/NOCK/PROGRAM-CELL` -/
def wireFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 78, 79, 67, 75, 47, 80, 82, 79, 71, 82, 65, 77, 45, 67, 69, 76, 76]

def encode (state : Store layout) : List UInt8 :=
  wireFrame ++ payloadStream.encode (wireVersion, programAt state)

def decodeRaw (bytes : List UInt8) : Option (Store layout) :=
  if bytes.take wireFrame.length = wireFrame then do
    let (version, program) ← payloadStream.toLawful.decode (bytes.drop wireFrame.length)
    if version = wireVersion then some (stateOfOption program) else none
  else none

@[simp] theorem decodeRaw_encode (state : Store layout) :
    decodeRaw (encode state) = some state := by
  have decoded := payloadStream.toLawful.decode_encode (wireVersion, programAt state)
  change payloadStream.toLawful.decode
    (payloadStream.encode (wireVersion, programAt state)) =
      some (wireVersion, programAt state) at decoded
  simp [decodeRaw, encode, decoded, ← state_ext state]

def decode (bytes : List UInt8) : Option (Store layout) := do
  let state ← decodeRaw bytes
  if encode state = bytes then some state else none

@[simp] theorem decode_encode (state : Store layout) : decode (encode state) = some state := by
  simp [decode]

theorem decode_canonical {bytes : List UInt8} {state : Store layout}
    (accepted : decode bytes = some state) : encode state = bytes := by
  unfold decode at accepted
  cases raw : decodeRaw bytes with
  | none => simp [raw] at accepted
  | some selected =>
      simp only [raw, bind, Option.bind] at accepted
      split at accepted
      next canonical =>
        cases Option.some.inj accepted
        exact canonical
      next => contradiction

theorem wrong_version_refused (version : Nat) (program : Option Program)
    (different : version ≠ wireVersion) :
    decode (wireFrame ++ payloadStream.encode (version, program)) = none := by
  have decoded := payloadStream.toLawful.decode_encode (version, program)
  change payloadStream.toLawful.decode (payloadStream.encode (version, program)) =
    some (version, program) at decoded
  simp [decode, decodeRaw, decoded, different]

def stateCodec : LawfulCodec (Store layout) where
  encode := encode
  decode := decode
  decode_encode := decode_encode

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def materializer : Materializer layout Digest where
  codec := stateCodec
  rootBytes := rootBytes

/-- The loaded/final law: the cell sits at its content address. Cheap enough to
run on every load (one hash of the record); canonicality is a birth fact,
carried by ROM and by the id binding the bytes. -/
def CellValid (domain : Digest) (cellId : Nat) (program : Program) : Prop :=
  cellId = physicalId domain (programId program)

instance cellValidDecidable (domain : Digest) (cellId : Nat) (program : Program) :
    Decidable (CellValid domain cellId program) := by
  unfold CellValid; infer_instance

end Minidregg.Compiler.NockProgramCodec
/-- info: 'Minidregg.Compiler.NockProgramCodec.abi_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.abi_roundtrip
/-- info: 'Minidregg.Compiler.NockProgramCodec.abi_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.abi_canonical
/-- info: 'Minidregg.Compiler.NockProgramCodec.program_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.program_roundtrip
/-- info: 'Minidregg.Compiler.NockProgramCodec.program_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.program_canonical
/-- info: 'Minidregg.Compiler.NockProgramCodec.programCodec_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.programCodec_injective
/-- info: 'Minidregg.Compiler.NockProgramCodec.customizations_distinct' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.customizations_distinct
/-- info: 'Minidregg.Compiler.NockProgramCodec.check_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.check_ok_iff
/-- info: 'Minidregg.Compiler.NockProgramCodec.noCue_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.noCue_refused
/-- info: 'Minidregg.Compiler.NockProgramCodec.nonCanonical_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.nonCanonical_refused
/-- info: 'Minidregg.Compiler.NockProgramCodec.fuelZero_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.fuelZero_refused
/-- info: 'Minidregg.Compiler.NockProgramCodec.padded_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.padded_refused
/-- info: 'Minidregg.Compiler.NockProgramCodec.admissible_jam_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.admissible_jam_unique
/-- info: 'Minidregg.Compiler.NockProgramCodec.admissible_jam_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.admissible_jam_eq
/-- info: 'Minidregg.Compiler.NockProgramCodec.program_immutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.program_immutable
/-- info: 'Minidregg.Compiler.NockProgramCodec.decode_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.decode_canonical
/-- info: 'Minidregg.Compiler.NockProgramCodec.wrong_version_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.wrong_version_refused
