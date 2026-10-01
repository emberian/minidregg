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
  cSHAKE256 over the whole `DREGG/PROGRAM/v1` record (evaluator id, code, ABI and the
  evaluator's params), and the
  cell id is `physicalId domain programId`. The ABI is in the identity because it
  decides what the kernel feeds the program: with the id over the jam alone, the
  first writer's ABI would be the only one any friend could ever use for that
  code. Two cells with the same jam and different ABIs are two programs.
* **Libraries.** `Abi.libraries` names other program cells by `programId`
  (NOCK N16: the hoon stdlib context rides once, not in every program). Their
  presence is checked against the store at birth (`CanonicalCellRegistry`).
* **Context (ABI v4; K-RUN-PIN's v3).** `Abi.context` says what the sample's context
  triple `[height caller room]` holds. `live`: the Host's height at admission, the
  signer and the room, so a claim is good for one height. `pinned`: the constants
  `[0 0 0]` (N11's choice for doors, `eny = our = now = 0`), so the sample is a
  function of the ABI's named slots and the target ids alone and one claim is
  admissible at every height where those slots hold the same values
  (`Kernel.NockProgramCell.sampleOf_pinned_of_fields`). A door is `live` only: its
  sample is its own state and event number, which every poke advances.
* **Noun slots.** `SlotType.noun`: the slot value is the atom of a noun's jam
  (N11's state encoding). In a sample the kernel cues it (refusing a value that is
  not the jam atom of the noun it cues to); in an output the kernel writes the jam
  atom of the product's noun, bounded by `nounMaxBytes`.
* **Params (E3).** What only the evaluator reads — Nock's arm — is not an ABI field: it is
  the record's `params` bytes, decoded by the evaluator (`Machine.decodeParams`; Nock's codec
  `DREGG/NOCK/PARAMS/v1` is `Kernel.NockEntry.encodeParams`). The ABI keeps what the KERNEL
  reads: the sample layout, the outputs, the libraries it loads, the fuel, the door, the context.
* **Names (E3).** No ABI name may hold a NUL (`NamesNulFree`, refused `nulInName`): Nock writes a
  key as a cord, and `cord "a" = cord "a\u0000"`.
* **Admission.** The birth check is the evaluator's (`Compiler.Evaluator.Machine.admit`,
  `admitRecord`): this file holds the record, its codec, its refusal names and the ABI's shape.
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

/-- v4 (E3): the record carries ABI v5 and the evaluator's params. Program-cell v1 (K-NOCK-CELL …
K-RUN-PIN), v2 (NC-2), v3 (E2) refuse at the version gate (`wrong_version_refused`). -/
def wireVersion : Nat := 4
/-- v2 added the optional `door` (N11); v3 (twice) `context`/`noun` and `max`; v4 their union (E2).
**v5** (E3): `arm` left the ABI for the evaluator's params, and the frame lost `NOCK`
(`DREGG/ABI/v5`: the ABI is the kernel's, read the same under every evaluator). A v1–v4 record
does not decode (`abi_old_frame_refused`). -/
def abiVersion : Nat := 5
/-- Registry tag 13 (final: 11 pay, 12 stream, 13 nockProgram, 14 clock); schema 91011. -/
def registryTag : UInt8 := 13
def schemaId : Nat := 91011

/-! ## The ABI -/

/-- How a projected slot value (an `Int`) becomes a sample noun, and an output
noun becomes a field value. `nat` is the atom itself and refuses negatives (what
every Hoon `@` sample expects); `int` is `Theory.Noun`'s zigzag `Int.toNoun`;
`noun` is the atom of the noun's jam (N11's state encoding), cued on the way in
and jammed on the way out. -/
inductive SlotType where
  | nat
  | int
  | noun
  deriving DecidableEq, Repr

/-- What the sample's context triple holds (K-RUN-PIN). `live`: the admission
height, the signer and the room. `pinned`: `[0 0 0]`, so the sample is a function
of the named slots and the targets only. -/
inductive ContextMode where
  | live
  | pinned
  deriving DecidableEq, Repr

/-- The largest jam (bytes) a `noun` output slot writes: the birth-source bound
(`native/resource-client/src/current_birth.rs` `MAX_SOURCE`, 4 MiB), the bound a
program's own jam already meets to be born. -/
def nounMaxBytes : Nat := 4194304

/-- One sample entry: the program sees `[key value]`, where `value` is the
participant slot `slot` of the command's `target`-th target (0-based, the
command's signed target order, K-JOINT's `joint/index/{target}/…`).

`max` (NC-2, DML's `int(n)` at the ABI): the largest atom the program will ever be
handed for this entry. A sample whose value encodes above it is refused
(`fieldOverMax`), so the program's sample shape holds `[0, max]` there
(`NockProgramCell.shapeOf`) and a step bound can be read from that shape
(`Theory.NockCost.Summaries.costSym`) before any run. `none`: undeclared, any atom. -/
structure SampleSlot where
  target : Nat
  slot : String
  key : String
  type : SlotType
  max : Option Nat := none
  deriving DecidableEq, Repr

/-- One write the program may emit: `[key value]` in its output list is a write
of object field `field` on the command's `target`-th target. -/
structure OutputSlot where
  key : String
  target : Nat
  field : Nat
  type : SlotType
  deriving DecidableEq, Repr

/-- A NockApp kernel door (NOCK §2.7, N11). The program's jam is the kernel
trap (booted with `[9 2 0 1]`); the params' arm is the poke axis (NockApp: 23) and
`peek` the peek axis (NockApp: 22). The door's state (core axis 6) lives as the
atom of its jam in object field `state` of the command's target 0, its event
number in field `event`. -/
structure Door where
  peek : Nat
  state : Nat
  event : Nat
  deriving DecidableEq, Repr

structure Abi where
  version : Nat
  sample : List SampleSlot
  outputs : List OutputSlot
  /-- Program cells (by `programId`) this program is run against. -/
  libraries : List Digest
  /-- The fuel bound a run is held to (Lean `Theory.Nock.steps`). -/
  fuel : Nat
  /-- A NockApp kernel door, or `none` for a gate. -/
  door : Option Door := none
  /-- What the sample's context triple holds (v4; K-RUN-PIN). -/
  context : ContextMode := .live
  deriving DecidableEq, Repr

/-- A program record. `evaluator` is the registry id of the evaluator the code is
for (`Compiler.Evaluator.id`; Nock's is `idOf "nock" "4K/Theory.Nock/v1"`): the kernel
re-executes the program on that evaluator and on no other, and `programId` covers it,
so the same bytes under another evaluator are another program (EVAL §1.4). -/
structure Program where
  evaluator : Digest
  jam : List UInt8
  abi : Abi
  /-- The evaluator's own entry data, as bytes only it decodes (`Machine.decodeParams`;
  Nock: `DREGG/NOCK/PARAMS/v1`, the arm). Covered by `programId`. -/
  params : List UInt8
  deriving DecidableEq, Repr

/-! ## Codecs `DREGG/ABI/v5`, `DREGG/PROGRAM/v1` -/

def slotTypeStream : StreamCodec SlotType :=
  StreamCodec.xmap StreamCodec.nat (fun | .nat => 0 | .int => 1 | .noun => 2)
    (fun n => if n = 1 then .int else if n = 2 then .noun else .nat)
    (by intro value; cases value <;> rfl)

def contextStream : StreamCodec ContextMode :=
  StreamCodec.xmap StreamCodec.nat (fun | .live => 0 | .pinned => 1)
    (fun n => if n = 1 then .pinned else .live) (by intro value; cases value <;> rfl)

def sampleSlotStream : StreamCodec SampleSlot :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product stringStream (StreamCodec.product stringStream
        (StreamCodec.product slotTypeStream (StreamCodec.option StreamCodec.nat)))))
    (fun s => (s.target, s.slot, s.key, s.type, s.max))
    (fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def outputSlotStream : StreamCodec OutputSlot :=
  StreamCodec.xmap
    (StreamCodec.product stringStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat slotTypeStream)))
    (fun s => (s.key, s.target, s.field, s.type)) (fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2⟩)
    (by intro value; cases value; rfl)

def doorStream : StreamCodec Door :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))
    (fun d => (d.peek, d.state, d.event)) (fun v => ⟨v.1, v.2.1, v.2.2⟩)
    (by intro value; cases value; rfl)

def abiStream : StreamCodec Abi :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.list sampleSlotStream)
        (StreamCodec.product (StreamCodec.list outputSlotStream)
          (StreamCodec.product (StreamCodec.list digestStream)
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product (StreamCodec.option doorStream) contextStream))))))
    (fun a => (a.version, a.sample, a.outputs, a.libraries, a.fuel, a.door, a.context))
    (fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def programStream : StreamCodec Program :=
  StreamCodec.xmap (StreamCodec.product digestStream
      (StreamCodec.product bytesStream (StreamCodec.product abiStream bytesStream)))
    (fun p => (p.evaluator, p.jam, p.abi, p.params)) (fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2⟩)
    (by intro value; cases value; rfl)

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

/-- `DREGG/ABI/v5` -/
def abiFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 65, 66, 73, 47, 118, 53]
/-- `DREGG/PROGRAM/v1` (E3, EVAL §1.4: the evaluator-generic record — evaluator id, code, ABI,
params; the `DREGG/NOCK/PROGRAM/v1..v3` frames do not decode, and every `programId` changes). -/
def programFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 80, 82, 79, 71, 82, 65, 77, 47, 118, 49]

theorem abiFrame_spells : abiFrame = "DREGG/ABI/v5".toUTF8.toList := by decide +kernel
theorem programFrame_spells : programFrame = "DREGG/PROGRAM/v1".toUTF8.toList := by decide +kernel

def abiCodec : LawfulCodec Abi := framed abiFrame abiStream
def programCodec : LawfulCodec Program := framed programFrame programStream

theorem abi_roundtrip (abi : Abi) : abiCodec.decode (abiCodec.encode abi) = some abi :=
  abiCodec.decode_encode abi

/-- The frames of ABI v1 (K-NOCK), v2 (N11), v3 (K-RUN-PIN's and NC-2's, two shapes), v4 (E2). -/
def abiFrameV1 : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 78, 79, 67, 75, 47, 65, 66, 73, 47, 118, 49]
def abiFrameV2 : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 78, 79, 67, 75, 47, 65, 66, 73, 47, 118, 50]
def abiFrameV3 : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 78, 79, 67, 75, 47, 65, 66, 73, 47, 118, 51]
def abiFrameV4 : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 78, 79, 67, 75, 47, 65, 66, 73, 47, 118, 52]

theorem framedDecode_other_frame {α : Type} {frame old : List UInt8} (stream : StreamCodec α)
    (rest : List UInt8) (long : frame.length ≤ old.length) (differ : old.take frame.length ≠ frame) :
    framedDecode frame stream (old ++ rest) = none := by
  unfold framedDecode
  rw [List.take_append_of_le_length long, if_neg differ]

/-- A record under an older ABI frame does not decode: v1–v4 refuse to load rather than
being read as v5 (whatever bytes follow the frame). -/
theorem abi_old_frame_refused (rest : List UInt8) :
    abiCodec.decode (abiFrameV1 ++ rest) = none ∧ abiCodec.decode (abiFrameV2 ++ rest) = none ∧
      abiCodec.decode (abiFrameV3 ++ rest) = none ∧ abiCodec.decode (abiFrameV4 ++ rest) = none := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show framedDecode abiFrame abiStream (abiFrameV1 ++ rest) = none
    exact framedDecode_other_frame abiStream rest (by decide) (by decide)
  · show framedDecode abiFrame abiStream (abiFrameV2 ++ rest) = none
    exact framedDecode_other_frame abiStream rest (by decide) (by decide)
  · show framedDecode abiFrame abiStream (abiFrameV3 ++ rest) = none
    exact framedDecode_other_frame abiStream rest (by decide) (by decide)
  · show framedDecode abiFrame abiStream (abiFrameV4 ++ rest) = none
    exact framedDecode_other_frame abiStream rest (by decide) (by decide)

/-- `DREGG/NOCK/PROGRAM/v3`: E2's record frame. -/
def programFrameNockV3 : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 78, 79, 67, 75, 47, 80, 82, 79, 71, 82, 65, 77, 47, 118, 51]

/-- E2's `DREGG/NOCK/PROGRAM/v3` record does not decode as `DREGG/PROGRAM/v1`. -/
theorem program_old_frame_refused (rest : List UInt8) :
    programCodec.decode (programFrameNockV3 ++ rest) = none := by
  show framedDecode programFrame programStream (programFrameNockV3 ++ rest) = none
  exact framedDecode_other_frame programStream rest (by decide) (by decide)

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

/-- cSHAKE256 over the program record (evaluator id, jam and ABI): what a run claim names. -/
def programId (program : Program) : Digest :=
  (Sp800185Cshake256.hash programCustomization (programCodec.encode program)).digest

/-- The cell a program lives in, in one deployment. -/
def physicalId (domain id : Digest) : Nat :=
  (Sp800185Cshake256.hash idCustomization
    ((StreamCodec.product digestStream digestStream).encode (domain, id))).digest.value

/-! ## Admissibility at birth -/

/-- Why a program is not admitted. Order is the check order. -/
inductive Refusal where
  /-- The record names an evaluator id no compiled-in entry has (K-EVAL; E3: at birth). -/
  | unknownEvaluator
  /-- The record's evaluator is compiled in and this deployment's operator disabled it. -/
  | evaluatorDisabled
  | noCue
  | nonCanonical
  | abiVersion
  /-- An ABI name (a sample slot, a sample key, an output key) holds a NUL (E3). -/
  | nulInName
  | fuelZero
  /-- The evaluator's params bytes do not decode (`Machine.decodeParams`). -/
  | paramsMalformed
  | armZero
  | abiShape
  | missingLibrary
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .unknownEvaluator => "unknownEvaluator"
  | .evaluatorDisabled => "evaluatorDisabled"
  | .noCue => "noCue"
  | .nonCanonical => "nonCanonical"
  | .abiVersion => "abiVersion"
  | .nulInName => "nulInName"
  | .fuelZero => "fuelZero"
  | .paramsMalformed => "paramsMalformed"
  | .armZero => "armZero"
  | .abiShape => "abiShape"
  | .missingLibrary => "missingLibrary"

/-- Why a door's effects are not writes (N11's two refusals, evaluator-generic: `Kernel.Door`
reports them as `outputMalformed` and `effectNotWrite`). -/
inductive EffectRefusal where
  | effectsMalformed
  | effectNotWrite
  deriving DecidableEq, Repr

/-- A door reads no sample slots and no libraries (its subject is the kernel's
own `[[trap state] job]`), names a peek arm, and keeps its state and event
fields apart from each other and from every output write on target 0.

A door is `live`, never `pinned`: its sample holds no height (the job's
`eny our now` are already the constants 0), and what it does hold, the stored
state and the event number, is advanced by every poke, so no poke claim can be
admitted twice. `pinned` on a door would be a field that changes nothing and
reads as a promise of reuse, so it is refused at birth. -/
def DoorShape (abi : Abi) (door : Door) : Prop :=
  0 < door.peek ∧ door.state ≠ door.event ∧ abi.sample = [] ∧ abi.libraries = [] ∧
    abi.context = .live ∧
    ∀ o ∈ abi.outputs, o.target = 0 → o.field ≠ door.state ∧ o.field ≠ door.event

instance doorShapeDecidable (abi : Abi) (door : Door) : Decidable (DoorShape abi door) := by
  unfold DoorShape; infer_instance

/-- The key prefix reserved for the target entries of the sample. -/
def targetPrefix : String := "target/"

/-- Keys are unambiguous: sample keys and output keys are each distinct, no
sample key can be mistaken for a target entry, libraries are distinct. A declared
maximum bounds an atom, so a `noun` slot (whose value may be a cell) declares none:
NC-2's `max` and K-RUN-PIN's `noun` met in ABI v4, and the pair is refused at birth
rather than read as "an atom no larger than `max`". -/
def AbiShape (abi : Abi) : Prop :=
  (abi.sample.map SampleSlot.key).Nodup ∧ (abi.outputs.map OutputSlot.key).Nodup ∧
    abi.libraries.Nodup ∧ (∀ slot ∈ abi.sample, targetPrefix.isPrefixOf slot.key = false) ∧
    (∀ slot ∈ abi.sample, slot.type = .noun → slot.max = none) ∧
    ∀ door ∈ abi.door, DoorShape abi door

instance abiShapeDecidable (abi : Abi) : Decidable (AbiShape abi) := by
  unfold AbiShape; infer_instance

/-! ## Names: no NUL (E3)

Nock writes a sample key as a cord, which drops trailing zero bytes, so `"a"` and
`"a\u0000"` are one key on the wire (E1, `scratch/CordKeyCollision.lean`). A name with a
NUL is therefore refused where the ABI is read (`Machine.admit`, refusal `nulInName`), for
every name the ABI carries. -/

/-- No zero byte in the name's UTF-8 bytes. In UTF-8 the only zero byte is U+0000's, so
this is exactly "the name holds no NUL". -/
def NulFree (name : String) : Prop := (0 : UInt8) ∉ name.toUTF8.toList

instance nulFreeDecidable (name : String) : Decidable (NulFree name) := by
  unfold NulFree; infer_instance

/-- Every name an ABI carries: each sample slot's participant slot and key, each output key. -/
def abiNames (abi : Abi) : List String :=
  abi.sample.flatMap (fun slot => [slot.slot, slot.key]) ++ abi.outputs.map OutputSlot.key

def NamesNulFree (abi : Abi) : Prop := ∀ name ∈ abiNames abi, NulFree name

instance namesNulFreeDecidable (abi : Abi) : Decidable (NamesNulFree abi) := by
  unfold NamesNulFree; infer_instance

theorem NamesNulFree.keys {abi : Abi} (h : NamesNulFree abi) :
    ∀ slot ∈ abi.sample, NulFree slot.key := fun slot member =>
  h _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨slot, member, by simp⟩))

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
theorem admissible_jam_unique {left right : Program} (hl : Noun.canonical left.jam = true)
    (hr : Noun.canonical right.jam = true) (same : Noun.cue left.jam = Noun.cue right.jam) :
    left.jam = right.jam :=
  Noun.canonical_unique hl hr same

theorem admissible_jam_eq {program : Program} (admitted : Noun.canonical program.jam = true)
    {n : Noun} (cued : Noun.cue program.jam = some n) : program.jam = Noun.jam n := by
  obtain ⟨m, hm⟩ := Noun.canonical_iff.mp admitted
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
/-- info: 'Minidregg.Compiler.NockProgramCodec.abi_old_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.abi_old_frame_refused
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
/-- info: 'Minidregg.Compiler.NockProgramCodec.padded_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.padded_refused
/-- info: 'Minidregg.Compiler.NockProgramCodec.admissible_jam_unique' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.admissible_jam_unique
/-- info: 'Minidregg.Compiler.NockProgramCodec.admissible_jam_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.admissible_jam_eq
/-- info: 'Minidregg.Compiler.NockProgramCodec.program_immutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.program_immutable
/-- info: 'Minidregg.Compiler.NockProgramCodec.decode_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.decode_canonical
/-- info: 'Minidregg.Compiler.NockProgramCodec.wrong_version_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.wrong_version_refused
/-- info: 'Minidregg.Compiler.NockProgramCodec.program_old_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.program_old_frame_refused
/-- info: 'Minidregg.Compiler.NockProgramCodec.abiFrame_spells' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NockProgramCodec.abiFrame_spells
