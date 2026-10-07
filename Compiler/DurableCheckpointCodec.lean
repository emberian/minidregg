/-
# Compiler.DurableCheckpointCodec — the durable log, its MAC chain, and checkpoints

The host's durable store is three objects (the whole-image `DREGG.DURABLE.IMAGE`
record is gone):

* the **seed**, written once at bootstrap (`DREGG.DURABLE.SEED/v1`);
* the **log**: entry `h` (1-based) is one accepted record (`DREGG.DURABLE.LOG/v2`: the record and its signing subject)
  and a 32-byte tag. The log is chained by C1's log root: `chain₀ = logStart seed`
  (the host passes `NativeHostCodec.logRoot0 domain semantics`), and
  `chainₕ = Kernel.WorldRoot.chainDigest chainₕ₋₁ (recordDigest recordₕ)`; the tag of
  entry `h` is `KMAC256(key, (keyId, h, chainₕ))`. One chain: the value the
  world root's system slot commits to is the value the MAC authenticates;
* **checkpoints** (`DREGG.DURABLE.CHECKPOINT/v1`): the materialized state at a
  height, its world root, the log chain at that height, and
  `KMAC256(key, (keyId, height, root, H(body bytes)))`.

**MAC custody (DATAMODEL §6 Q1).** The key is 32 bytes generated at
`mini bootstrap`, stored mode 0600 beside the operator configuration, one per
Store; it authenticates only that Store's checkpoints and log tags. Rotation is
a new checkpoint at the head under the new key (the checkpoint's chain value
then vouches for every earlier entry). The MAC means "this host executed and
accepted this history"; an attacker who can forge it can already forge the
host's receipts, so no new trust is introduced. Genesis re-admission of every
signed ingress remains available as the operator `audit` command.

**What is checked on open** (`Compiler.DurableReceiverIO.load`): the chain is
recomputed over every stored record; the latest checkpoint's MAC, key id, world
root and chain value must all match; every entry's tag must verify
(`Compiler.DurableLogTags`), refused by height. Any mismatch refuses to open — nothing reinterprets.

The world root is the parameterised `Checkpoint.check` of DATAMODEL B2 over
the current cell-root function (`rootBytes`), until C1 supplies the world-root
function; it is recomputed from the checkpoint's cells, never trusted.
-/
import Compiler.DurableReceiverCodec
import Compiler.Sp800185Cshake256
import Compiler.Sp800185Kmac256
import Kernel.DurableCheckpoint
import Kernel.WorldRootCache
import Theory.AssertAxioms
import Theory.AssertCompiled

namespace Minidregg.Compiler.DurableCheckpointCodec

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableCheckpoint
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableReceiverCodec
open Minidregg.Compiler.Sp800185Cshake256 (cshake256Bytes kmac256Bytes kmac256Bytes_length)

set_option autoImplicit false

/-! ## Framed objects -/

/-- A fixed frame followed by one stream value, recovered only on exact
re-encoding (no aliases, no trailing bytes). -/
structure Framed (α : Type) where
  frame : List UInt8
  stream : StreamCodec α

namespace Framed

variable {α : Type}

def encode (framed : Framed α) (value : α) : List UInt8 :=
  (StreamCodec.product bytesStream framed.stream).encode (framed.frame, value)

def decode (framed : Framed α) (bytes : List UInt8) : Option α := do
  let (frame, value) ← (StreamCodec.product bytesStream framed.stream).toLawful.decode bytes
  if frame = framed.frame ∧ framed.encode value = bytes then some value else none

theorem decode_encode (framed : Framed α) (value : α) :
    framed.decode (framed.encode value) = some value := by
  have roundtrip : (StreamCodec.product bytesStream framed.stream).toLawful.decode
      (framed.encode value) = some (framed.frame, value) :=
    (StreamCodec.product bytesStream framed.stream).toLawful.decode_encode (framed.frame, value)
  unfold decode
  rw [roundtrip]
  simp

theorem decode_canonical (framed : Framed α) {bytes : List UInt8} {value : α}
    (decoded : framed.decode bytes = some value) : framed.encode value = bytes := by
  unfold decode at decoded
  cases raw : (StreamCodec.product bytesStream framed.stream).toLawful.decode bytes with
  | none => simp [raw] at decoded
  | some pair =>
      simp only [raw, bind, Option.bind] at decoded
      split at decoded
      next ok => cases Option.some.inj decoded; exact ok.2
      next => contradiction

/-- Bytes carrying any other frame refuse: the frame is the first stream
value, so a decode would re-encode to a different first value. -/
theorem decode_other_frame (framed : Framed α) {other : List UInt8}
    (different : other ≠ framed.frame) (tail : List UInt8) :
    framed.decode (bytesStream.encode other ++ tail) = none := by
  cases decoded : framed.decode (bytesStream.encode other ++ tail) with
  | none => rfl
  | some value =>
      have exact := decode_canonical framed decoded
      have prefixed := bytesStream.decodePrefix_encode framed.frame (framed.stream.encode value)
      simp only [encode, StreamCodec.product] at exact
      rw [exact, bytesStream.decodePrefix_encode] at prefixed
      exact absurd (congrArg Prod.fst (Option.some.inj prefixed)) different

end Framed

/-! ## The Store epoch

A Store's bytes commit to five format components: the declared-effect state-key
codec, the cell schema references (hence every declared cell's layout digest),
the log-tag MAC label, the history accumulator and spent map, and the command
codecs its log records carry (a record replays by decoding its command). The
seed frame names them all, so a Store of another epoch is refused by name — read
from its seed before anything else, including the physical head anchor
(`DurableReceiverIO.load`).

The label is a `;`-separated list of parts, each `name/version`. It is read BY
NAME (`StoreEpoch.parse`), never by position or count: a component that is absent
reads as `"none"` and is refused naming that component, and a component of
another version is refused naming it. -/

/-- The log-tag MAC customization; `entryTag` uses exactly this label. -/
def logTagLabel : String := "DREGG/NATIVE-HOST/LOG-TAG/v3"

/-- One Store epoch: the format components its bytes commit to. -/
structure StoreEpoch where
  stateKey : String
  schemaRefs : String
  logTag : String
  /-- The history accumulator and spent map (`Compiler.DurableHistory`,
  `Compiler.DurableSpent`, KN2-STORE-OPEN). A three-component label (an epoch
  born before it) reads as `none` and is refused by naming this component. -/
  accumulator : String
  /-- The command codecs of the log records. `commands/v2`: the delegation
  command no longer signs the authority-cell root
  (`CapabilityDelegationController.commandFrame` v2). A label without it (an
  epoch born before it) reads as `none` and is refused by naming it. -/
  commands : String
  deriving DecidableEq, Repr

/-- The epoch this Host writes and reads. `stateKey` is
`DeclaredEffectCell.stateKeyCodecId` and `schemaRefs` the declared-effect
schema reference version (`DeployedCellRegistry.declaredEffectSchemaRef`);
`ConsentAnchor.storeEpoch_stateKey`/`storeEpoch_schemaRefs` fail to build when
either moves without this value. A change to any component changes the seed
frame and refuses every older Store by name. -/
def StoreEpoch.current : StoreEpoch :=
  ⟨"state-key/tagged-v4", "schema-refs/v5", logTagLabel,
    "history/mmr-v1;spent/trie-v1;checkpoint/v3", "commands/v2"⟩

/-- The label carried in the seed frame: every component, `;`-separated (the
accumulator is itself two parts, `history/…;spent/…`). -/
def StoreEpoch.label (epoch : StoreEpoch) : String :=
  s!"{epoch.stateKey};{epoch.schemaRefs};{epoch.logTag};{epoch.accumulator};{epoch.commands}"

/-- A label part's name: everything before its last `/`
(`DREGG/NATIVE-HOST/LOG-TAG/v3` is named `DREGG/NATIVE-HOST/LOG-TAG`). -/
def StoreEpoch.partName (part : String) : String :=
  "/".intercalate (part.splitOn "/").dropLast

/-- The accumulator's own parts, in label order (`Compiler.DurableHistory`,
`Compiler.DurableSpent`, and the checkpoint shape of KN2-STORE-OPEN). -/
def StoreEpoch.accumulatorParts : List String := ["history", "spent", "checkpoint"]

/-- Every part name a label may carry, in label order. -/
def StoreEpoch.partNames : List String :=
  ["state-key", "schema-refs", "DREGG/NATIVE-HOST/LOG-TAG"] ++ StoreEpoch.accumulatorParts ++ ["commands"]

/-- The part of a label named `name`, if present. -/
def StoreEpoch.partNamed (parts : List String) (name : String) : Option String :=
  parts.find? (fun part => StoreEpoch.partName part == name)

/-- Read a label BY NAME. The parts must be known names, each at most once, in
label order; state key, schema references and log tags have been in every label
and are required. An absent accumulator or command-codec component reads as
`"none"` (an epoch born before it), so it is refused naming that component and
never read as this Host's. The accumulator is its present parts in order, so a
label missing one of them differs from this Host's and is refused naming the
accumulator. -/
def StoreEpoch.parse (text : String) : Option StoreEpoch :=
  let parts := text.splitOn ";"
  let names := parts.map StoreEpoch.partName
  if names = StoreEpoch.partNames.filter (names.contains ·) then
    match StoreEpoch.partNamed parts "state-key", StoreEpoch.partNamed parts "schema-refs",
        StoreEpoch.partNamed parts "DREGG/NATIVE-HOST/LOG-TAG" with
    | some stateKey, some schemaRefs, some logTag =>
        let accumulator := match StoreEpoch.accumulatorParts.filterMap (StoreEpoch.partNamed parts) with
          | [] => "none"
          | present => ";".intercalate present
        some ⟨stateKey, schemaRefs, logTag, accumulator,
          (StoreEpoch.partNamed parts "commands").getD "none"⟩
    | _, _, _ => none
  else none

/-- The components in which a Store's epoch differs from this Host's, named. -/
def StoreEpoch.differing (store host : StoreEpoch) : List String :=
  (if store.stateKey = host.stateKey then [] else
      [s!"state-key codec: Store {store.stateKey}, this Host {host.stateKey}"]) ++
    (if store.schemaRefs = host.schemaRefs then [] else
      [s!"cell schema references: Store {store.schemaRefs}, this Host {host.schemaRefs}"]) ++
    (if store.logTag = host.logTag then [] else
      [s!"log tags: Store {store.logTag}, this Host {host.logTag}"]) ++
    (if store.accumulator = host.accumulator then [] else
      [s!"history accumulator: Store {store.accumulator}, this Host {host.accumulator}"]) ++
    (if store.commands = host.commands then [] else
      [s!"command codecs: Store {store.commands}, this Host {host.commands}"])

/-- **No component differs exactly when the epochs are equal.** -/
theorem StoreEpoch.differing_nil_iff (store host : StoreEpoch) :
    store.differing host = [] ↔ store = host := by
  cases store; cases host
  simp only [StoreEpoch.differing, StoreEpoch.mk.injEq]
  constructor
  · intro none
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (apply Classical.byContradiction; intro ne; simp_all)
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    simp

/-- **A state-key codec break is named, and only it.** -/
theorem StoreEpoch.differing_stateKey (host : StoreEpoch) (stateKey : String)
    (changed : stateKey ≠ host.stateKey) :
    StoreEpoch.differing { host with stateKey } host =
      [s!"state-key codec: Store {stateKey}, this Host {host.stateKey}"] := by
  simp [StoreEpoch.differing, changed]

/-- **A schema-reference break is named, and only it.** -/
theorem StoreEpoch.differing_schemaRefs (host : StoreEpoch) (schemaRefs : String)
    (changed : schemaRefs ≠ host.schemaRefs) :
    StoreEpoch.differing { host with schemaRefs } host =
      [s!"cell schema references: Store {schemaRefs}, this Host {host.schemaRefs}"] := by
  simp [StoreEpoch.differing, changed]

/-- **A log-tag break is named, and only it.** -/
theorem StoreEpoch.differing_logTag (host : StoreEpoch) (logTag : String)
    (changed : logTag ≠ host.logTag) :
    StoreEpoch.differing { host with logTag } host =
      [s!"log tags: Store {logTag}, this Host {host.logTag}"] := by
  simp [StoreEpoch.differing, changed]

def seedFrameName : List UInt8 := "DREGG.DURABLE.SEED".toUTF8.toList

/-- Seed frame v2: the name, version byte 2, then the epoch label. The v1 frame
(name and byte 1) carried no epoch, so a v1 Store's components are unknown (it
may be of any earlier epoch, including this one's components): it refuses as
unlabelled. -/
def seedFrame : Framed Seed :=
  ⟨seedFrameName ++ [2] ++ StoreEpoch.current.label.toUTF8.toList, seedStream⟩

/-- What a Store's seed bytes say about its epoch, read from the frame alone. -/
inductive SeedEpoch where
  | labelled (epoch : StoreEpoch)
  | unlabelled (version : UInt8)
  | foreign

def SeedEpoch.ofBytes (bytes : List UInt8) : SeedEpoch :=
  match bytesStream.decodePrefix bytes with
  | none => .foreign
  | some (frame, _) =>
      if frame = seedFrame.frame then .labelled StoreEpoch.current
      else if frame = seedFrameName ++ [1] then .unlabelled 1
      else if frame.take seedFrameName.length = seedFrameName then
        match frame.drop seedFrameName.length with
        | 2 :: label =>
            match String.fromUTF8? label.toByteArray >>= StoreEpoch.parse with
            | some epoch => .labelled epoch
            | none => .foreign
        | [version] => .unlabelled version
        | _ => .foreign
      else .foreign

/-- The refusal naming a Store's epoch, or `none` when it is this Host's. -/
def SeedEpoch.refusal : SeedEpoch → Option String
  | .labelled epoch =>
      match epoch.differing StoreEpoch.current with
      | [] => none
      | named => some s!"this Store was born in another epoch ({String.intercalate "; " named}); re-genesis the world"
  | .unlabelled version =>
      some s!"this Store's seed frame is version {version}, which carries no epoch label (it was born before Store epochs were labelled, so its state-key codec, schema references and log tags are unknown); this Host reads {StoreEpoch.current.label}; re-genesis the world"
  | .foreign => some "the Store's seed is not a durable seed frame"

/-- The current seed frame reads back as this Host's labelled epoch. -/
theorem seedEpoch_ofBytes_current (rest : List UInt8) :
    SeedEpoch.ofBytes (bytesStream.encode seedFrame.frame ++ rest) =
      .labelled StoreEpoch.current := by
  unfold SeedEpoch.ofBytes
  rw [bytesStream.decodePrefix_encode]
  simp

/-- **This Host's own seeds pass the epoch check.** -/
theorem seedEpoch_current (seed : Seed) :
    (SeedEpoch.ofBytes (seedFrame.encode seed)).refusal = none := by
  show (SeedEpoch.ofBytes (bytesStream.encode seedFrame.frame ++ seedStream.encode seed)).refusal = none
  rw [seedEpoch_ofBytes_current]
  simp [SeedEpoch.refusal, (StoreEpoch.differing_nil_iff _ _).mpr rfl]

/-- **Every v1 Store refuses by name**: its frame carries no epoch. -/
theorem seedEpoch_v1_refused (rest : List UInt8) :
    ∃ named, (SeedEpoch.ofBytes (bytesStream.encode (seedFrameName ++ [1]) ++ rest)).refusal =
      some named := by
  have older : seedFrameName ++ [1] ≠ seedFrame.frame := by
    intro same
    have tails := List.append_cancel_left (same.trans (by simp [seedFrame]) :
      seedFrameName ++ [1] = seedFrameName ++ (2 :: StoreEpoch.current.label.toUTF8.toList))
    simp at tails
  unfold SeedEpoch.ofBytes
  rw [bytesStream.decodePrefix_encode]
  simp only [older, if_false, if_true]
  exact ⟨_, rfl⟩

/-- **An accumulator break is named, and only it.** -/
theorem StoreEpoch.differing_accumulator (host : StoreEpoch) (accumulator : String)
    (changed : accumulator ≠ host.accumulator) :
    StoreEpoch.differing { host with accumulator } host =
      [s!"history accumulator: Store {accumulator}, this Host {host.accumulator}"] := by
  simp [StoreEpoch.differing, changed]

/-- **A command-codec break is named, and only it.** -/
theorem StoreEpoch.differing_commands (host : StoreEpoch) (commands : String)
    (changed : commands ≠ host.commands) :
    StoreEpoch.differing { host with commands } host =
      [s!"command codecs: Store {commands}, this Host {host.commands}"] := by
  simp [StoreEpoch.differing, changed]

/-- The seed frame of a Store whose label is `label`. -/
def labelledFrame (label : String) : List UInt8 := seedFrameName ++ 2 :: label.toUTF8.toList

/-- The refusal for a Store labelled `label`, which `SeedEpoch.ofBytes` reads
from its frame alone (whatever follows). -/
theorem seedEpoch_ofBytes_labelled (label : String) (rest : List UInt8) :
    SeedEpoch.ofBytes (bytesStream.encode (labelledFrame label) ++ rest) =
      SeedEpoch.ofBytes (bytesStream.encode (labelledFrame label)) := by
  unfold SeedEpoch.ofBytes
  rw [bytesStream.decodePrefix_encode, ← List.append_nil (bytesStream.encode (labelledFrame label)),
    bytesStream.decodePrefix_encode]

/-! ### Poles: each missing or other-version component is refused naming it, and only it

The claims go through `String.splitOn` and `String.fromUTF8?`, which the kernel
does not reduce; they are checked by the compiled evaluator (`#assert_compiled`). -/

/-- This Host's label with the command-codec component removed: an epoch born
before it. -/
def labelWithoutCommands : String :=
  s!"{StoreEpoch.current.stateKey};{StoreEpoch.current.schemaRefs};{StoreEpoch.current.logTag};{StoreEpoch.current.accumulator}"

/-- This Host's label with the accumulator removed. -/
def labelWithoutAccumulator : String :=
  s!"{StoreEpoch.current.stateKey};{StoreEpoch.current.schemaRefs};{StoreEpoch.current.logTag};{StoreEpoch.current.commands}"

/-- This Host's label at command codecs v1. -/
def labelCommandsV1 : String := StoreEpoch.label { StoreEpoch.current with commands := "commands/v1" }

theorem seedEpoch_noCommands_refused (rest : List UInt8) :
    (SeedEpoch.ofBytes (bytesStream.encode (labelledFrame labelWithoutCommands) ++ rest)).refusal =
      some "this Store was born in another epoch (command codecs: Store none, this Host commands/v2); re-genesis the world" := by
  rw [seedEpoch_ofBytes_labelled]
  native_decide

theorem seedEpoch_commandsV1_refused (rest : List UInt8) :
    (SeedEpoch.ofBytes (bytesStream.encode (labelledFrame labelCommandsV1) ++ rest)).refusal =
      some "this Store was born in another epoch (command codecs: Store commands/v1, this Host commands/v2); re-genesis the world" := by
  rw [seedEpoch_ofBytes_labelled]
  native_decide

theorem seedEpoch_noAccumulator_refused (rest : List UInt8) :
    (SeedEpoch.ofBytes (bytesStream.encode (labelledFrame labelWithoutAccumulator) ++ rest)).refusal =
      some "this Store was born in another epoch (history accumulator: Store none, this Host history/mmr-v1;spent/trie-v1;checkpoint/v3); re-genesis the world" := by
  rw [seedEpoch_ofBytes_labelled]
  native_decide

#assert_axioms StoreEpoch.differing_accumulator
#assert_axioms StoreEpoch.differing_commands
#assert_axioms seedEpoch_ofBytes_labelled
#assert_compiled seedEpoch_noCommands_refused
#assert_compiled seedEpoch_commandsV1_refused
#assert_compiled seedEpoch_noAccumulator_refused
#assert_axioms StoreEpoch.differing_nil_iff
#assert_axioms StoreEpoch.differing_stateKey
#assert_axioms StoreEpoch.differing_schemaRefs
#assert_axioms StoreEpoch.differing_logTag
#assert_axioms seedEpoch_current
#assert_axioms seedEpoch_v1_refused
/-- Version 2: a record carries its signing subject (`IntentRecord.subject`),
which the presence index folds. A v1 record refuses (`v1_record_refused`). -/
def recordFrame : Framed IntentRecord := ⟨"DREGG.DURABLE.LOG".toUTF8.toList ++ [2], intentStream⟩

def retiredRecordFrameV1 : List UInt8 := "DREGG.DURABLE.LOG".toUTF8.toList ++ [1]

theorem v1_record_refused (tail : List UInt8) :
    recordFrame.decode (bytesStream.encode retiredRecordFrameV1 ++ tail) = none :=
  Framed.decode_other_frame recordFrame (by decide +kernel) tail

/-- info: 'Minidregg.Compiler.DurableCheckpointCodec.v1_record_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v1_record_refused

/-! ## The MAC key -/

structure MacKey where
  bytes : List UInt8
  length_exact : bytes.length = 32

def MacKey.ofBytes? (bytes : List UInt8) : Option MacKey :=
  if exact : bytes.length = 32 then some ⟨bytes, exact⟩ else none

/-- A public identifier of the key (a hash of a 256-bit secret). -/
def MacKey.id (key : MacKey) : List UInt8 :=
  cshake256Bytes "DREGG/NATIVE-HOST/MAC-KEY-ID/v1".toUTF8.toList key.bytes

/-! ## The log chain and entry tags -/

/-- The turn digest of an accepted record: cSHAKE over its canonical bytes. -/
def recordDigest (record : IntentRecord) : Digest :=
  Kernel.WorldRoot.turnDigestOfBytes (intentStream.encode record)

def chainStep (previous : Digest) (record : IntentRecord) : Digest :=
  Kernel.WorldRoot.chainDigest previous (recordDigest record)

/-- The chain value after the given records, in order. -/
def chainAfter (start : Digest) (records : List IntentRecord) : Digest :=
  records.foldl chainStep start

/-- The turn digest of a record read off its STORED bytes: the bytes after the
frame, hashed as they are (no decode-then-re-encode on the open's chain). -/
def storedRecordDigest (bytes : List UInt8) : Digest :=
  Kernel.WorldRoot.turnDigestOfBytes (bytes.drop (bytesStream.encode recordFrame.frame).length)

/-- **Hashing the stored bytes is hashing the record**, whenever the bytes
decode: the codec is canonical (`Framed.decode_canonical`), so the stored bytes
ARE the frame followed by the record's canonical encoding. A non-canonical
stored encoding does not decode, and the open refuses it by height before any
chain is computed. -/
theorem storedRecordDigest_eq {bytes : List UInt8} {record : IntentRecord}
    (decoded : recordFrame.decode bytes = some record) :
    storedRecordDigest bytes = recordDigest record := by
  have canonical := Framed.decode_canonical recordFrame decoded
  unfold storedRecordDigest recordDigest
  rw [← canonical]
  simp [Framed.encode, StreamCodec.product, recordFrame]

/-- One chain link from a record's stored bytes. -/
def chainStepStored (previous : Digest) (bytes : List UInt8) : Digest :=
  Kernel.WorldRoot.chainDigest previous (storedRecordDigest bytes)

theorem chainStepStored_eq {previous : Digest} {bytes : List UInt8} {record : IntentRecord}
    (decoded : recordFrame.decode bytes = some record) :
    chainStepStored previous bytes = chainStep previous record := by
  unfold chainStepStored chainStep
  rw [storedRecordDigest_eq decoded]

#assert_axioms storedRecordDigest_eq
#assert_axioms chainStepStored_eq

theorem chainAfter_append (start : Digest) (left right : List IntentRecord) :
    chainAfter start (left ++ right) = chainAfter (chainAfter start left) right := by
  simp [chainAfter, List.foldl_append]

/-- The system slot's leaf: the height and the log root (C1's
`NativeHostCodec.Leaf.system`). -/
def systemLeaf (height : Nat) (chain : Digest) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.SYSTEM/v1".toUTF8.toList
    ((StreamCodec.product StreamCodec.nat digestStream).encode (height, chain))).digest

-- The entry tag (v3 trailer: root, chain, frontier digest, spent root, MAC)
-- is `Compiler.DurableHistory.trailer`; the log-tag label above is its MAC label.

/-! ## Checkpoints -/

/-- v3: the cells and the allowance; no consumed nullifiers (they are a
function of the verified prefix, `DurableCheckpoint.State`). -/
def stateStream : StreamCodec State :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product (StreamCodec.list (StreamCodec.product digestStream bytesStream))
        chargeStream))
    (fun state => (state.absentBytes, state.cells, state.available))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro value; cases value; rfl)

/-- The authenticated content of a checkpoint. -/
structure Body where
  keyId : List UInt8
  height : Nat
  chain : Digest
  /-- The log accumulator's peaks after `height` leaves (`DurableHistory`). -/
  frontier : List (Nat × Digest)
  /-- The spent map's root after `height` records (`DurableSpent`). -/
  spentRoot : Digest
  state : State

def frontierStream : StreamCodec (List (Nat × Digest)) :=
  StreamCodec.list (StreamCodec.product StreamCodec.nat digestStream)

def bodyStream : StreamCodec Body :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream
        (StreamCodec.product frontierStream (StreamCodec.product digestStream stateStream)))))
    (fun body => (body.keyId, body.height, body.chain, body.frontier, body.spentRoot, body.state))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2.1, tuple.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

/-- The world-root entries of a materialized state at a height: the system slot
(height, log root), then every cell's root under the cell-root function — C1's
`NativeHostCodec.worldEntries`, read off a state instead of an image. -/
def stateEntries (rootBytes : List UInt8 → Digest) (height : Nat) (chain : Digest)
    (state : State) : List (Kernel.WorldRoot.Key × Digest) :=
  (.system, systemLeaf height chain) ::
    state.cells.map fun cell => (.cell cell.1.value, rootBytes cell.2)

/-- The checkpoint's world root: C1's deployed root of its entries, so it is
the receipt root at that height. Recomputed on open, never trusted. -/
def worldRoot (rootBytes : List UInt8 → Digest) (body : Body) : Digest :=
  Kernel.WorldRoot.deployedRoot (stateEntries rootBytes body.height body.chain body.state)

structure Sealed where
  body : Body
  root : Digest
  mac : List UInt8

def sealedStream : StreamCodec Sealed :=
  StreamCodec.xmap (StreamCodec.product bodyStream (StreamCodec.product digestStream bytesStream))
    (fun sealed => (sealed.body, sealed.root, sealed.mac))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro value; cases value; rfl)

/-- v3: the body carries the accumulator frontier and the spent root, and its
state no consumed nullifiers. An older checkpoint refuses (`malformed`): its
frame differs; the Store epoch (`StoreEpoch.accumulator`) names the change. -/
def checkpointFrame : Framed Sealed :=
  ⟨"DREGG.DURABLE.CHECKPOINT".toUTF8.toList ++ [3], sealedStream⟩

def macInputStream : StreamCodec (List UInt8 × Nat × Digest × List UInt8) :=
  StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream bytesStream))

/-- `KMAC256(key, (keyId, height, root, H(body bytes)))`. -/
def checkpointMac (key : MacKey) (body : Body) (root : Digest) : List UInt8 :=
  kmac256Bytes key.bytes "DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1".toUTF8.toList
    (macInputStream.encode (body.keyId, body.height, root,
      cshake256Bytes "DREGG/NATIVE-HOST/CHECKPOINT-BODY/v1".toUTF8.toList
        (bodyStream.encode body)))

/-- Seal a checkpoint body under a supplied world root. The host supplies its
cached root (`DurableReceiverIO.sealCheckpoint_uses_cached_root`); `openSealed`
recomputes it from the body and refuses any other. -/
def sealAt (key : MacKey) (height : Nat) (chain : Digest) (frontier : List (Nat × Digest))
    (spentRoot : Digest) (state : State) (root : Digest) : Sealed :=
  let body : Body := ⟨key.id, height, chain, frontier, spentRoot, state⟩
  ⟨body, root, checkpointMac key body root⟩

/-- The specification seal: the root evaluated in full from the body. -/
def sealCheckpoint (key : MacKey) (rootBytes : List UInt8 → Digest) (height : Nat) (chain : Digest)
    (frontier : List (Nat × Digest)) (spentRoot : Digest) (state : State) : Sealed :=
  sealAt key height chain frontier spentRoot state
    (worldRoot rootBytes ⟨key.id, height, chain, frontier, spentRoot, state⟩)

/-- Sealing under any root equal to the body's world root is the
specification seal, byte for byte. -/
theorem sealAt_eq_sealCheckpoint (key : MacKey) (rootBytes : List UInt8 → Digest) (height : Nat)
    (chain : Digest) (frontier : List (Nat × Digest)) (spentRoot : Digest) (state : State)
    {root : Digest}
    (exact : root = worldRoot rootBytes ⟨key.id, height, chain, frontier, spentRoot, state⟩) :
    sealAt key height chain frontier spentRoot state root =
      sealCheckpoint key rootBytes height chain frontier spentRoot state := by
  subst exact
  rfl

inductive OpenError where
  | malformed
  | foreignKey
  | rootMismatch
  | badMac
  deriving DecidableEq, Repr

/-- Open a stored checkpoint: exact decode, this key, the recomputed world
root, and the MAC — in that order. Every failure refuses. -/
def openSealed (key : MacKey) (rootBytes : List UInt8 → Digest) (bytes : List UInt8) :
    Except OpenError Body := do
  let some sealed := checkpointFrame.decode bytes | throw .malformed
  unless sealed.body.keyId = key.id do throw .foreignKey
  unless sealed.root = worldRoot rootBytes sealed.body do throw .rootMismatch
  unless sealed.mac = checkpointMac key sealed.body sealed.root do throw .badMac
  pure sealed.body

/-- Satisfiable pole: what the host seals, it opens, exactly. -/
theorem openSealed_seal (key : MacKey) (rootBytes : List UInt8 → Digest) (height : Nat)
    (chain : Digest) (frontier : List (Nat × Digest)) (spentRoot : Digest) (state : State) :
    openSealed key rootBytes (checkpointFrame.encode
        (sealCheckpoint key rootBytes height chain frontier spentRoot state)) =
      .ok ⟨key.id, height, chain, frontier, spentRoot, state⟩ := by
  simp [openSealed, Framed.decode_encode, sealCheckpoint, sealAt]
  rfl

/-- Refuting pole: a decodable checkpoint whose MAC is not the key's MAC of
its body and root refuses, whatever else it carries. -/
theorem openSealed_bad_mac (key : MacKey) (rootBytes : List UInt8 → Digest)
    (sealed : Sealed) (forged : sealed.mac ≠ checkpointMac key sealed.body sealed.root) :
    ∃ reason, openSealed key rootBytes (checkpointFrame.encode sealed) = .error reason ∧
      reason ≠ .malformed := by
  unfold openSealed
  simp only [Framed.decode_encode]
  by_cases keyOk : sealed.body.keyId = key.id
  · by_cases rootOk : sealed.root = worldRoot rootBytes sealed.body
    · have forged' : sealed.mac ≠ checkpointMac key sealed.body
          (worldRoot rootBytes sealed.body) := rootOk ▸ forged
      refine ⟨.badMac, ?_, by decide⟩
      simp [keyOk, rootOk, forged']
      rfl
    · refine ⟨.rootMismatch, ?_, by decide⟩
      simp [keyOk, rootOk]
      rfl
  · refine ⟨.foreignKey, ?_, by decide⟩
    simp [keyOk]
    rfl

/-- The forgery premise is inhabited: an empty tag is never a KMAC tag. -/
theorem empty_mac_forged (key : MacKey) (body : Body) (root : Digest) :
    ([] : List UInt8) ≠ checkpointMac key body root := by
  intro same
  have := congrArg List.length same
  simp [checkpointMac, kmac256Bytes_length] at this

/-- A checkpoint sealed under one key and opened under a key with a different
id refuses. -/
theorem openSealed_foreign_key (key other : MacKey) (rootBytes : List UInt8 → Digest)
    (height : Nat) (chain : Digest) (frontier : List (Nat × Digest)) (spentRoot : Digest)
    (state : State) (distinct : other.id ≠ key.id) :
    openSealed key rootBytes (checkpointFrame.encode
        (sealCheckpoint other rootBytes height chain frontier spentRoot state)) =
      .error .foreignKey := by
  simp [openSealed, Framed.decode_encode, sealCheckpoint, sealAt, distinct]
  rfl

/-- info: 'Minidregg.Compiler.DurableCheckpointCodec.sealAt_eq_sealCheckpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sealAt_eq_sealCheckpoint

end Minidregg.Compiler.DurableCheckpointCodec
