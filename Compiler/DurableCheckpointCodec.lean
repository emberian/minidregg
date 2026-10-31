/-
# Compiler.DurableCheckpointCodec — the durable log, its MAC chain, and checkpoints

The host's durable store is three objects (the whole-image `DREGG.DURABLE.IMAGE`
record is gone):

* the **seed**, written once at bootstrap (`DREGG.DURABLE.SEED/v1`);
* the **log**: entry `h` (1-based) is one accepted record (`DREGG.DURABLE.LOG`, frame byte 4: the record, its signing subject and its meter credit)
  and a 32-byte tag. The log is chained by C1's log root: `chain₀ = logStart seed`
  (the host passes `NativeHostCodec.logRoot0 domain semantics`), and
  `chainₕ = Kernel.WorldRoot.chainDigest chainₕ₋₁ (recordDigest recordₕ)`; the tag of
  entry `h` is `KMAC256(key, (keyId, h, chainₕ))`. One chain: the value the
  world root's system slot commits to is the value the MAC authenticates;
* **checkpoints** (`DREGG.DURABLE.CHECKPOINT/v1`): the materialized state at a
  height, its world root, the log chain at that height, and
  `KMAC256(key, (keyId, height, root, H(body bytes)))`.

**MAC custody (docs/DATAMODEL.md §6 Q1).** The key is 32 bytes generated at
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

The world root is the parameterised `Checkpoint.check` of docs/DATAMODEL.md §5 B2 over
the current cell-root function (`rootBytes`), until C1 supplies the world-root
function; it is recomputed from the checkpoint's cells, never trusted.
-/
module

public import Compiler.PersistedCodecTags.Core
-- The census, privately: only `persistedCodecCorpus`'s unexposed body reads it, so a census
-- edit changes no public interface of this module and rebuilds none of its importers.
import Compiler.PersistedCodecTags
public import Compiler.CanonicalCellRegistry
public import Compiler.DurableReceiverCodec
public import Compiler.Sp800185Cshake256
public import Compiler.Sp800185Kmac256
public import Kernel.DurableCheckpoint
public import Kernel.WorldRootCache
public import Kernel.WorldSystemCodec
public import Theory.AssertAxioms
public import Theory.AssertCompiled
meta import Compiler.PersistedCodecTags
meta import Compiler.PersistedCodecTags.Core
meta import Compiler.CanonicalCellRegistry
meta import Compiler.DurableReceiverCodec
meta import Compiler.Sp800185Cshake256
meta import Compiler.Sp800185Kmac256
meta import Kernel.DurableCheckpoint
meta import Kernel.WorldRootCache
meta import Kernel.WorldSystemCodec
meta import Theory.AssertAxioms
meta import Theory.AssertCompiled

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
meta import Compiler.PersistedCodecTagRegistry

@[expose] public section

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

/-- A fixed frame (length-prefixed) followed by one stream value.  The frame is
CHECKED by the stream (`StreamCodec.framed`), and the stream is canonical, so a
decode accepts exactly the encodings (`decode_canonical`): no aliases, no
trailing bytes, no re-encode. -/
structure Framed (α : Type) where
  frame : List UInt8
  stream : StreamCodec α

namespace Framed

variable {α : Type}

/-- The checked frame octets, then the value. -/
def codec (framed : Framed α) : StreamCodec α :=
  StreamCodec.framed (bytesStream.encode framed.frame) framed.stream

def encode (framed : Framed α) (value : α) : List UInt8 :=
  framed.codec.encode value

theorem encode_eq (framed : Framed α) (value : α) :
    framed.encode value = bytesStream.encode framed.frame ++ framed.stream.encode value := rfl

def decode (framed : Framed α) (bytes : List UInt8) : Option α :=
  framed.codec.toLawful.decode bytes

theorem decode_encode (framed : Framed α) (value : α) :
    framed.decode (framed.encode value) = some value :=
  framed.codec.toLawful.decode_encode value

theorem decode_canonical (framed : Framed α) {bytes : List UInt8} {value : α}
    (decoded : framed.decode bytes = some value) : framed.encode value = bytes :=
  framed.codec.toLawful_canonical bytes value decoded

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
      rw [← encode_eq, exact, bytesStream.decodePrefix_encode] at prefixed
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
def logTagLabel : String := Minidregg.Compiler.PersistedCodecTags.native_host_log_tag_v4

/-- One Store epoch: the format components its bytes commit to. -/
structure StoreEpoch where
  stateKey : String
  schemaRefs : String
  logTag : String
  /-- The history accumulator and the index trie (`Compiler.DurableHistory`,
  `Compiler.DurableIndex`, KN2-STORE-OPEN). `index/trie-v1` replaced the separate
  spent map (`spent/trie-v1`): a Store born with it is refused naming this
  component. A three-component label (an epoch
  born before it) reads as `none` and is refused by naming this component. -/
  accumulator : String
  /-- The command codecs of the log records. `commands/v2`: the delegation
  command no longer signs the authority-cell root
  (`CapabilityDelegationController.commandFrame` v2). A label without it (an
  epoch born before it) reads as `none` and is refused by naming it. -/
  commands : String
  deriving DecidableEq, Repr

/-- Enumerate the actual receiving registry's byte tags, never a parallel list
of kinds. `kindAtTag_tag` ensures every kind appears at its own UInt8 tag. The
descriptor includes namespace tags, key/value codec IDs and the blinding slot. -/
def persistedCellDescriptors : List (Nat × Nat × Nat × List UInt8) :=
  (List.range 256).filterMap fun tag => do
    let kind ← CanonicalCellRegistry.kindAtTag (UInt8.ofNat tag)
    let schema := CanonicalCellRegistry.schemaRef kind
    let descriptor := match CanonicalCellRegistry.wire? kind with
      | some wire => StoreCodec.descriptor wire
      | none => []
    pure (tag, schema.schemaId.value, schema.version, descriptor)

/-- Canonical, length-prefixed receiving identities and actual cell layout
descriptors. Implementation bodies and proof terms are not persisted formats.
Unexposed: its body is the only reader of the census (`Compiler.PersistedCodecTags`),
which this module imports privately. -/
@[no_expose] def persistedCodecCorpus : List UInt8 :=
  let entries := PersistedCodecTags.canonicalSet (PersistedCodecTags.entries.map (·.bytes))
  (StreamCodec.product (StreamCodec.list bytesStream)
    (StreamCodec.list (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat bytesStream))))).encode
    (entries, persistedCellDescriptors)

/-- The content of the persisted identities and cell descriptors. Removing the
implementation fingerprints changes this corpus once; old Stores refuse through
`SeedEpoch.refusalFor`, before their log records are decoded. -/
def persistedSchemaRefs : String :=
  s!"schema-refs/{(Sp800185Cshake256.hash
    "MINI.PERSISTED-CODEC-CORPUS/v1".toUTF8.toList persistedCodecCorpus).digest.value}"

/-- The epoch this Host writes and reads, including the cell layout descriptors. -/
def StoreEpoch.current : StoreEpoch :=
  ⟨DeclaredEffectCell.stateKeyCodecId, persistedSchemaRefs, logTagLabel,
    "history/mmr-v1;index/trie-v1;checkpoint/v5", "commands/v2"⟩

/-- The label carried in the seed frame: every component, `;`-separated (the
accumulator is itself two parts, `history/…;spent/…`). -/
def StoreEpoch.label (epoch : StoreEpoch) : String :=
  s!"{epoch.stateKey};{epoch.schemaRefs};{epoch.logTag};{epoch.accumulator};{epoch.commands}"

/-- A label part's name: everything before its last `/`
(`DREGG/NATIVE-HOST/LOG-TAG/v4` is named `DREGG/NATIVE-HOST/LOG-TAG`). -/
def StoreEpoch.partName (part : String) : String :=
  "/".intercalate (part.splitOn "/").dropLast

/-- The accumulator's own parts, in label order (`Compiler.DurableHistory`,
the retired spent map, `Compiler.DurableIndex`, and the checkpoint shape of
KN2-STORE-OPEN). `spent` stays a KNOWN name so that a Store born with the
retired spent map parses and is refused naming the accumulator, rather than
failing as an unreadable label. -/
def StoreEpoch.accumulatorParts : List String := ["history", "spent", "index", "checkpoint"]

/-- Every part name a label may carry, in label order. -/
def StoreEpoch.partNames : List String :=
  ["state-key", "schema-refs", Minidregg.Compiler.PersistedCodecTags.prefix_native_host_log_tag] ++ StoreEpoch.accumulatorParts ++ ["commands"]

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
        StoreEpoch.partNamed parts Minidregg.Compiler.PersistedCodecTags.prefix_native_host_log_tag with
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

def seedFrameName : List UInt8 := Minidregg.Compiler.PersistedCodecTags.durable_seed.toUTF8.toList

/-- Seed frame v3: the name, version byte 3, then the epoch label. The v1 frame
(name and byte 1) carried no epoch, so a v1 Store's components are unknown (it
may be of any earlier epoch, including this one's components): it refuses as
unlabelled. A v2 frame (labelled, but its seed codec nests the cell codecs from
before the Book's floors section) refuses as retired, whatever its label says. -/
def seedFrameFor (epoch : StoreEpoch) : Framed Seed :=
  ⟨seedFrameName ++ [UInt8.ofNat PersistedCodecTags.seedWireVersion] ++ epoch.label.toUTF8.toList, seedStream⟩

def seedFrame : Framed Seed := seedFrameFor StoreEpoch.current

/-- What a Store's seed bytes say about its epoch, read from the frame alone. -/
inductive SeedEpoch where
  | labelled (epoch : StoreEpoch)
  | unlabelled (version : UInt8)
  | retired (version : UInt8)
  | foreign

def SeedEpoch.ofBytesFor (host : StoreEpoch) (bytes : List UInt8) : SeedEpoch :=
  match bytesStream.decodePrefix bytes with
  | none => .foreign
  | some (frame, _) =>
      if frame = (seedFrameFor host).frame then .labelled host
      else if frame.take seedFrameName.length = seedFrameName then
        match frame.drop seedFrameName.length with
        | [version] => .unlabelled version
        | version :: label =>
            if version = UInt8.ofNat PersistedCodecTags.seedWireVersion then
              match String.fromUTF8? label.toByteArray >>= StoreEpoch.parse with
              | some epoch => .labelled epoch
              | none => .foreign
            else .retired version
        | _ => .foreign
      else .foreign

def SeedEpoch.ofBytes (bytes : List UInt8) : SeedEpoch :=
  SeedEpoch.ofBytesFor StoreEpoch.current bytes

/-- The refusal naming a Store's epoch, or `none` when it is this Host's. -/
def SeedEpoch.refusalFor (host : StoreEpoch) : SeedEpoch → Option String
  | .labelled epoch =>
      match epoch.differing host with
      | [] => none
      | named => some s!"this Store was born in another epoch ({String.intercalate "; " named}); re-genesis the world"
  | .unlabelled version =>
      some s!"this Store's seed frame is version {version}, which carries no epoch label (it was born before Store epochs were labelled, so its state-key codec, schema references and log tags are unknown); this Host reads {host.label}; re-genesis the world"
  | .retired version =>
      some s!"this Store's seed frame is version {version}, retired: this Host reads seed frame version {PersistedCodecTags.seedWireVersion} ({host.label}), and a retired frame's seed codec is never reinterpreted; re-genesis the world"
  | .foreign => some "the Store's seed is not a durable seed frame"

def SeedEpoch.refusal (epoch : SeedEpoch) : Option String :=
  epoch.refusalFor StoreEpoch.current

/-- Prove the frame round trip with an arbitrary epoch, so kernel equality
checking never needs to normalize the concrete corpus digest. -/
theorem seedEpoch_ofBytes_forCurrent (epoch : StoreEpoch) (rest : List UInt8) :
    SeedEpoch.ofBytesFor epoch (bytesStream.encode (seedFrameFor epoch).frame ++ rest) =
      .labelled epoch := by
  unfold SeedEpoch.ofBytesFor
  rw [bytesStream.decodePrefix_encode]
  exact if_pos rfl

/-- The current seed frame reads back as this Host's labelled epoch. -/
theorem seedEpoch_ofBytes_current (rest : List UInt8) :
    SeedEpoch.ofBytes (bytesStream.encode seedFrame.frame ++ rest) =
      .labelled StoreEpoch.current := by
  exact seedEpoch_ofBytes_forCurrent StoreEpoch.current rest

/-- The host's own seed passes for any epoch, without normalizing a digest. -/
theorem seedEpoch_currentFor (host : StoreEpoch) (seed : Seed) :
    (SeedEpoch.ofBytesFor host ((seedFrameFor host).encode seed)).refusalFor host = none := by
  show (SeedEpoch.ofBytesFor host
    (bytesStream.encode (seedFrameFor host).frame ++ seedStream.encode seed)).refusalFor host = none
  rw [seedEpoch_ofBytes_forCurrent]
  simp [SeedEpoch.refusalFor, (StoreEpoch.differing_nil_iff _ _).mpr rfl]

/-- **This Host's own seeds pass the epoch check.** -/
theorem seedEpoch_current (seed : Seed) :
    (SeedEpoch.ofBytes (seedFrame.encode seed)).refusal = none :=
  seedEpoch_currentFor StoreEpoch.current seed

/-- The unlabelled v1 frame refuses under every host epoch. -/
theorem seedEpoch_v1_refusedFor (host : StoreEpoch) (rest : List UInt8) :
    ∃ named, (SeedEpoch.ofBytesFor host (bytesStream.encode (seedFrameName ++ [1]) ++ rest)).refusalFor host =
      some named := by
  have older : seedFrameName ++ [1] ≠ (seedFrameFor host).frame := by
    intro same
    have tails := List.append_cancel_left
      (same.trans (by simp [seedFrameFor, List.append_assoc]) :
      seedFrameName ++ [1] = seedFrameName ++ (UInt8.ofNat PersistedCodecTags.seedWireVersion :: host.label.toUTF8.toList))
    simp [PersistedCodecTags.seedWireVersion] at tails
  unfold SeedEpoch.ofBytesFor
  rw [bytesStream.decodePrefix_encode]
  simp only [older, if_false, List.take_left, List.drop_left, if_true]
  exact ⟨_, rfl⟩

/-- **Every v2 Store refuses by name**, whatever label it carries: its seed
codec predates the Book's floors section, and a retired frame is not read as a
labelled epoch. -/
theorem seedEpoch_v2_refusedFor (host : StoreEpoch) (label rest : List UInt8) :
    ∃ named, (SeedEpoch.ofBytesFor host (bytesStream.encode (seedFrameName ++ 2 :: label) ++ rest)).refusalFor host =
      some named := by
  have notCurrent : seedFrameName ++ 2 :: label ≠ (seedFrameFor host).frame := by
    intro same
    have tails := List.append_cancel_left
      (same.trans (by simp [seedFrameFor, List.append_assoc]) :
      seedFrameName ++ 2 :: label = seedFrameName ++ (UInt8.ofNat PersistedCodecTags.seedWireVersion :: host.label.toUTF8.toList))
    simp [PersistedCodecTags.seedWireVersion] at tails
  unfold SeedEpoch.ofBytesFor
  rw [bytesStream.decodePrefix_encode]
  simp only [notCurrent, if_false, List.take_left, List.drop_left, if_true]
  cases label with
  | nil => exact ⟨_, rfl⟩
  | cons byte bytes =>
      simp only [PersistedCodecTags.seedWireVersion]
      exact ⟨_, rfl⟩

theorem seedEpoch_v2_refused (label rest : List UInt8) :
    ∃ named, (SeedEpoch.ofBytes (bytesStream.encode (seedFrameName ++ 2 :: label) ++ rest)).refusal =
      some named := seedEpoch_v2_refusedFor StoreEpoch.current label rest

/-- **Every v3 Store refuses by name**, whatever label it carries: its registry predates
the platform cell kind (loaded-law label `STORE-CELLS/v17`), and a retired frame is not
read as a labelled epoch. -/
theorem seedEpoch_v3_refusedFor (host : StoreEpoch) (label rest : List UInt8) :
    ∃ named, (SeedEpoch.ofBytesFor host (bytesStream.encode (seedFrameName ++ 3 :: label) ++ rest)).refusalFor host =
      some named := by
  have notCurrent : seedFrameName ++ 3 :: label ≠ (seedFrameFor host).frame := by
    intro same
    have tails := List.append_cancel_left
      (same.trans (by simp [seedFrameFor, List.append_assoc]) :
      seedFrameName ++ 3 :: label = seedFrameName ++ (UInt8.ofNat PersistedCodecTags.seedWireVersion :: host.label.toUTF8.toList))
    simp [PersistedCodecTags.seedWireVersion] at tails
  unfold SeedEpoch.ofBytesFor
  rw [bytesStream.decodePrefix_encode]
  simp only [notCurrent, if_false, List.take_left, List.drop_left, if_true]
  cases label with
  | nil => exact ⟨_, rfl⟩
  | cons byte bytes =>
      simp only [PersistedCodecTags.seedWireVersion]
      exact ⟨_, rfl⟩

theorem seedEpoch_v3_refused (label rest : List UInt8) :
    ∃ named, (SeedEpoch.ofBytes (bytesStream.encode (seedFrameName ++ 3 :: label) ++ rest)).refusal =
      some named := seedEpoch_v3_refusedFor StoreEpoch.current label rest

/-- **Every v4 Store refuses by name**, whatever label it carries: its seed predates
the structure re-emitted with seed frame version 5, and a retired frame is not read as a
labelled epoch. -/
theorem seedEpoch_v4_refusedFor (host : StoreEpoch) (label rest : List UInt8) :
    ∃ named, (SeedEpoch.ofBytesFor host (bytesStream.encode (seedFrameName ++ 4 :: label) ++ rest)).refusalFor host =
      some named := by
  have notCurrent : seedFrameName ++ 4 :: label ≠ (seedFrameFor host).frame := by
    intro same
    have tails := List.append_cancel_left
      (same.trans (by simp [seedFrameFor, List.append_assoc]) :
      seedFrameName ++ 4 :: label = seedFrameName ++ (UInt8.ofNat PersistedCodecTags.seedWireVersion :: host.label.toUTF8.toList))
    simp [PersistedCodecTags.seedWireVersion] at tails
  unfold SeedEpoch.ofBytesFor
  rw [bytesStream.decodePrefix_encode]
  simp only [notCurrent, if_false, List.take_left, List.drop_left, if_true]
  cases label with
  | nil => exact ⟨_, rfl⟩
  | cons byte bytes =>
      simp only [PersistedCodecTags.seedWireVersion]
      exact ⟨_, rfl⟩

theorem seedEpoch_v4_refused (label rest : List UInt8) :
    ∃ named, (SeedEpoch.ofBytes (bytesStream.encode (seedFrameName ++ 4 :: label) ++ rest)).refusal =
      some named := seedEpoch_v4_refusedFor StoreEpoch.current label rest

/-- **Every v1 Store refuses by name**: its frame carries no epoch. -/
theorem seedEpoch_v1_refused (rest : List UInt8) :
    ∃ named, (SeedEpoch.ofBytes (bytesStream.encode (seedFrameName ++ [1]) ++ rest)).refusal =
      some named := seedEpoch_v1_refusedFor StoreEpoch.current rest

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
def labelledFrame (label : String) : List UInt8 :=
  seedFrameName ++ UInt8.ofNat PersistedCodecTags.seedWireVersion :: label.toUTF8.toList

/-- The refusal for a Store labelled `label`, which `SeedEpoch.ofBytes` reads
from its frame alone (whatever follows). -/
theorem seedEpoch_ofBytes_labelled (label : String) (rest : List UInt8) :
    SeedEpoch.ofBytes (bytesStream.encode (labelledFrame label) ++ rest) =
      SeedEpoch.ofBytes (bytesStream.encode (labelledFrame label)) := by
  unfold SeedEpoch.ofBytes SeedEpoch.ofBytesFor
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
      some s!"this Store was born in another epoch (history accumulator: Store none, this Host {StoreEpoch.current.accumulator}); re-genesis the world" := by
  rw [seedEpoch_ofBytes_labelled]
  native_decide

/-- The label of the epoch before the unified index (separate spent map, v3 tags, checkpoint v3). -/
def labelSpentMap : String :=
  "state-key/tagged-v4;schema-refs/v5;DREGG/NATIVE-HOST/LOG-TAG/v3;history/mmr-v1;spent/trie-v1;checkpoint/v3;commands/v2"

/-- **A Store of the separate spent map is refused by name** (log tags and the
accumulator), never read as this Host's. -/
theorem seedEpoch_spentMap_refused (rest : List UInt8) :
    (SeedEpoch.ofBytes (bytesStream.encode (labelledFrame labelSpentMap) ++ rest)).refusal =
      some s!"this Store was born in another epoch (cell schema references: Store schema-refs/v5, this Host {persistedSchemaRefs}; log tags: Store DREGG/NATIVE-HOST/LOG-TAG/v3, this Host {logTagLabel}; history accumulator: Store history/mmr-v1;spent/trie-v1;checkpoint/v3, this Host {StoreEpoch.current.accumulator}); re-genesis the world" := by
  rw [seedEpoch_ofBytes_labelled]
  native_decide

#assert_compiled seedEpoch_spentMap_refused
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
#assert_axioms seedEpoch_ofBytes_forCurrent
#assert_axioms seedEpoch_currentFor
#assert_axioms seedEpoch_v2_refusedFor
#assert_axioms seedEpoch_v2_refused
#assert_axioms seedEpoch_v3_refusedFor
#assert_axioms seedEpoch_v3_refused
#assert_axioms seedEpoch_v4_refusedFor
#assert_axioms seedEpoch_v4_refused
#assert_axioms seedEpoch_v1_refusedFor
#assert_axioms seedEpoch_v1_refused
/-- Frame byte 4: a record carries its signing subject (`IntentRecord.subject`, which the
presence index folds) and its meter credit (`IntentRecord.credit`, the seed-meter refill's).
Bytes 1-3 refuse (`v1_record_refused`, `v2_record_refused`, `v3_record_refused`; byte 3 is
the subject-only record of the A11 regen). -/
def recordFrame : Framed IntentRecord := ⟨Minidregg.Compiler.PersistedCodecTags.durable_log_byte_v4, intentStream⟩

def retiredRecordFrameV3 : List UInt8 := "DREGG.DURABLE.LOG".toUTF8.toList ++ [3]

theorem v3_record_refused (tail : List UInt8) :
    recordFrame.decode (bytesStream.encode retiredRecordFrameV3 ++ tail) = none :=
  Framed.decode_other_frame recordFrame (by decide +kernel) tail

def retiredRecordFrameV1 : List UInt8 := "DREGG.DURABLE.LOG".toUTF8.toList ++ [1]

def retiredRecordFrameV2 : List UInt8 := "DREGG.DURABLE.LOG".toUTF8.toList ++ [2]

theorem v2_record_refused (tail : List UInt8) :
    recordFrame.decode (bytesStream.encode retiredRecordFrameV2 ++ tail) = none :=
  Framed.decode_other_frame recordFrame (by decide +kernel) tail

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
  rw [← canonical, Framed.encode_eq]
  simp [recordFrame]

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
  (Sp800185Cshake256.hash Minidregg.Compiler.PersistedCodecTags.native_host_system_v1.toUTF8.toList
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
  /-- The index trie's root after `height` records (`DurableIndex`). -/
  indexRoot : Digest
  state : State
  /-- The fold's World's system store at `height` (journal, head, retired, parent, spent,
  allowance; `Kernel.WorldSystemCodec`); its cells are `state`'s, decoded. `none` when the
  sealing session's World was lost: the open then folds from genesis. -/
  system : Option (Minidregg.Theory.Store.Store Kernel.WorldSystemCodec.DSys)
  /-- The identity of the fold that produced `system` (`foldSemantics`): a body sealed by
  another fold under the same Store key is refused by name (`OpenError.foreignSemantics`). -/
  semantics : Digest

def frontierStream : StreamCodec (List (Nat × Digest)) :=
  StreamCodec.list (StreamCodec.product StreamCodec.nat digestStream)

def bodyStream : StreamCodec Body :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream
        (StreamCodec.product frontierStream (StreamCodec.product digestStream
          (StreamCodec.product stateStream
            (StreamCodec.product (StreamCodec.option Kernel.WorldSystemCodec.systemStream)
              digestStream)))))))
    (fun body => (body.keyId, body.height, body.chain, body.frontier, body.indexRoot, body.state,
      body.system, body.semantics))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2.1, tuple.2.2.2.2.2.1,
      tuple.2.2.2.2.2.2.1, tuple.2.2.2.2.2.2.2⟩)
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

/-- v4: the body carries the fold's World's system store and the fold's semantics
(HOT-PATH §2(h)), beside v3's accumulator frontier and spent root. An older checkpoint
refuses (`malformed`): its frame differs; the Store epoch (`StoreEpoch.accumulator`,
`checkpoint/v5`) names the change. -/
def checkpointFrame : Framed Sealed :=
  ⟨Minidregg.Compiler.PersistedCodecTags.durable_checkpoint_byte_v4, sealedStream⟩

def macInputStream : StreamCodec (List UInt8 × Nat × Digest × List UInt8) :=
  StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream bytesStream))

/-- `KMAC256(key, (keyId, height, root, H(body bytes)))`. -/
def checkpointMac (key : MacKey) (body : Body) (root : Digest) : List UInt8 :=
  kmac256Bytes key.bytes "DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1".toUTF8.toList
    (macInputStream.encode (body.keyId, body.height, root,
      cshake256Bytes "DREGG/NATIVE-HOST/CHECKPOINT-BODY/v1".toUTF8.toList
        (bodyStream.encode body)))

/-- The fold's version: bumped whenever `DurableReceiverIO.foldRecords`' World semantics (the
turn derivation, `admit`, the system rows it writes) change, so a checkpoint's World sealed by
another fold is refused by name rather than trusted. -/
def foldVersion : String := "FOLD/turn-of-intent-v1"

/-- The fold's identity a v4 body carries: the epoch (every persisted codec and layout) and the
fold's version. -/
def foldSemantics : Digest :=
  (Sp800185Cshake256.hash "DREGG/NATIVE-HOST/FOLD-SEMANTICS/v1".toUTF8.toList
    (StoreEpoch.current.label ++ ";" ++ foldVersion).toUTF8.toList).digest

/-- Seal a checkpoint body under a supplied world root. The host supplies its
cached root (`DurableReceiverIO.sealCheckpoint_uses_cached_root`); `openSealed`
recomputes it from the body and refuses any other. -/
def sealAt (key : MacKey) (height : Nat) (chain : Digest) (frontier : List (Nat × Digest))
    (indexRoot : Digest) (state : State) (system : Option (Minidregg.Theory.Store.Store Kernel.WorldSystemCodec.DSys))
    (root : Digest) : Sealed :=
  let body : Body := ⟨key.id, height, chain, frontier, indexRoot, state, system, foldSemantics⟩
  ⟨body, root, checkpointMac key body root⟩

/-- The specification seal: the root evaluated in full from the body. -/
def sealCheckpoint (key : MacKey) (rootBytes : List UInt8 → Digest) (height : Nat) (chain : Digest)
    (frontier : List (Nat × Digest)) (indexRoot : Digest) (state : State)
    (system : Option (Minidregg.Theory.Store.Store Kernel.WorldSystemCodec.DSys)) : Sealed :=
  sealAt key height chain frontier indexRoot state system
    (worldRoot rootBytes ⟨key.id, height, chain, frontier, indexRoot, state, system, foldSemantics⟩)

/-- Sealing under any root equal to the body's world root is the
specification seal, byte for byte. -/
theorem sealAt_eq_sealCheckpoint (key : MacKey) (rootBytes : List UInt8 → Digest) (height : Nat)
    (chain : Digest) (frontier : List (Nat × Digest)) (indexRoot : Digest) (state : State)
    (system : Option (Minidregg.Theory.Store.Store Kernel.WorldSystemCodec.DSys)) {root : Digest}
    (exact : root = worldRoot rootBytes
      ⟨key.id, height, chain, frontier, indexRoot, state, system, foldSemantics⟩) :
    sealAt key height chain frontier indexRoot state system root =
      sealCheckpoint key rootBytes height chain frontier indexRoot state system := by
  subst exact
  rfl

inductive OpenError where
  | malformed
  | foreignKey
  | foreignSemantics
  | rootMismatch
  | badMac
  deriving DecidableEq, Repr

/-- Open a stored checkpoint: exact decode, this key, the recomputed world
root, and the MAC — in that order. Every failure refuses. -/
def openSealed (key : MacKey) (rootBytes : List UInt8 → Digest) (bytes : List UInt8) :
    Except OpenError Body := do
  let some sealed := checkpointFrame.decode bytes | throw .malformed
  unless sealed.body.keyId = key.id do throw .foreignKey
  unless sealed.body.semantics = foldSemantics do throw .foreignSemantics
  unless sealed.root = worldRoot rootBytes sealed.body do throw .rootMismatch
  unless sealed.mac = checkpointMac key sealed.body sealed.root do throw .badMac
  pure sealed.body

/-- `openSealed` with the world-root evaluation handed to the caller: `derive`
evaluates something from which `rootOf` reads the body's world root (`exact`);
the open compares the sealed root against it and returns it beside the body, so
a caller that needs the evaluated tree (`DurableServed.openHead`) does not
evaluate the root a second time. The checks and their order are `openSealed`'s
(`openSealedWith_fst`). -/
def openSealedWith {α : Body → Type} (key : MacKey) (rootBytes : List UInt8 → Digest)
    (bytes : List UInt8) (derive : (body : Body) → α body) (rootOf : (body : Body) → α body → Digest)
    (_exact : ∀ body, rootOf body (derive body) = worldRoot rootBytes body) :
    Except OpenError ((body : Body) × α body) := do
  let some sealed := checkpointFrame.decode bytes | throw .malformed
  unless sealed.body.keyId = key.id do throw .foreignKey
  unless sealed.body.semantics = foldSemantics do throw .foreignSemantics
  let derived := derive sealed.body
  unless sealed.root = rootOf sealed.body derived do throw .rootMismatch
  unless sealed.mac = checkpointMac key sealed.body sealed.root do throw .badMac
  pure ⟨sealed.body, derived⟩

/-- **The cached open is the open**: same refusals, same body. -/
theorem openSealedWith_fst {α : Body → Type} (key : MacKey) (rootBytes : List UInt8 → Digest)
    (bytes : List UInt8) (derive : (body : Body) → α body) (rootOf : (body : Body) → α body → Digest)
    (exact : ∀ body, rootOf body (derive body) = worldRoot rootBytes body) :
    (openSealedWith key rootBytes bytes derive rootOf exact).map Sigma.fst =
      openSealed key rootBytes bytes := by
  unfold openSealedWith openSealed
  cases checkpointFrame.decode bytes with
  | none => rfl
  | some sealed =>
      simp only [exact]
      by_cases keyOk : sealed.body.keyId = key.id
      · by_cases semOk : sealed.body.semantics = foldSemantics
        · by_cases rootOk : sealed.root = worldRoot rootBytes sealed.body
          · by_cases macOk : sealed.mac = checkpointMac key sealed.body (worldRoot rootBytes sealed.body) <;>
              simp [keyOk, semOk, rootOk, macOk] <;> rfl
          · simp [keyOk, semOk, rootOk]
            rfl
        · simp [keyOk, semOk]
          rfl
      · simp [keyOk]
        rfl

#assert_axioms openSealedWith_fst

/-- **The cached open is the open, paired**: `openSealed` with the derived value
of the body beside it. -/
theorem openSealedWith_eq {α : Body → Type} (key : MacKey) (rootBytes : List UInt8 → Digest)
    (bytes : List UInt8) (derive : (body : Body) → α body) (rootOf : (body : Body) → α body → Digest)
    (exact : ∀ body, rootOf body (derive body) = worldRoot rootBytes body) :
    openSealedWith key rootBytes bytes derive rootOf exact =
      (fun body => (⟨body, derive body⟩ : (body : Body) × α body)) <$> openSealed key rootBytes bytes := by
  unfold openSealedWith openSealed
  cases checkpointFrame.decode bytes with
  | none => rfl
  | some sealed =>
      simp only [exact]
      by_cases keyOk : sealed.body.keyId = key.id
      · by_cases semOk : sealed.body.semantics = foldSemantics
        · by_cases rootOk : sealed.root = worldRoot rootBytes sealed.body
          · by_cases macOk : sealed.mac = checkpointMac key sealed.body (worldRoot rootBytes sealed.body) <;>
              simp [keyOk, semOk, rootOk, macOk]
          · simp [keyOk, semOk, rootOk]
            rfl
        · simp [keyOk, semOk]
          rfl
      · simp [keyOk]
        rfl

/-- What an accepted cached open hands back: the body `openSealed` accepts, and
a derived value whose root is that body's world root. -/
theorem openSealedWith_ok {α : Body → Type} {key : MacKey} {rootBytes : List UInt8 → Digest}
    {bytes : List UInt8} {derive : (body : Body) → α body} {rootOf : (body : Body) → α body → Digest}
    {exact : ∀ body, rootOf body (derive body) = worldRoot rootBytes body} {body : Body} {derived : α body}
    (opened : openSealedWith key rootBytes bytes derive rootOf exact = .ok ⟨body, derived⟩) :
    openSealed key rootBytes bytes = .ok body ∧ rootOf body derived = worldRoot rootBytes body := by
  rw [openSealedWith_eq] at opened
  cases plain : openSealed key rootBytes bytes with
  | error reason => rw [plain] at opened; cases opened
  | ok found =>
      rw [plain] at opened
      cases opened
      exact ⟨rfl, exact _⟩

#assert_axioms openSealedWith_eq
#assert_axioms openSealedWith_ok

/-- Satisfiable pole: what the host seals, it opens, exactly. -/
theorem openSealed_seal (key : MacKey) (rootBytes : List UInt8 → Digest) (height : Nat)
    (chain : Digest) (frontier : List (Nat × Digest)) (indexRoot : Digest) (state : State)
    (system : Option (Minidregg.Theory.Store.Store Kernel.WorldSystemCodec.DSys)) :
    openSealed key rootBytes (checkpointFrame.encode
        (sealCheckpoint key rootBytes height chain frontier indexRoot state system)) =
      .ok ⟨key.id, height, chain, frontier, indexRoot, state, system, foldSemantics⟩ := by
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
  · by_cases semOk : sealed.body.semantics = foldSemantics
    · by_cases rootOk : sealed.root = worldRoot rootBytes sealed.body
      · have forged' : sealed.mac ≠ checkpointMac key sealed.body
            (worldRoot rootBytes sealed.body) := rootOk ▸ forged
        refine ⟨.badMac, ?_, by decide⟩
        simp [keyOk, semOk, rootOk, forged']
        rfl
      · refine ⟨.rootMismatch, ?_, by decide⟩
        simp [keyOk, semOk, rootOk]
        rfl
    · refine ⟨.foreignSemantics, ?_, by decide⟩
      simp [keyOk, semOk]
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
    (height : Nat) (chain : Digest) (frontier : List (Nat × Digest)) (indexRoot : Digest)
    (state : State) (system : Option (Minidregg.Theory.Store.Store Kernel.WorldSystemCodec.DSys))
    (distinct : other.id ≠ key.id) :
    openSealed key rootBytes (checkpointFrame.encode
        (sealCheckpoint other rootBytes height chain frontier indexRoot state system)) =
      .error .foreignKey := by
  simp [openSealed, Framed.decode_encode, sealCheckpoint, sealAt, distinct]
  rfl

/-- info: 'Minidregg.Compiler.DurableCheckpointCodec.sealAt_eq_sealCheckpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sealAt_eq_sealCheckpoint

end Minidregg.Compiler.DurableCheckpointCodec
