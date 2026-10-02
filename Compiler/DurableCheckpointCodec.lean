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

def seedFrame : Framed Seed := ⟨"DREGG.DURABLE.SEED".toUTF8.toList ++ [1], seedStream⟩
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

theorem chainAfter_append (start : Digest) (left right : List IntentRecord) :
    chainAfter start (left ++ right) = chainAfter (chainAfter start left) right := by
  simp [chainAfter, List.foldl_append]

/-- The system slot's leaf: the height and the log root (C1's
`NativeHostCodec.Leaf.system`). -/
def systemLeaf (height : Nat) (chain : Digest) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.SYSTEM/v1".toUTF8.toList
    ((StreamCodec.product StreamCodec.nat digestStream).encode (height, chain))).digest

def tagInputStream : StreamCodec (List UInt8 × Nat × Digest) :=
  StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat digestStream)

def entryTag (key : MacKey) (height : Nat) (chain : Digest) : List UInt8 :=
  kmac256Bytes key.bytes "DREGG/NATIVE-HOST/LOG-TAG/v1".toUTF8.toList
    (tagInputStream.encode (key.id, height, chain))

/-! ## Checkpoints -/

def stateStream : StreamCodec State :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product (StreamCodec.list (StreamCodec.product digestStream bytesStream))
        (StreamCodec.product (StreamCodec.list nullifierStream) chargeStream)))
    (fun state => (state.absentBytes, state.cells, state.consumed, state.available))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; cases value; rfl)

/-- The authenticated content of a checkpoint. -/
structure Body where
  keyId : List UInt8
  height : Nat
  chain : Digest
  state : State

def bodyStream : StreamCodec Body :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream stateStream)))
    (fun body => (body.keyId, body.height, body.chain, body.state))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
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

def checkpointFrame : Framed Sealed :=
  ⟨"DREGG.DURABLE.CHECKPOINT".toUTF8.toList ++ [1], sealedStream⟩

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
def sealAt (key : MacKey) (height : Nat) (chain : Digest) (state : State) (root : Digest) : Sealed :=
  let body : Body := ⟨key.id, height, chain, state⟩
  ⟨body, root, checkpointMac key body root⟩

/-- The specification seal: the root evaluated in full from the body. -/
def sealCheckpoint (key : MacKey) (rootBytes : List UInt8 → Digest) (height : Nat) (chain : Digest)
    (state : State) : Sealed :=
  sealAt key height chain state (worldRoot rootBytes ⟨key.id, height, chain, state⟩)

/-- Sealing under any root equal to the body's world root is the
specification seal, byte for byte. -/
theorem sealAt_eq_sealCheckpoint (key : MacKey) (rootBytes : List UInt8 → Digest) (height : Nat)
    (chain : Digest) (state : State) {root : Digest}
    (exact : root = worldRoot rootBytes ⟨key.id, height, chain, state⟩) :
    sealAt key height chain state root = sealCheckpoint key rootBytes height chain state := by
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
    (chain : Digest) (state : State) :
    openSealed key rootBytes (checkpointFrame.encode (sealCheckpoint key rootBytes height chain state)) =
      .ok ⟨key.id, height, chain, state⟩ := by
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
    (height : Nat) (chain : Digest) (state : State) (distinct : other.id ≠ key.id) :
    openSealed key rootBytes (checkpointFrame.encode (sealCheckpoint other rootBytes height chain state)) =
      .error .foreignKey := by
  simp [openSealed, Framed.decode_encode, sealCheckpoint, sealAt, distinct]
  rfl

/-- info: 'Minidregg.Compiler.DurableCheckpointCodec.sealAt_eq_sealCheckpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sealAt_eq_sealCheckpoint

end Minidregg.Compiler.DurableCheckpointCodec
