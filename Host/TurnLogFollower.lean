/- The Turn-log follower (FD-1, R4a).

`turn-log-follower export CONFIG OUT` (the exporter, one process): open the Store
named by a client settings file, build the deployed genesis World of its seed,
and for every accepted record derive the Turn against the current World
(`Turn.ofIntent`), admit it (`World.admit`), and write it with digest guards
(`DeployedTurnCompact.encodeTurnAt`, against the World it is admitted at).  It then
checks the World against the Store it read: every cell's bytes, every spent
nullifier, the height.  It writes `OUT/genesis.bin`, `OUT/turns.bin`, `OUT/root`.

`turn-log-follower follow OUT [--plant-drop K]` (the follower, a second process): reads only
`genesis.bin` and `turns.bin` (no post image, no Store), folds the decoded turns
(`TurnLog.followFrom`, which IS `World.fold`), and prints `ROOT <digest>`; a
tampered entry stops it as `STOP undecodable|refused <height>`. -/
import Host.ClientConsentCore
import Kernel.TurnLog

namespace Minidregg.Host.TurnLogFollower

open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.World
open Minidregg.Kernel.TurnLog
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

/-- Where a turn's bytes go: read ops, write ops, allocate/free ops, born images. -/
def breakdown (t : TurnOfIntent.DTurn deployedR Digest) : Nat × Nat × Nat × Nat :=
  t.legs.foldl (fun acc leg => leg.patch.foldl (fun (r, w, a, i) op =>
    let n := (DeployedHistory.encodeOp leg.kind op).length
    match op with
    | .read _ _ _ => (r + n, w, a, i)
    | .write _ _ _ _ => (r, w + n, a, i)
    | _ => (r, w, a + n, i)) acc)
    (0, 0, 0, (t.creates.map fun c => (encodeCell (some c.2.1)).length).sum)

/-- The genesis file: the seed (absent bytes, cells, allowance). -/
def seedStream : StreamCodec DurableReceiver.Seed :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product (StreamCodec.list (StreamCodec.product digestStream bytesStream))
        DurableReceiverCodec.chargeStream))
    (fun s => (s.absentBytes, s.cells, s.available))
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun _ => rfl)

def readBytes (path : System.FilePath) : IO (List UInt8) := do
  return (← IO.FS.readBinFile path).toList

def writeBytes (path : System.FilePath) (bytes : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path (ByteArray.mk bytes.toArray)

def exportLog (config out : String) : IO UInt32 := do
  let settings ← Minidregg.Host.ClientConsentCore.loadSettings config
  let loaded ← IO.ofExcept (← DurableReceiverIO.load settings.config.transport
    ResourceBirthCodec.rootBytes)
  let seed := loaded.image.seed
  let g ← match genesisOfSeed seed with
    | .ok g => pure g
    | .error e => throw (IO.userError s!"genesis {reprStr e}")
  let mut w := g
  let mut entries : Array (List UInt8) := #[]
  let mut turns : Array (TurnOfIntent.DTurn deployedR Digest) := #[]
  let mut index := 0
  let mut fullBytes := 0
  let mut compactN := 0
  let mut compactB := 0
  let mut verbatimN := 0
  let mut verbatimB := 0
  let mut createB := 0
  let mut eventB := 0
  let mut fieldB : List Nat := List.replicate 12 0
  let mut absentB := 0
  let mut recWritesB := 0
  let mut recGuardsN := 0
  let mut recNullN := 0
  let mut recNullB := 0
  let mut recWritesN := 0
  for record in loaded.image.accepted do
    let some intent := record.bind? ResourceBirthCodec.rootBytes
      | throw (IO.userError s!"record {index} does not bind")
    match TurnOfIntent.Turn.ofIntent bridge DeployedHistory.history w intent with
    | .error r =>
      IO.println s!"NOTURN {index} {(reprStr r).replace "\n" " "}"
      return (1 : UInt32)
    | .ok t =>
      match World.admit DeployedHistory.history w t with
      | .error r =>
        IO.println s!"REFUSED {index} {reprStr r}"
        return (1 : UInt32)
      | .ok w' =>
        entries := entries.push (DeployedTurnCompact.encodeTurnAt w t)
        for leg in t.legs do
          let b := DeployedTurnCompact.encodeLegAt (DeployedTurnCompact.heldOf w t.creates) leg
          if b.head? == some 0 then
            compactN := compactN + 1; compactB := compactB + b.length
          else
            verbatimN := verbatimN + 1; verbatimB := verbatimB + b.length
        fieldB := (fieldB.zip (DeployedHistory.turnFields t)).map fun (n, f) => n + f.length
        absentB := absentB + (t.pins.filter fun p => decide (p.2 = DeployedHistory.history.cellDigest none)).length
        eventB := eventB + (DurableReceiverCodec.eventStream.encode t.event).length
        recWritesB := recWritesB + (record.writes.map fun x => x.canonicalPostBytes.length).sum
        recGuardsN := recGuardsN + record.readGuards.length
        recNullN := recNullN + record.nullifiers.length
        recNullB := recNullB + (record.nullifiers.map fun n => n.canonicalBytes.length).sum
        recWritesN := recWritesN + record.writes.length
        createB := createB + (t.creates.map DeployedTurnCodec.createBytes |>.map List.length).sum
        fullBytes := fullBytes + (DeployedHistory.encodeTurn t).length
        w := w'
        turns := turns.push t
    index := index + 1
  -- The World against the Store it was derived from.
  let ids := idsOf seed turns.toList
  let mut bad := 0
  for c in ids do
    if bytesOf w c != loaded.snapshot.canonicalBytes ⟨c⟩ then
      IO.println s!"CELL-MISMATCH {c}"
      bad := bad + 1
  for record in loaded.image.accepted do
    for n in record.nullifiers do
      if (w.spent (TurnOfIntent.digestKey n)).isNone then
        IO.println s!"SPENT-MISSING {n.canonicalBytes.length}"
        bad := bad + 1
  let height := (w.head.map Prod.fst).getD 0
  if height != loaded.image.accepted.length then
    IO.println s!"HEIGHT-MISMATCH {height} {loaded.image.accepted.length}"
    bad := bad + 1
  if bad != 0 then return 1
  IO.FS.createDirAll out
  writeBytes (System.FilePath.mk out / "genesis.bin") (seedStream.encode seed)
  let framed := frameEntries entries.toList
  writeBytes (System.FilePath.mk out / "turns.bin") framed
  let root := turnLogRoot w ids
  IO.FS.writeFile (System.FilePath.mk out / "root") s!"{root.value}\n"
  let recordBytes := loaded.image.accepted.foldl
    (fun acc r => acc + (DurableCheckpointCodec.recordFrame.encode r).length) 0
  IO.println s!"EXPORT turns {entries.size} cells {ids.length} turn-bytes {framed.length} record-bytes {recordBytes}"
  let (r, wr, a, i) := turns.foldl (fun (r, wr, a, i) t =>
    let (r', wr', a', i') := breakdown t; (r + r', wr + wr', a + a', i + i')) (0, 0, 0, 0)
  IO.println s!"BYTES whole-value-turns {fullBytes} (reads {r} writes {wr} alloc-free {a} images {i}); digest-guard log {framed.length}"
  IO.println s!"FIELDS {fieldB} absent-pins {absentB}"
  IO.println s!"LEGS compact {compactN} ({compactB} B) verbatim {verbatimN} ({verbatimB} B) creates {createB} B events {eventB} B; records: post-image bytes {recWritesB} read-guards {recGuardsN} writes {recWritesN} nullifiers {recNullN} ({recNullB} B)"
  IO.println s!"ROOT {root.value}"
  return 0

def follow (out : String) (drop : Option Nat := none) : IO UInt32 := do
  let some seed := DeployedTurnCodec.full seedStream (← readBytes (System.FilePath.mk out / "genesis.bin"))
    | IO.println "STOP genesis-undecodable"; return 1
  let some entries := unframeEntries (← readBytes (System.FilePath.mk out / "turns.bin"))
    | IO.println "STOP log-unframed"; return 1
  -- Plant: a follower handed a log with one entry missing.
  let entries := match drop with
    | some k => entries.eraseIdx k
    | none => entries
  match genesisOfSeed seed with
  | .error e => IO.println s!"STOP genesis {reprStr e}"; return (1 : UInt32)
  | .ok g =>
  match followFrom g 0 entries with
  | .error (.undecodable h) => IO.println s!"STOP undecodable {h}"; return 1
  | .error (.refused h r) => IO.println s!"STOP refused {h} {reprStr r}"; return 1
  | .ok (w, turns) =>
    let root := turnLogRoot w (idsOf seed turns)
    IO.println s!"FOLLOW turns {entries.length} height {(w.head.map Prod.fst).getD 0}"
    IO.println s!"ROOT {root.value}"
    return 0

end Minidregg.Host.TurnLogFollower

def main (arguments : List String) : IO UInt32 := do
  try
    match arguments with
    | ["export", config, out] => Minidregg.Host.TurnLogFollower.exportLog config out
    | ["follow", out] => Minidregg.Host.TurnLogFollower.follow out
    | ["follow", out, "--plant-drop", k] =>
      Minidregg.Host.TurnLogFollower.follow out k.toNat?
    | _ =>
      IO.eprintln "usage: turn-log-follower export CONFIG OUT | follow OUT"
      return (2 : UInt32)
  catch e =>
    IO.eprintln s!"turn-log-follower: {e}"
    return (1 : UInt32)
