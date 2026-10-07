/- KN2 unified trie, executed plants against a real Store (cv 01a11742-712b).

A 41-record Store (one transaction id and one nullifier per record) is opened, and
the index — ONE trie, families 0 (spent) and 1 (transactions), one root bound by
the head tag's MAC — is attacked at its verifier, its reveal, its Store rows and
its audit. Every plant has a control that passes first:

* a forged MEMBERSHIP opening (an honest opening, another value) is refused;
* a forged NON-MEMBERSHIP opening (absence claimed for a present key, from the
  honest opening and from an empty terminal) is refused;
* a family-0 key presented as family 1 (same primary) is refused, and the
  family-1 lookup of that primary is a VERIFIED absence;
* a deleted leaf row is refused at the family's reveal — never answered as a
  shorter set — and the store audit names the missing node;
* a tampered row value is refused at the query (`Reader.byTx`).

Usage: lake env lean --run scripts/kn2/index-tamper.lean STORE-HELPER
(the helper binary from native/hyperdocument-link-sqlite-store). -/
import Compiler.DurableStoreAudit
import Compiler.DurableServed
import Compiler.Sp800185Cshake256

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler
open Minidregg.Compiler.DurableReceiverIO
open Minidregg.Compiler.DurableHistoryReader

namespace IndexTamper

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.DURABLE.RECEIVER.PROBE/v1".toUTF8.toList bytes).digest

def seed : Seed := { absentBytes := [], cells := [(⟨1⟩, [1]), (⟨3⟩, [0])], available := fun _ => 1000 }

def nullifier (number : Nat) : StableNullifier := ⟨1, ⟨700⟩, ⟨number⟩, [UInt8.ofNat number]⟩

/-- Record `number` moves cell 3 from `[number - 1]` to `[number]`. -/
def step (number : Nat) : DataIntent rootBytes where
  transactionId := ⟨1000 + number⟩
  writes := [⟨⟨3⟩, rootBytes [UInt8.ofNat (number - 1)], rootBytes [UInt8.ofNat number], [UInt8.ofNat number]⟩]
  readGuards := []
  nullifiers := [nullifier number]
  exactCharge := fun _ => 1
  event := ⟨1, ⟨800⟩, ⟨number⟩, [UInt8.ofNat number]⟩
  subject := none
  postRootsBound := by simp
  guardsReadOnly := by simp

def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL index tamper: {label}")
  IO.println s!"ok: {label}"

def sql (database : System.FilePath) (statement : String) : IO Unit := do
  let output ← IO.Process.output { cmd := "python3", args := #["-c",
    s!"import sqlite3,sys; c=sqlite3.connect(sys.argv[1]); c.execute(sys.argv[2]); c.commit()",
    database.toString, statement] }
  unless output.exitCode == 0 do throw (IO.userError s!"FAIL sql: {output.stderr}")

def hex (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let digits := String.ofList (Nat.toDigits 16 b.toNat)
    if digits.length = 1 then "0" ++ digits else digits)

def run (binary : System.FilePath) (directory : System.FilePath) : IO Unit := do
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
  let config : NativeConfig :=
    { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 16 }
  let transport := { config.transport (fun _ => ⟨7⟩) ⟨999⟩ with systemCell := none }
  match ← bootstrap transport rootBytes seed with
  | .error message => throw (IO.userError message)
  | .ok () => pure ()
  for number in List.range' 1 41 do
    match ← receive transport rootBytes (step number) 3 with
    | .confirmed _ _ => pure ()
    | .rejected reason => throw (IO.userError s!"FAIL commit {number}: rejected {repr reason}")
    | .unavailable detail => throw (IO.userError s!"FAIL commit {number}: unavailable {detail}")
    | .uncertain detail => throw (IO.userError s!"FAIL commit {number}: uncertain {detail}")
    | .contention => throw (IO.userError s!"FAIL commit {number}: contention")
  let loaded ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"FAIL open: {detail}")
  let database := directory / "store" / "forward-link.sqlite3"
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf transport rootBytes loaded with
    | .ok reader => pure reader
    | .error detail => throw (IO.userError s!"FAIL reader: {detail}")
  let root := reader.head.indexRoot
  let spentKeys := (List.range' 1 41).map (DurableIndex.nullifierKey ∘ nullifier)
  let txKeys := (List.range' 1 41).map fun n => DurableIndex.transactionKey ⟨1000 + n⟩
  let rows ← match ← indexRows transport 41 (spentKeys ++ txKeys) with
    | .ok rows => pure rows
    | .error message => throw (IO.userError s!"FAIL rows: {message}")
  let k5 := DurableIndex.nullifierKey (nullifier 5)
  let opening5 := DurableIndex.openingOf rows root k5
  let absentKey := DurableIndex.nullifierKey (nullifier 77)
  let absentOpening := DurableIndex.openingOf rows root absentKey
  -- Controls: the honest answers verify.
  require "control: nullifier 5's honest membership opening verifies (height 5)"
    (DurableIndex.verify root k5 (some (DurableIndex.heightValue 5)) opening5)
  require "control: nullifier 77's honest non-membership opening verifies"
    (DurableIndex.verify root absentKey none absentOpening)
  -- PLANT 1: a forged membership opening (the honest opening, another value).
  require "forged membership (nullifier 5 at height 6) is refused"
    (!DurableIndex.verify root k5 (some (DurableIndex.heightValue 6)) opening5)
  require "forged membership (nullifier 77 present, from its absence opening) is refused"
    (!DurableIndex.verify root absentKey (some (DurableIndex.heightValue 77)) absentOpening)
  -- PLANT 2: a forged non-membership opening.
  require "forged non-membership of a present key (honest opening, answer none) is refused"
    (!DurableIndex.verify root k5 none opening5)
  require "forged non-membership of a present key (empty terminal at the opening's depth) is refused"
    (!DurableIndex.verify root k5 none ⟨opening5.siblings, .empty⟩)
  require "forged non-membership of a present key (empty root opening) is refused"
    (!DurableIndex.verify root k5 none ⟨[], .empty⟩)
  -- PLANT 3: a family-0 key presented as family 1.
  let asTransaction : DurableIndex.IndexKey := { k5 with family := DurableIndex.Family.transaction }
  require "a family-0 opening presented for the family-1 key of the same primary is refused"
    (!DurableIndex.verify root asTransaction (some (DurableIndex.heightValue 5)) opening5)
  match DurableIndex.lookupRows rows root asTransaction with
  | .ok answer => require "the family-1 key of a family-0 primary is a VERIFIED absence" (answer.value.isNone)
  | .error message => throw (IO.userError s!"FAIL family-1 lookup refused: {message}")
  -- Reveals: family 0's prefix is its first 8 bits.
  let family0 := (DurableIndex.bitsOf k5).take 8
  match DurableIndex.revealRows rows root family0 with
  | .ok revealed =>
      require "control: family 0's reveal verifies with its 41 members"
        (revealed.members.length == 41 && revealed.members.all (·.1.family == DurableIndex.Family.spent))
  | .error message => throw (IO.userError s!"FAIL honest reveal refused: {message}")
  match ← DurableStoreAudit.audit transport rootBytes with
  | .ok report => IO.println s!"control: {report.line}"
  | .error message => throw (IO.userError s!"FAIL control audit refused the honest Store: {message}")
  -- PLANT 4: delete every version of nullifier 37's leaf row.
  let opening37 := DurableIndex.openingOf rows root (DurableIndex.nullifierKey (nullifier 37))
  let leafKey37 := DurableIndex.rowKey ((DurableIndex.bitsOf (DurableIndex.nullifierKey (nullifier 37))).take
    opening37.siblings.length)
  sql database s!"DELETE FROM durable_node WHERE space = 3 AND key = X'{hex leafKey37}'"
  let cut ← match ← indexRows transport 41 (spentKeys ++ txKeys) with
    | .ok rows => pure rows
    | .error message => throw (IO.userError s!"FAIL rows: {message}")
  match DurableIndex.revealRows cut root family0 with
  | .ok revealed => throw (IO.userError
      s!"FAIL a reveal without nullifier 37's leaf verified ({revealed.members.length} members)")
  | .error message => require s!"a deleted leaf is refused at the reveal, not answered as 40 members ({message})" true
  match ← DurableStoreAudit.audit transport rootBytes with
  | .ok _ => throw (IO.userError "FAIL store audit accepted a Store missing an index row")
  | .error message =>
      require s!"store audit names the missing index node ({message})" ((message.splitOn "index node").length > 1)
  -- PLANT 5: the newest version of transaction 1036's leaf row says height 99.
  match ← reader.byTx ⟨1036⟩ with
  | .ok (.present found) => require "control: byTx 1036 is height 36" (found.height == 36)
  | _ => throw (IO.userError "FAIL control byTx 1036")
  let k36 := DurableIndex.transactionKey ⟨1036⟩
  let opening36 := DurableIndex.openingOf rows root k36
  let leafKey36 := DurableIndex.rowKey ((DurableIndex.bitsOf k36).take opening36.siblings.length)
  let forged := DurableIndex.rowStream.encode (.leaf k36 (DurableIndex.heightValue 99))
  sql database s!"UPDATE durable_node SET value = X'{hex forged}' WHERE space = 3 AND key = X'{hex leafKey36}' AND height = (SELECT max(height) FROM durable_node WHERE space = 3 AND key = X'{hex leafKey36}')"
  match ← reader.byTx ⟨1036⟩ with
  | .ok (.present found) => throw (IO.userError s!"FAIL byTx through a tampered row answered height {found.height}")
  | .ok (.absent _) => throw (IO.userError "FAIL byTx through a tampered row answered absent")
  | .error refusal => require s!"a tampered row value is refused at the query ({refusal.message})" true
  IO.println "PASS index tamper: forged membership and non-membership, a cross-family key, a deleted leaf and a tampered value, each refused; the audit names the missing row"

end IndexTamper

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir (IndexTamper.run binary)
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/index-tamper.lean STORE-HELPER")
