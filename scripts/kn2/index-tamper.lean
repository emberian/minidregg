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

Then a second Store (KN2-TRIE B1): 24 records writing two content cells with
links, signed by two subjects (a checkpoint at 16, so the open verifies the
suffix 17..24 against the index rows at 16). Controls first: the light open and
the audit accept it, and every presence (2), link (4) and backlink (5) key the
log names opens, verified, to exactly what the log declares
(`DurableIndex.declared`). Then:

* a tampered family-5 row value is refused at verify;
* a MISSING family-2, family-4 and family-5 leaf (every version) is each
  refused by the store audit naming the index node AND by the open (a suffix
  record overwrites that presence, reveals that cell's links, retargets that
  backlink), and the restored Store is accepted again;
* a record that drops and re-adds a link — two writes of one cell — never
  reaches the Store: the receiver refuses it (`duplicateCell`); the index rows
  of such a record are planted in `DurableIndexModel.FamiliesProbe`
  (`drop_and_readd_indexes_final`, control `drop_only_deletes`);
* a Store born with the two-family index (`index/trie-v1`) is refused at the
  open by name.

Usage: lake env lean --run scripts/kn2/index-tamper.lean STORE-HELPER
(the helper binary from native/hyperdocument-link-sqlite-store). -/
import Compiler.DurableStoreAudit
import Compiler.DurableServed
import Compiler.Sp800185Cshake256
import Compiler.DurableIndexModel

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

/-! ## Families 2, 4, 5 against a real Store -/

open DurableIndex.FamiliesProbe (cellA cellB linkA linkB documentA documentB subjectA subjectB linkTo contentImage)

def familiesSeed : Seed :=
  { absentBytes := [], cells := [(cellA, contentImage []), (cellB, contentImage [])], available := fun _ => 1000 }

/-- The links record `number` writes: cell A (odd records) holds linkA, whose
target alternates between documents A and B every two writes (its record — and
so its live-since height — changes at every write), and linkB, unchanged; cell B
(even records) holds linkA to document A, or nothing every fourth record. -/
def linksAt (number : Nat) : List (Minidregg.Theory.Hyperdocument.LinkId × Minidregg.Theory.Hyperdocument.LinkRecord) :=
  if number % 2 = 1 then
    [(linkA, linkTo (if (number / 2) % 2 = 0 then documentA else documentB) number), (linkB, linkTo documentB 301)]
  else if number % 4 = 0 then [] else [(linkA, linkTo documentA 302)]

def cellAt (number : Nat) : CellId := if number % 2 = 1 then cellA else cellB

def subjectAt (number : Nat) : Option SubjectId :=
  if number % 3 = 0 then none else some (if number % 2 = 0 then subjectA else subjectB)

def bytesBefore (number : Nat) : List UInt8 :=
  if number ≤ 2 then contentImage [] else contentImage (linksAt (number - 2))

def familyStep (number : Nat) : DataIntent rootBytes where
  transactionId := ⟨5000 + number⟩
  writes := [⟨cellAt number, rootBytes (bytesBefore number), rootBytes (contentImage (linksAt number)),
    contentImage (linksAt number)⟩]
  readGuards := []
  nullifiers := [nullifier (100 + number)]
  exactCharge := fun _ => 1
  event := ⟨1, ⟨800⟩, ⟨5000 + number⟩, [UInt8.ofNat number]⟩
  subject := subjectAt number
  postRootsBound := by simp
  guardsReadOnly := by simp

/-- One record writing cell A twice: linkA dropped, then the cell's current links
(linkA back, unchanged) — the drop-and-re-add the index's LAST-write rule covers. -/
def twoWrites : DataIntent rootBytes where
  transactionId := ⟨5025⟩
  writes := [⟨cellA, rootBytes (contentImage (linksAt 23)), rootBytes (contentImage [(linkB, linkTo documentB 301)]),
      contentImage [(linkB, linkTo documentB 301)]⟩,
    ⟨cellA, rootBytes (contentImage [(linkB, linkTo documentB 301)]), rootBytes (contentImage (linksAt 23)),
      contentImage (linksAt 23)⟩]
  readGuards := []
  nullifiers := [nullifier 125]
  exactCharge := fun _ => 1
  event := ⟨1, ⟨800⟩, ⟨5025⟩, [25]⟩
  subject := some subjectB
  postRootsBound := by simp
  guardsReadOnly := by simp

def familyRecords : List IntentRecord := (List.range' 1 24).map fun n => IntentRecord.ofIntent (familyStep n)

/-- Every presence, link and backlink key the log names. -/
def familyKeys : List DurableIndex.IndexKey :=
  [subjectA, subjectB].flatMap (fun s => [cellA, cellB].map fun c => DurableIndex.presenceKey s c) ++
  [cellA, cellB].flatMap (fun c => [linkA, linkB].map fun l => DurableIndex.linkKey c l) ++
  [documentA, documentB].flatMap fun d => [cellA, cellB].flatMap fun c => [linkA, linkB].map fun l =>
    DurableIndex.backlinkKey (DurableIndex.targetPrimary (.document d)) c l

/-- The SQL predicate of every version of `k`'s leaf row, wherever it sits. -/
def leafRowsOf (k : DurableIndex.IndexKey) : String :=
  s!"space = 3 AND substr(value, 1, 1) = X'00' AND substr(value, 2, 65) = X'{hex k.bytes}'"

def runFamilies (binary : System.FilePath) (directory : System.FilePath) : IO Unit := do
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 11 + 5))).toByteArray
  let config : NativeConfig :=
    { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 16 }
  let transport := { config.transport (fun _ => ⟨7⟩) ⟨999⟩ with systemCell := none }
  match ← bootstrap transport rootBytes familiesSeed with
  | .error message => throw (IO.userError message)
  | .ok () => pure ()
  for number in List.range' 1 24 do
    match ← receive transport rootBytes (familyStep number) 3 with
    | .confirmed _ _ => pure ()
    | .rejected reason => throw (IO.userError s!"FAIL family commit {number}: rejected {repr reason}")
    | .unavailable detail => throw (IO.userError s!"FAIL family commit {number}: unavailable {detail}")
    | .uncertain detail => throw (IO.userError s!"FAIL family commit {number}: uncertain {detail}")
    | .contention => throw (IO.userError s!"FAIL family commit {number}: contention")
  let database := directory / "store" / "forward-link.sqlite3"
  let opens : IO (Except String Unit) := do
    match ← DurableServed.openHead transport rootBytes with
    | .ok _ => return .ok ()
    | .error detail => return .error detail
  let audits : IO (Except String Unit) := do
    match ← DurableStoreAudit.audit transport rootBytes with
    | .ok _ => return .ok ()
    | .error detail => return .error detail
  -- Controls: the open and the audit accept the honest Store.
  match ← opens with
  | .ok () => require "control: the light open verifies the suffix 17..24 against the family rows" true
  | .error detail => throw (IO.userError s!"FAIL control open refused the honest families Store: {detail}")
  match ← audits with
  | .ok () => require "control: the audit re-derives every family row from the records" true
  | .error detail => throw (IO.userError s!"FAIL control audit refused the honest families Store: {detail}")
  let loaded ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"FAIL open: {detail}")
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf transport rootBytes loaded with
    | .ok reader => pure reader
    | .error detail => throw (IO.userError s!"FAIL reader: {detail}")
  let root := reader.head.indexRoot
  let rows ← match ← indexRows transport 24 familyKeys with
    | .ok rows => pure rows
    | .error message => throw (IO.userError s!"FAIL rows: {message}")
  -- Control: every family key opens, verified, to what the log declares.
  for k in familyKeys do
    match DurableIndex.lookupRows rows root k with
    | .ok answer =>
        unless answer.value == DurableIndex.declared familyRecords k do
          throw (IO.userError s!"FAIL family key (family {k.family}) answers other than the log declares")
    | .error message => throw (IO.userError s!"FAIL family key (family {k.family}) refused: {message}")
  require s!"control: all {familyKeys.length} presence/link/backlink keys open to the log's declared values" true
  let present := familyKeys.filter fun k => (DurableIndex.declared familyRecords k).isSome
  require s!"control: {present.length} of them present (families 2, 4 and 5 all represented)"
    ([2, 4, 5].all fun f : UInt8 => present.any (·.family == f))
  -- PLANT F1: a tampered family-5 value is refused at verify.
  let k5 := DurableIndex.backlinkKey (DurableIndex.targetPrimary (.document documentB)) cellA linkB
  let opening5 := DurableIndex.openingOf rows root k5
  let leafKey5 := DurableIndex.rowKey ((DurableIndex.bitsOf k5).take opening5.siblings.length)
  let some honest5 := DurableIndex.declared familyRecords k5
    | throw (IO.userError "FAIL the plant's backlink is not in the log")
  require "control: the backlink of linkB under document B verifies with its row"
    (DurableIndex.verify root k5 (some honest5) opening5)
  let forged := DurableIndex.rowStream.encode
    (.leaf k5 (DurableIndex.rowValue cellA linkB (linkTo documentB 301) 999))
  let newest := s!"space = 3 AND key = X'{hex leafKey5}' AND height = (SELECT max(height) FROM durable_node WHERE space = 3 AND key = X'{hex leafKey5}')"
  sql database s!"CREATE TABLE saved_f5 AS SELECT * FROM durable_node WHERE {newest}"
  sql database s!"UPDATE durable_node SET value = X'{hex forged}' WHERE {newest}"
  let tampered ← match ← indexRows transport 24 [k5] with
    | .ok rows => pure rows
    | .error message => throw (IO.userError s!"FAIL rows: {message}")
  match DurableIndex.lookupRows tampered root k5 with
  | .ok answer => throw (IO.userError s!"FAIL a tampered family-5 row verified ({answer.value.map (·.length)})")
  | .error message => require s!"a tampered family-5 row value is refused at verify ({message})" true
  sql database s!"DELETE FROM durable_node WHERE {newest}"
  sql database "INSERT INTO durable_node SELECT * FROM saved_f5"
  sql database "DROP TABLE saved_f5"
  -- PLANTS F2/F4/F5: a missing leaf of each family (every version), at a key a suffix record touches.
  let missing : List (String × DurableIndex.IndexKey) :=
    [("family-2 presence (subject B, cell A)", DurableIndex.presenceKey subjectB cellA),
     ("family-4 link (cell A, linkB)", DurableIndex.linkKey cellA linkB),
     ("family-5 backlink (document B, cell A, linkA)",
       DurableIndex.backlinkKey (DurableIndex.targetPrimary (.document documentB)) cellA linkA)]
  for (label, k) in missing do
    sql database s!"CREATE TABLE saved_leaf AS SELECT * FROM durable_node WHERE {leafRowsOf k}"
    sql database s!"DELETE FROM durable_node WHERE {leafRowsOf k}"
    match ← audits with
    | .ok () => throw (IO.userError s!"FAIL the audit accepted a Store missing the {label} leaf")
    | .error message =>
        require s!"the audit names the missing {label} leaf ({message})" ((message.splitOn "index node").length > 1)
    match ← opens with
    | .ok () => throw (IO.userError s!"FAIL the open accepted a Store missing the {label} leaf")
    | .error message => require s!"the open's index check refuses the missing {label} leaf ({message})" true
    sql database "INSERT INTO durable_node SELECT * FROM saved_leaf"
    sql database "DROP TABLE saved_leaf"
    match ← audits with
    | .ok () => require s!"control: restored, the {label} leaf audits again" true
    | .error message => throw (IO.userError s!"FAIL restored Store refused: {message}")
  -- PLANT F6: a record writing one cell twice (drop linkA, then re-add it) never reaches the Store.
  match ← receive transport rootBytes twoWrites 3 with
  | .rejected reason =>
      require s!"a record writing one cell twice is refused by the receiver ({repr reason})"
        (((toString (repr reason)).splitOn "duplicateCell").length > 1)
  | _ => throw (IO.userError "FAIL a record writing one cell twice was not refused")
  match ← opens with
  | .ok () => require "control: after the refusal the Store opens unchanged" true
  | .error detail => throw (IO.userError s!"FAIL open after the refused record: {detail}")
  -- PLANT F7: a Store born with the two-family index is refused at the open, by name.
  let olderFrame := DurableCheckpointCodec.seedFrameName ++ [2] ++ DurableCheckpointCodec.labelTrieV1.toUTF8.toList
  let olderSeed := (Tower256ConcreteBackend.StreamCodec.product Tower256ConcreteBackend.bytesStream
    DurableReceiverCodec.seedStream).encode (olderFrame, familiesSeed)
  sql database s!"UPDATE durable_seed SET bytes = X'{hex olderSeed}'"
  match ← opens with
  | .ok () => throw (IO.userError "FAIL a trie-v1 Store opened")
  | .error detail =>
      require s!"a trie-v1 Store is refused at the open by name ({detail})"
        ((detail.splitOn "history accumulator: Store history/mmr-v1;index/trie-v1;checkpoint/v4").length > 1)
  IO.println "PASS index families tamper: a tampered backlink value, a missing presence, link and backlink leaf (audit and open), a two-write record and a trie-v1 Store, each refused; every control passed"

end IndexTamper

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => do
      IO.FS.withTempDir (IndexTamper.run binary)
      IO.FS.withTempDir (IndexTamper.runFamilies binary)
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/index-tamper.lean STORE-HELPER")
