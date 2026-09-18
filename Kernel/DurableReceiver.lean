/-
# Kernel.DurableReceiver — finite receiving image for the existing durable semantics

The persisted image is a finite genesis plus the ordered, exact intents that
were accepted. Reopening runs `DurableDataIntent.execute`; this module does not
reimplement its guards, metering, nullifiers, replay identity, or installation.
The genesis meter is resource allowance, not monetary ownership or a transfer.

This is an INTERNAL settlement boundary. A live caller supplies an already
controller-bound `DataIntent`. Decoding a journal does not authenticate a new
user request. The physical store must preserve the exact image bytes supplied
by that trusted controller; SQLite/OS durability remains an external floor.
-/
import Kernel.DurableDataIntent

namespace Minidregg.Kernel.DurableDataIntent.DataSnapshot

set_option autoImplicit false

/-- Unique physical write identities make the shared first-match lookup
return every member's exact post bytes. This does not assume root injectivity. -/
theorem lookupPostBytes_of_member (writes : List DataWrite)
    (unique : (writes.map DataWrite.cellId).Nodup) (write : DataWrite)
    (member : write ∈ writes) :
    lookupPostBytes write.cellId writes = some write.canonicalPostBytes := by
  induction writes with
  | nil => simp at member
  | cons head rest ih =>
      have uniqueParts : head.cellId ∉ rest.map DataWrite.cellId ∧
          (rest.map DataWrite.cellId).Nodup := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | inRest
      · simp [lookupPostBytes]
      · have different : head.cellId ≠ write.cellId := by
          intro same
          apply uniqueParts.1
          exact List.mem_map.mpr ⟨write, inRest, same.symm⟩
        rw [lookupPostBytes, if_neg different]
        exact ih uniqueParts.2 inRest

/-- The actual shared installer, rather than a second post-state function,
installs each uniquely identified member's exact canonical bytes. -/
theorem install_canonicalBytes_of_member
    {rootBytes : List UInt8 → Minidregg.Theory.TypedAuthorization.Digest}
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (unique : (intent.writes.map DataWrite.cellId).Nodup) (write : DataWrite)
    (member : write ∈ intent.writes) :
    (install before intent).canonicalBytes write.cellId = write.canonicalPostBytes := by
  change (lookupPostBytes write.cellId intent.writes).getD
    (before.canonicalBytes write.cellId) = write.canonicalPostBytes
  rw [lookupPostBytes_of_member intent.writes unique write member]
  rfl

end Minidregg.Kernel.DurableDataIntent.DataSnapshot

namespace Minidregg.Kernel.DurableReceiver

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

/-- First-order contents of a bound intent. The closed ten-lane charge has a
finite codec even though the semantic carrier is a function. -/
structure IntentRecord where
  transactionId : TransactionId
  writes : List DataWrite
  readGuards : List ReadGuard
  nullifiers : List StableNullifier
  exactCharge : Charge
  event : StableEvent

def IntentRecord.ofIntent {rootBytes : List UInt8 → Digest}
    (intent : DataIntent rootBytes) : IntentRecord :=
  ⟨intent.transactionId, intent.writes, intent.readGuards, intent.nullifiers,
    intent.exactCharge, intent.event⟩

def IntentRecord.bind? (rootBytes : List UInt8 → Digest) (record : IntentRecord) :
    Option (DataIntent rootBytes) :=
  if roots : record.writes.all
      (fun write => decide (rootBytes write.canonicalPostBytes = write.exactPost)) then
    if guards : record.readGuards.all
        (fun guard => decide (guard.cellId ∉ record.writes.map DataWrite.cellId)) then
      some
        { transactionId := record.transactionId
          writes := record.writes
          readGuards := record.readGuards
          nullifiers := record.nullifiers
          exactCharge := record.exactCharge
          event := record.event
          postRootsBound := by simpa using roots
          guardsReadOnly := by simpa using guards }
    else none
  else none

@[simp] theorem IntentRecord.bind_ofIntent {rootBytes : List UInt8 → Digest}
    (intent : DataIntent rootBytes) :
    (IntentRecord.ofIntent intent).bind? rootBytes = some intent := by
  have roots : intent.writes.all
      (fun write => decide (rootBytes write.canonicalPostBytes = write.exactPost)) = true :=
    by simpa using intent.postRootsBound
  have guards : intent.readGuards.all
      (fun guard => decide (guard.cellId ∉ intent.writes.map DataWrite.cellId)) = true :=
    by simpa using intent.guardsReadOnly
  unfold IntentRecord.bind? IntentRecord.ofIntent
  simp only [roots, guards, ↓reduceDIte]

theorem IntentRecord.bind_exact {rootBytes : List UInt8 → Digest}
    {record : IntentRecord} {intent : DataIntent rootBytes}
    (bound : record.bind? rootBytes = some intent) :
    IntentRecord.ofIntent intent = record := by
  unfold IntentRecord.bind? at bound
  split at bound
  next roots =>
    split at bound
    next guards =>
      cases Option.some.inj bound
      cases record
      rfl
    next => simp at bound
  next => simp at bound

/-- Explicit initial bytes, an explicit default for unallocated identifiers,
and initial metering allowance. A CellSlot deployment supplies its canonical
fresh encoding as `absentBytes`; no schema-specific empty root is invented. -/
structure Seed where
  absentBytes : List UInt8
  cells : List (CellId × List UInt8)
  available : Charge

def Seed.lookup (cells : List (CellId × List UInt8)) (cellId : CellId) :
    Option (List UInt8) :=
  match cells with
  | [] => none
  | (identifier, bytes) :: rest =>
      if identifier = cellId then some bytes else lookup rest cellId

def Seed.snapshot (rootBytes : List UInt8 → Digest) (seed : Seed) :
    DataSnapshot rootBytes where
  model :=
    { roots := fun cellId =>
        rootBytes ((lookup seed.cells cellId).getD seed.absentBytes)
      consumed := fun _ => false
      available := seed.available
      history := []
      journal := [] }
  canonicalBytes := fun cellId => (lookup seed.cells cellId).getD seed.absentBytes
  coherent := fun _ => rfl

/-- The whole image is finite. Its journal is chronological; the restored
protocol's own journal remains newest-first exactly as `execute` defines it. -/
structure Image where
  seed : Seed
  accepted : List IntentRecord

/-- Replay only genuinely new accepted commits. A recorded retry or rejection
inside the stored acceptance log is malformed and must not become a new event. -/
def replay (rootBytes : List UInt8 → Digest) (before : DataSnapshot rootBytes) :
    List IntentRecord → Option (DataSnapshot rootBytes)
  | [] => some before
  | record :: records => do
      let intent ← record.bind? rootBytes
      match DurableDataIntent.execute .complete before intent with
      | .accepted next => replay rootBytes next records
      | _ => none

def Image.restore (rootBytes : List UInt8 → Digest) (image : Image) :
    Option (DataSnapshot rootBytes) :=
  if (image.seed.cells.map Prod.fst).Nodup then
    replay rootBytes (image.seed.snapshot rootBytes) image.accepted
  else none

def Image.append {rootBytes : List UInt8 → Digest} (image : Image)
    (intent : DataIntent rootBytes) : Image :=
  { image with accepted := image.accepted ++ [IntentRecord.ofIntent intent] }

/-- Every identifier ever explicitly seeded or written remains enumerable,
including tombstones. Enumeration does not reinterpret or compact a cell. -/
def Image.cellIds (image : Image) : List CellId :=
  (image.seed.cells.map Prod.fst ++
    image.accepted.flatMap (fun record => record.writes.map DataWrite.cellId)).eraseDups

/-- Finite current bytes come from the existing replay result, not a second
map-update interpreter. The controller decodes these with its fixed cell codec. -/
def Image.currentCells (rootBytes : List UInt8 → Digest) (image : Image) :
    Option (List (CellId × List UInt8)) := do
  let snapshot ← image.restore rootBytes
  some (image.cellIds.map fun cellId => (cellId, snapshot.canonicalBytes cellId))

theorem Seed.lookup_missing (cells : List (CellId × List UInt8)) (cellId : CellId)
    (missing : cellId ∉ cells.map Prod.fst) : Seed.lookup cells cellId = none := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at missing
      simp [Seed.lookup, Ne.symm missing.1, ih missing.2]

theorem lookupPostBytes_missing (writes : List DataWrite) (cellId : CellId)
    (missing : cellId ∉ writes.map DataWrite.cellId) :
    DataSnapshot.lookupPostBytes cellId writes = none := by
  induction writes with
  | nil => rfl
  | cons write writes ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at missing
      simp [DataSnapshot.lookupPostBytes, Ne.symm missing.1, ih missing.2]

theorem replay_outside_support (rootBytes : List UInt8 → Digest)
    (before : DataSnapshot rootBytes) (records : List IntentRecord) (cellId : CellId)
    (missing : cellId ∉ records.flatMap (fun record => record.writes.map DataWrite.cellId))
    (after : DataSnapshot rootBytes) (restored : replay rootBytes before records = some after) :
    after.canonicalBytes cellId = before.canonicalBytes cellId := by
  induction records generalizing before after with
  | nil => cases Option.some.inj restored; rfl
  | cons record records ih =>
      simp only [List.flatMap_cons, List.mem_append, not_or] at missing
      unfold replay at restored
      cases bound : record.bind? rootBytes with
      | none => simp [bound] at restored
      | some intent =>
          simp only [bound, bind, Option.bind] at restored
          have writes : intent.writes = record.writes :=
            congrArg IntentRecord.writes (IntentRecord.bind_exact bound)
          cases executed : DurableDataIntent.execute .complete before intent with
          | accepted next =>
              simp only [executed] at restored
              have framed : next.canonicalBytes cellId = before.canonicalBytes cellId := by
                have atomic := execute_no_partial_data_commit .complete before intent
                simp only [executed, Outcome.storeAfter] at atomic
                rcases atomic with same | installed
                · rw [same]
                · rw [installed, DataSnapshot.install_canonicalBytes,
                    lookupPostBytes_missing intent.writes cellId (by simpa [writes] using missing.1)]
                  rfl
              exact (ih (before := next) missing.2 after restored).trans framed
          | replayed recorded => simp [executed] at restored
          | rejected reason => simp [executed] at restored
          | crashed point next => simp [executed] at restored

/-- An identifier outside the finite support is exactly the deployment's
explicit fresh image. Retired identifiers remain in support and cannot be
mistaken for this default. -/
theorem Image.outside_support (rootBytes : List UInt8 → Digest) (image : Image)
    (snapshot : DataSnapshot rootBytes) (restored : image.restore rootBytes = some snapshot)
    (cellId : CellId) (missing : cellId ∉ image.cellIds) :
    snapshot.canonicalBytes cellId = image.seed.absentBytes := by
  have absent : cellId ∉ image.seed.cells.map Prod.fst ∧
      cellId ∉ image.accepted.flatMap (fun record => record.writes.map DataWrite.cellId) := by
    simpa [Image.cellIds] using missing
  unfold Image.restore at restored
  split at restored
  next =>
    rw [replay_outside_support rootBytes (image.seed.snapshot rootBytes)
      image.accepted cellId absent.2 snapshot restored]
    simp [Seed.snapshot, Seed.lookup_missing image.seed.cells cellId absent.1]
  next => simp at restored

/-- Statement before proof: appending one accepted intent to a represented
image represents EXACTLY the existing executor's complete next snapshot. -/
def ExactAppend : Prop :=
  ∀ (rootBytes : List UInt8 → Digest) (image : Image)
    (before next : DataSnapshot rootBytes) (intent : DataIntent rootBytes),
    image.restore rootBytes = some before →
    DurableDataIntent.execute .complete before intent = .accepted next →
    (image.append intent).restore rootBytes = some next

theorem replay_append (rootBytes : List UInt8 → Digest)
    (before : DataSnapshot rootBytes) (left right : List IntentRecord) :
    replay rootBytes before (left ++ right) =
      (replay rootBytes before left).bind (fun middle => replay rootBytes middle right) := by
  induction left generalizing before with
  | nil => rfl
  | cons record records ih =>
      simp only [List.cons_append, replay]
      cases bound : record.bind? rootBytes with
      | none => simp
      | some intent =>
          cases executed : DurableDataIntent.execute .complete before intent <;>
            simp [executed, ih]

theorem exactAppend : ExactAppend := by
  intro rootBytes image before next intent restored accepted
  unfold Image.restore at restored ⊢
  simp only [Image.append]
  split at restored
  next valid =>
    simp only [valid, ↓reduceIte, replay_append, restored, Option.bind_some]
    simp [replay, accepted]
  next invalid => simp at restored

/-- A ready image carries the semantic fact used by the physical CAS driver.
No independent post image, root, or journal can be substituted. -/
structure Ready (rootBytes : List UInt8 → Digest) (image : Image)
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes) where
  next : DataSnapshot rootBytes
  executed : DurableDataIntent.execute .complete before intent = .accepted next
  restored : (image.append intent).restore rootBytes = some next

/-- The receiver calls the shared executor. It never retries a stale prepared
post image after a failed CAS: it reloads and calls this function again. -/
def prepare {rootBytes : List UInt8 → Digest} (image : Image)
    (before : DataSnapshot rootBytes) (represented : image.restore rootBytes = some before)
    (intent : DataIntent rootBytes) :
    Sum (Ready rootBytes image before intent) (Outcome rootBytes) :=
  match executed : DurableDataIntent.execute .complete before intent with
  | .accepted next => .inl ⟨next, executed, exactAppend rootBytes image before next intent represented executed⟩
  | outcome => .inr outcome

namespace Witness

open DurableDataIntent.Witness

def seed : Seed :=
  { absentBytes := [], cells := [(readCell, [1, 2, 3]), (writeCell, [4, 5])]
    available := fun _ => 10 }

def image : Image := ⟨seed, []⟩

theorem seed_represents : image.restore lengthRoot = some (seed.snapshot lengthRoot) := by
  simp [image, Image.restore, seed, replay, readCell, writeCell]

theorem inhabited_acceptance :
    DurableDataIntent.execute .complete (seed.snapshot lengthRoot) intent =
      .accepted (DataSnapshot.install (seed.snapshot lengthRoot) intent) := by
  apply execute_complete_ready
  · rfl
  · decide

theorem accepted_append_reopens :
    (image.append intent).restore lengthRoot =
      some (DataSnapshot.install (seed.snapshot lengthRoot) intent) :=
  exactAppend lengthRoot image _ _ intent seed_represents inhabited_acceptance

theorem acceptance_premises_inhabited :
    ∃ (stored : Image) (initial next : DataSnapshot lengthRoot)
      (acceptedIntent : DataIntent lengthRoot),
      stored.restore lengthRoot = some initial ∧
      DurableDataIntent.execute .complete initial acceptedIntent = .accepted next :=
  ⟨image, seed.snapshot lengthRoot, DataSnapshot.install (seed.snapshot lengthRoot) intent,
    intent, seed_represents, inhabited_acceptance⟩

theorem duplicate_journal_append_refused :
    (((image.append intent).append intent).restore lengthRoot).isNone = true := by decide

theorem stale_read_refuses :
    intent.preflight
      ({ seed with cells := [(readCell, [1]), (writeCell, [4, 5])] }.snapshot lengthRoot) =
        .error .staleReadGuard := by decide

end Witness

end Minidregg.Kernel.DurableReceiver

/-- info: 'Minidregg.Kernel.DurableReceiver.exactAppend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableReceiver.exactAppend
/-- info: 'Minidregg.Kernel.DurableReceiver.Image.outside_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableReceiver.Image.outside_support
/-- info: 'Minidregg.Kernel.DurableReceiver.Witness.accepted_append_reopens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableReceiver.Witness.accepted_append_reopens
